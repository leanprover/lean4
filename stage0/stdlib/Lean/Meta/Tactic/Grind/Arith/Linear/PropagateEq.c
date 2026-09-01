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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v___x_303_; lean_object* v_mctx_304_; lean_object* v_lctx_305_; lean_object* v_options_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v___x_303_ = lean_st_ref_get(v___y_297_);
v_mctx_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_mctx_304_);
lean_dec(v___x_303_);
v_lctx_305_ = lean_ctor_get(v___y_296_, 2);
v_options_306_ = lean_ctor_get(v___y_298_, 1);
lean_inc_ref(v_options_306_);
lean_inc_ref(v_lctx_305_);
v___x_307_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_307_, 0, v_env_302_);
lean_ctor_set(v___x_307_, 1, v_mctx_304_);
lean_ctor_set(v___x_307_, 2, v_lctx_305_);
lean_ctor_set(v___x_307_, 3, v_options_306_);
v___x_308_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_msgData_295_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5___boxed(lean_object* v_msgData_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msgData_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_317_; double v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_float_of_nat(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(lean_object* v_cls_322_, lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_375_; 
v_ref_329_ = lean_ctor_get(v___y_326_, 4);
v___x_330_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_375_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_375_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_375_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_traceState_336_; lean_object* v_env_337_; lean_object* v_nextMacroScope_338_; lean_object* v_ngen_339_; lean_object* v_auxDeclNGen_340_; lean_object* v_cache_341_; lean_object* v_messages_342_; lean_object* v_infoState_343_; lean_object* v_snapshotTasks_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_374_; 
v___x_335_ = lean_st_ref_take(v___y_327_);
v_traceState_336_ = lean_ctor_get(v___x_335_, 4);
v_env_337_ = lean_ctor_get(v___x_335_, 0);
v_nextMacroScope_338_ = lean_ctor_get(v___x_335_, 1);
v_ngen_339_ = lean_ctor_get(v___x_335_, 2);
v_auxDeclNGen_340_ = lean_ctor_get(v___x_335_, 3);
v_cache_341_ = lean_ctor_get(v___x_335_, 5);
v_messages_342_ = lean_ctor_get(v___x_335_, 6);
v_infoState_343_ = lean_ctor_get(v___x_335_, 7);
v_snapshotTasks_344_ = lean_ctor_get(v___x_335_, 8);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_374_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_374_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snapshotTasks_344_);
lean_inc(v_infoState_343_);
lean_inc(v_messages_342_);
lean_inc(v_cache_341_);
lean_inc(v_traceState_336_);
lean_inc(v_auxDeclNGen_340_);
lean_inc(v_ngen_339_);
lean_inc(v_nextMacroScope_338_);
lean_inc(v_env_337_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_374_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint64_t v_tid_348_; lean_object* v_traces_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_373_; 
v_tid_348_ = lean_ctor_get_uint64(v_traceState_336_, sizeof(void*)*1);
v_traces_349_ = lean_ctor_get(v_traceState_336_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_traceState_336_);
if (v_isSharedCheck_373_ == 0)
{
v___x_351_ = v_traceState_336_;
v_isShared_352_ = v_isSharedCheck_373_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_traces_349_);
lean_dec(v_traceState_336_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_373_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; double v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_355_ = 0;
v___x_356_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_357_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_357_, 0, v_cls_322_);
lean_ctor_set(v___x_357_, 1, v___x_353_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_ctor_set_float(v___x_357_, sizeof(void*)*3, v___x_354_);
lean_ctor_set_float(v___x_357_, sizeof(void*)*3 + 8, v___x_354_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*3 + 16, v___x_355_);
v___x_358_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_359_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v_a_331_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_inc(v_ref_329_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_ref_329_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_PersistentArray_push___redArg(v_traces_349_, v___x_360_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_361_);
v___x_363_ = v___x_351_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_361_);
lean_ctor_set_uint64(v_reuseFailAlloc_372_, sizeof(void*)*1, v_tid_348_);
v___x_363_ = v_reuseFailAlloc_372_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 4, v___x_363_);
v___x_365_ = v___x_346_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_env_337_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_nextMacroScope_338_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_ngen_339_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_auxDeclNGen_340_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v_cache_341_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_messages_342_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_infoState_343_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_snapshotTasks_344_);
v___x_365_ = v_reuseFailAlloc_371_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_st_ref_put(v___y_327_, v___x_365_);
v___x_367_ = lean_box(0);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_367_);
v___x_369_ = v___x_333_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object* v_cls_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_376_, v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_398_ = l_Lean_Name_append(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_539_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_539_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_539_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_539_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
if (lean_obj_tag(v_a_416_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_534_; 
v_val_420_ = lean_ctor_get(v_a_416_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_534_ == 0)
{
v___x_422_ = v_a_416_;
v_isShared_423_ = v_isSharedCheck_534_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v_a_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_534_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_snd_424_; lean_object* v_snd_425_; lean_object* v_options_426_; lean_object* v_fst_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_532_; 
v_snd_424_ = lean_ctor_get(v_val_420_, 1);
lean_inc(v_snd_424_);
v_snd_425_ = lean_ctor_get(v_snd_424_, 1);
lean_inc(v_snd_425_);
v_options_426_ = lean_ctor_get(v_a_412_, 1);
v_fst_427_ = lean_ctor_get(v_val_420_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_val_420_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_val_420_, 1);
lean_dec(v_unused_533_);
v___x_429_ = v_val_420_;
v_isShared_430_ = v_isSharedCheck_532_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_fst_427_);
lean_dec(v_val_420_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_532_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_530_; 
v_fst_431_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_snd_424_, 1);
lean_dec(v_unused_531_);
v___x_433_ = v_snd_424_;
v_isShared_434_ = v_isSharedCheck_530_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_fst_431_);
lean_dec(v_snd_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_530_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_p_435_; lean_object* v_toCold_436_; uint8_t v_hasTrace_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_p_435_ = lean_ctor_get(v_snd_425_, 0);
v_toCold_436_ = lean_ctor_get(v_a_412_, 0);
v_hasTrace_437_ = lean_ctor_get_uint8(v_options_426_, sizeof(void*)*1);
v___x_438_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_435_, v_fst_431_);
lean_inc(v_p_402_);
v___x_439_ = l_Lean_Grind_Linarith_Poly_mul(v_p_402_, v___x_438_);
v___x_440_ = lean_int_neg(v_fst_427_);
lean_inc(v_p_435_);
v___x_441_ = l_Lean_Grind_Linarith_Poly_mul(v_p_435_, v___x_440_);
lean_dec(v___x_440_);
v___x_442_ = l_Lean_Grind_Linarith_Poly_combine(v___x_439_, v___x_441_);
if (v_hasTrace_437_ == 0)
{
lean_dec(v___x_438_);
lean_dec(v_fst_427_);
lean_dec(v_p_402_);
goto v___jp_443_;
}
else
{
lean_object* v_inheritedTraceOptions_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_inheritedTraceOptions_456_ = lean_ctor_get(v_toCold_436_, 4);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_456_, v_options_426_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v___x_438_);
lean_dec(v_fst_427_);
lean_dec(v_p_402_);
goto v___jp_443_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_p_402_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_431_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_425_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_442_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
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
v___x_471_ = l_Int_repr(v_fst_427_);
lean_dec(v_fst_427_);
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
v___x_482_ = l_Int_repr(v___x_438_);
lean_dec(v___x_438_);
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
v___x_489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_457_, v___x_488_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
goto v___jp_443_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___x_442_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
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
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
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
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
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
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
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
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
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
v___jp_443_:
{
lean_object* v___x_445_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_442_);
lean_ctor_set(v___x_433_, 0, v_snd_425_);
v___x_445_ = v___x_433_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_snd_425_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_442_);
v___x_445_ = v_reuseFailAlloc_455_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_445_);
lean_ctor_set(v___x_429_, 0, v_fst_431_);
v___x_447_ = v___x_429_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_454_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_447_);
v___x_449_ = v___x_422_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_449_);
v___x_451_ = v___x_418_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
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
lean_dec(v_a_416_);
lean_dec(v_p_402_);
v___x_535_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_535_);
v___x_537_ = v___x_418_;
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
lean_dec(v_p_402_);
v_a_540_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_415_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_415_);
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
v_options_723_ = lean_ctor_get(v_a_666_, 1);
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
lean_object* v_toCold_725_; lean_object* v_inheritedTraceOptions_726_; lean_object* v_cls_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_toCold_725_ = lean_ctor_get(v_a_666_, 0);
v_inheritedTraceOptions_726_ = lean_ctor_get(v_toCold_725_, 4);
v_cls_727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_726_, v_options_723_, v___x_728_);
if (v___x_729_ == 0)
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
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_653_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_654_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
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
v___x_744_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_727_, v___x_743_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
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
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
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
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
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
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
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
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
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
lean_dec_ref_known(v_a_807_, 1);
v___x_812_ = lean_nat_dec_eq(v_val_805_, v_val_811_);
lean_dec(v_val_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec_ref_known(v_a_801_, 1);
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
lean_dec_ref_known(v_a_801_, 1);
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
lean_dec_ref_known(v_a_801_, 1);
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
lean_dec_ref_known(v_a_885_, 1);
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
lean_dec_ref_known(v_a_893_, 1);
v___x_898_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_866_, v_a_869_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_867_, v_a_869_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___y_903_; uint8_t v___x_1002_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
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
lean_dec_ref_known(v___x_908_, 1);
v_p_910_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v___y_903_);
lean_inc_ref(v_p_910_);
v___x_911_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_910_, v___y_903_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
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
lean_dec_ref_known(v_a_914_, 1);
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
lean_dec_ref_known(v___x_933_, 1);
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
lean_dec_ref_known(v_a_936_, 1);
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
lean_dec_ref_known(v___x_932_, 2);
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
lean_dec_ref_known(v___x_932_, 2);
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
lean_dec_ref_known(v___x_932_, 2);
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
lean_dec_ref_known(v___x_1074_, 1);
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
lean_dec_ref_known(v_a_1078_, 1);
v___x_1083_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1061_, v_a_1063_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
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
lean_dec_ref_known(v_a_1086_, 1);
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
lean_dec_ref_known(v___x_1097_, 1);
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
lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_2795__overap_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1179_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1179_, 0, v___x_1178_);
v___x_2795__overap_1180_ = lean_panic_fn_borrowed(v___f_1179_, v_msg_1165_);
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
v___x_1181_ = lean_apply_12(v___x_2795__overap_1180_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, lean_box(0));
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
lean_dec_ref_known(v___x_1228_, 1);
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
lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v_p_1381_; lean_object* v_toCold_1382_; lean_object* v_options_1383_; lean_object* v_currRecDepth_1384_; lean_object* v_maxRecDepth_1385_; lean_object* v_ref_1386_; lean_object* v_currNamespace_1387_; lean_object* v_openDecls_1388_; lean_object* v_initHeartbeats_1389_; lean_object* v_maxHeartbeats_1390_; lean_object* v_currMacroScope_1391_; uint8_t v_diag_1392_; uint8_t v_suppressElabErrors_1393_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_p_1381_ = lean_ctor_get(v_c_1350_, 0);
v_toCold_1382_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_toCold_1382_);
v_options_1383_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_ref(v_options_1383_);
v_currRecDepth_1384_ = lean_ctor_get(v_a_1360_, 2);
lean_inc(v_currRecDepth_1384_);
v_maxRecDepth_1385_ = lean_ctor_get(v_a_1360_, 3);
lean_inc(v_maxRecDepth_1385_);
v_ref_1386_ = lean_ctor_get(v_a_1360_, 4);
lean_inc(v_ref_1386_);
v_currNamespace_1387_ = lean_ctor_get(v_a_1360_, 5);
lean_inc(v_currNamespace_1387_);
v_openDecls_1388_ = lean_ctor_get(v_a_1360_, 6);
lean_inc(v_openDecls_1388_);
v_initHeartbeats_1389_ = lean_ctor_get(v_a_1360_, 7);
lean_inc(v_initHeartbeats_1389_);
v_maxHeartbeats_1390_ = lean_ctor_get(v_a_1360_, 8);
lean_inc(v_maxHeartbeats_1390_);
v_currMacroScope_1391_ = lean_ctor_get(v_a_1360_, 9);
lean_inc(v_currMacroScope_1391_);
v_diag_1392_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*10);
v_suppressElabErrors_1393_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_1360_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_nat_dec_eq(v_maxRecDepth_1385_, v___x_1488_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_eq(v_currRecDepth_1384_, v_maxRecDepth_1385_);
if (v___x_1490_ == 0)
{
goto v___jp_1394_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_currMacroScope_1391_);
lean_dec(v_maxHeartbeats_1390_);
lean_dec(v_initHeartbeats_1389_);
lean_dec(v_openDecls_1388_);
lean_dec(v_currNamespace_1387_);
lean_dec(v_maxRecDepth_1385_);
lean_dec(v_currRecDepth_1384_);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_toCold_1382_);
lean_dec_ref(v_c_1350_);
v___x_1491_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1386_);
return v___x_1491_;
}
}
else
{
goto v___jp_1394_;
}
v___jp_1363_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1365_);
lean_ctor_set(v___x_1378_, 1, v___y_1366_);
lean_ctor_set(v___x_1378_, 2, v_c_1350_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1364_);
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
v___jp_1394_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_currRecDepth_1384_, v___x_1395_);
lean_dec(v_currRecDepth_1384_);
lean_inc_ref(v_options_1383_);
lean_inc_ref(v_toCold_1382_);
v___x_1397_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1397_, 0, v_toCold_1382_);
lean_ctor_set(v___x_1397_, 1, v_options_1383_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
lean_ctor_set(v___x_1397_, 3, v_maxRecDepth_1385_);
lean_ctor_set(v___x_1397_, 4, v_ref_1386_);
lean_ctor_set(v___x_1397_, 5, v_currNamespace_1387_);
lean_ctor_set(v___x_1397_, 6, v_openDecls_1388_);
lean_ctor_set(v___x_1397_, 7, v_initHeartbeats_1389_);
lean_ctor_set(v___x_1397_, 8, v_maxHeartbeats_1390_);
lean_ctor_set(v___x_1397_, 9, v_currMacroScope_1391_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*10, v_diag_1392_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*10 + 1, v_suppressElabErrors_1393_);
lean_inc(v_p_1381_);
v___x_1398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1381_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1397_, v_a_1361_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1479_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1479_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1479_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
if (lean_obj_tag(v_a_1399_) == 1)
{
lean_object* v_val_1403_; lean_object* v_snd_1404_; uint8_t v_hasTrace_1405_; 
lean_del_object(v___x_1401_);
v_val_1403_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v_a_1399_, 1);
v_snd_1404_ = lean_ctor_get(v_val_1403_, 1);
lean_inc(v_snd_1404_);
v_hasTrace_1405_ = lean_ctor_get_uint8(v_options_1383_, sizeof(void*)*1);
if (v_hasTrace_1405_ == 0)
{
lean_object* v_fst_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; 
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_toCold_1382_);
v_fst_1406_ = lean_ctor_get(v_val_1403_, 0);
lean_inc(v_fst_1406_);
lean_dec(v_val_1403_);
v_fst_1407_ = lean_ctor_get(v_snd_1404_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v_snd_1404_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_snd_1404_);
v___y_1364_ = v_snd_1408_;
v___y_1365_ = v_fst_1406_;
v___y_1366_ = v_fst_1407_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1397_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_fst_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1474_; 
v_fst_1409_ = lean_ctor_get(v_val_1403_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_val_1403_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_val_1403_, 1);
lean_dec(v_unused_1475_);
v___x_1411_ = v_val_1403_;
v_isShared_1412_ = v_isSharedCheck_1474_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_fst_1409_);
lean_dec(v_val_1403_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1474_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1473_; 
v_fst_1413_ = lean_ctor_get(v_snd_1404_, 0);
v_snd_1414_ = lean_ctor_get(v_snd_1404_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_snd_1404_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1416_ = v_snd_1404_;
v_isShared_1417_ = v_isSharedCheck_1473_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snd_1414_);
lean_inc(v_fst_1413_);
lean_dec(v_snd_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1473_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_inheritedTraceOptions_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_inheritedTraceOptions_1418_ = lean_ctor_get(v_toCold_1382_, 4);
lean_inc_ref(v_inheritedTraceOptions_1418_);
lean_dec_ref(v_toCold_1382_);
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1418_, v_options_1383_, v___x_1420_);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_inheritedTraceOptions_1418_);
if (v___x_1421_ == 0)
{
lean_del_object(v___x_1416_);
lean_del_object(v___x_1411_);
v___y_1364_ = v_snd_1414_;
v___y_1365_ = v_fst_1409_;
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
v___y_1376_ = v___x_1397_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1409_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1397_, v_a_1361_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1397_, v_a_1361_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1413_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1397_, v_a_1361_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_MessageData_ofExpr(v_a_1423_);
v___x_1429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1429_);
lean_ctor_set(v___x_1416_, 0, v___x_1428_);
v___x_1431_ = v___x_1416_;
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
if (v_isShared_1412_ == 0)
{
lean_ctor_set_tag(v___x_1411_, 7);
lean_ctor_set(v___x_1411_, 1, v___x_1432_);
lean_ctor_set(v___x_1411_, 0, v___x_1431_);
v___x_1434_ = v___x_1411_;
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
v___x_1438_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1419_, v___x_1437_, v_a_1358_, v_a_1359_, v___x_1397_, v_a_1361_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
v___y_1364_ = v_snd_1414_;
v___y_1365_ = v_fst_1409_;
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
v___y_1376_ = v___x_1397_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_c_1350_);
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
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_c_1350_);
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
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_c_1350_);
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
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_c_1350_);
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
lean_dec(v_a_1399_);
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_toCold_1382_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v_c_1350_);
v___x_1477_ = v___x_1401_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_c_1350_);
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
lean_dec_ref_known(v___x_1397_, 10);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_toCold_1382_);
lean_dec_ref(v_c_1350_);
v_a_1480_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1398_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1398_);
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
v_ref_1512_ = lean_ctor_get(v___y_1509_, 4);
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
lean_object* v_options_1751_; lean_object* v_p_1752_; lean_object* v_p_1753_; uint8_t v_strict_1754_; lean_object* v_toCold_1755_; uint8_t v_hasTrace_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_p_1761_; 
v_options_1751_ = lean_ctor_get(v_a_1748_, 1);
v_p_1752_ = lean_ctor_get(v_c_u2081_1736_, 0);
v_p_1753_ = lean_ctor_get(v_c_u2082_1738_, 0);
v_strict_1754_ = lean_ctor_get_uint8(v_c_u2082_1738_, sizeof(void*)*2);
v_toCold_1755_ = lean_ctor_get(v_a_1748_, 0);
v_hasTrace_1756_ = lean_ctor_get_uint8(v_options_1751_, sizeof(void*)*1);
v___x_1757_ = lean_nat_to_int(v_a_1734_);
lean_inc(v_p_1753_);
v___x_1758_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1753_, v___x_1757_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_int_neg(v_b_1737_);
lean_inc(v_p_1752_);
v___x_1760_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1752_, v___x_1759_);
lean_dec(v___x_1759_);
v_p_1761_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1758_, v___x_1760_);
if (v_hasTrace_1756_ == 0)
{
goto v___jp_1762_;
}
else
{
lean_object* v_inheritedTraceOptions_1766_; lean_object* v_cls_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_inheritedTraceOptions_1766_ = lean_ctor_get(v_toCold_1755_, 4);
v_cls_1767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1769_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1766_, v_options_1751_, v___x_1768_);
if (v___x_1769_ == 0)
{
goto v___jp_1762_;
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
goto v___jp_1762_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_p_1761_);
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
lean_dec(v_p_1761_);
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
lean_dec(v_p_1761_);
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
lean_dec(v_p_1761_);
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
v___jp_1762_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1763_, 0, v_x_1735_);
lean_ctor_set(v___x_1763_, 1, v_c_u2081_1736_);
lean_ctor_set(v___x_1763_, 2, v_c_u2082_1738_);
v___x_1764_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1764_, 0, v_p_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*2, v_strict_1754_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
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
lean_object* v_a_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v_b_1879_);
v_a_1894_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
v_fst_1895_ = lean_ctor_get(v_a_1894_, 0);
v_snd_1896_ = lean_ctor_get(v_a_1894_, 1);
lean_inc(v_snd_1896_);
lean_inc_ref(v_c_u2081_1875_);
lean_inc(v_x_1874_);
lean_inc(v_a_1873_);
v___x_1897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1873_, v_x_1874_, v_c_u2081_1875_, v_fst_1895_, v_snd_1896_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1898_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref_known(v___x_1899_, 1);
v___x_1900_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1914_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1914_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1914_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_unbox(v_a_1901_);
lean_dec(v_a_1901_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; 
lean_del_object(v___x_1903_);
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1878_, v___x_1907_);
v_i_1878_ = v___x_1908_;
v_b_1879_ = v___x_1906_;
goto _start;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1910_);
v___x_1912_ = v___x_1903_;
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
v_a_1915_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1900_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1900_);
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
v_a_1923_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1899_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1899_);
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
v_a_1931_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1897_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1897_);
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
lean_inc(v_fst_2226_);
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
lean_inc(v_fst_2236_);
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
lean_inc(v_fst_2294_);
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
v___x_2426_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2427_, lean_object* v_x_2428_, lean_object* v_c_2429_, lean_object* v_y_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2478_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2478_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2478_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_unbox(v_a_2444_);
lean_dec(v_a_2444_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
lean_del_object(v___x_2446_);
v___x_2449_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___y_2452_; lean_object* v_lowers_2460_; lean_object* v_size_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_lowers_2460_ = lean_ctor_get(v_a_2450_, 32);
lean_inc_ref(v_lowers_2460_);
lean_dec(v_a_2450_);
v_size_2461_ = lean_ctor_get(v_lowers_2460_, 2);
v___x_2462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2463_ = lean_nat_dec_lt(v_y_2430_, v_size_2461_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_dec_ref(v_lowers_2460_);
v___x_2464_ = l_outOfBounds___redArg(v___x_2462_);
v___y_2452_ = v___x_2464_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2462_, v_lowers_2460_, v_y_2430_);
lean_dec_ref(v_lowers_2460_);
v___y_2452_ = v___x_2465_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2453_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2428_, v___y_2452_);
lean_dec_ref(v___y_2452_);
v_fst_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_fst_2454_);
v_snd_2455_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2455_);
lean_dec_ref(v___x_2453_);
lean_inc(v_a_2431_);
v___f_2456_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2456_, 0, v_a_2431_);
lean_closure_set(v___f_2456_, 1, v_y_2430_);
lean_closure_set(v___f_2456_, 2, v_fst_2454_);
v___x_2457_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2458_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2457_, v___f_2456_, v_a_2432_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2459_; 
lean_dec_ref_known(v___x_2458_, 1);
v___x_2459_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2427_, v_x_2428_, v_c_2429_, v_snd_2455_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_snd_2455_);
return v___x_2459_;
}
else
{
lean_dec(v_snd_2455_);
lean_dec_ref(v_c_2429_);
lean_dec(v_x_2428_);
lean_dec(v_a_2427_);
return v___x_2458_;
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
v_a_2466_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2449_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2449_);
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
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2474_);
v___x_2476_ = v___x_2446_;
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
v_a_2479_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2443_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2443_);
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
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2644_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2644_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2644_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_unbox(v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
lean_del_object(v___x_2612_);
v___x_2615_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___y_2618_; lean_object* v_uppers_2626_; lean_object* v_size_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v_uppers_2626_ = lean_ctor_get(v_a_2616_, 33);
lean_inc_ref(v_uppers_2626_);
lean_dec(v_a_2616_);
v_size_2627_ = lean_ctor_get(v_uppers_2626_, 2);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2629_ = lean_nat_dec_lt(v_y_2596_, v_size_2627_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v_uppers_2626_);
v___x_2630_ = l_outOfBounds___redArg(v___x_2628_);
v___y_2618_ = v___x_2630_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2628_, v_uppers_2626_, v_y_2596_);
lean_dec_ref(v_uppers_2626_);
v___y_2618_ = v___x_2631_;
goto v___jp_2617_;
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v_fst_2620_; lean_object* v_snd_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2594_, v___y_2618_);
lean_dec_ref(v___y_2618_);
v_fst_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_fst_2620_);
v_snd_2621_ = lean_ctor_get(v___x_2619_, 1);
lean_inc(v_snd_2621_);
lean_dec_ref(v___x_2619_);
lean_inc(v_a_2597_);
v___f_2622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2622_, 0, v_a_2597_);
lean_closure_set(v___f_2622_, 1, v_y_2596_);
lean_closure_set(v___f_2622_, 2, v_fst_2620_);
v___x_2623_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2624_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2623_, v___f_2622_, v_a_2598_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v___x_2625_; 
lean_dec_ref_known(v___x_2624_, 1);
v___x_2625_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2593_, v_x_2594_, v_c_2595_, v_snd_2621_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_snd_2621_);
return v___x_2625_;
}
else
{
lean_dec(v_snd_2621_);
lean_dec_ref(v_c_2595_);
lean_dec(v_x_2594_);
lean_dec(v_a_2593_);
return v___x_2624_;
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
v_a_2632_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2615_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2615_);
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
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2640_);
v___x_2642_ = v___x_2612_;
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
v_a_2645_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2609_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2609_);
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
lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v_options_2805_; uint8_t v_hasTrace_2806_; 
v_options_2805_ = lean_ctor_get(v_a_2777_, 1);
v_hasTrace_2806_ = lean_ctor_get_uint8(v_options_2805_, sizeof(void*)*1);
if (v_hasTrace_2806_ == 0)
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
lean_object* v_toCold_2807_; lean_object* v_inheritedTraceOptions_2808_; lean_object* v_cls_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_toCold_2807_ = lean_ctor_get(v_a_2777_, 0);
v_inheritedTraceOptions_2808_ = lean_ctor_get(v_toCold_2807_, 4);
v_cls_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2808_, v_options_2805_, v___x_2810_);
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
lean_object* v_p_2851_; lean_object* v_toCold_2852_; lean_object* v_options_2853_; lean_object* v_currRecDepth_2854_; lean_object* v_maxRecDepth_2855_; lean_object* v_ref_2856_; lean_object* v_currNamespace_2857_; lean_object* v_openDecls_2858_; lean_object* v_initHeartbeats_2859_; lean_object* v_maxHeartbeats_2860_; lean_object* v_currMacroScope_2861_; uint8_t v_diag_2862_; uint8_t v_suppressElabErrors_2863_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_p_2851_ = lean_ctor_get(v_c_u2082_2838_, 0);
v_toCold_2852_ = lean_ctor_get(v_a_2848_, 0);
lean_inc_ref(v_toCold_2852_);
v_options_2853_ = lean_ctor_get(v_a_2848_, 1);
lean_inc_ref(v_options_2853_);
v_currRecDepth_2854_ = lean_ctor_get(v_a_2848_, 2);
lean_inc(v_currRecDepth_2854_);
v_maxRecDepth_2855_ = lean_ctor_get(v_a_2848_, 3);
lean_inc(v_maxRecDepth_2855_);
v_ref_2856_ = lean_ctor_get(v_a_2848_, 4);
lean_inc(v_ref_2856_);
v_currNamespace_2857_ = lean_ctor_get(v_a_2848_, 5);
lean_inc(v_currNamespace_2857_);
v_openDecls_2858_ = lean_ctor_get(v_a_2848_, 6);
lean_inc(v_openDecls_2858_);
v_initHeartbeats_2859_ = lean_ctor_get(v_a_2848_, 7);
lean_inc(v_initHeartbeats_2859_);
v_maxHeartbeats_2860_ = lean_ctor_get(v_a_2848_, 8);
lean_inc(v_maxHeartbeats_2860_);
v_currMacroScope_2861_ = lean_ctor_get(v_a_2848_, 9);
lean_inc(v_currMacroScope_2861_);
v_diag_2862_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*10);
v_suppressElabErrors_2863_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_2848_);
v___x_2915_ = lean_unsigned_to_nat(0u);
v___x_2916_ = lean_nat_dec_eq(v_maxRecDepth_2855_, v___x_2915_);
if (v___x_2916_ == 0)
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_nat_dec_eq(v_currRecDepth_2854_, v_maxRecDepth_2855_);
if (v___x_2917_ == 0)
{
goto v___jp_2864_;
}
else
{
lean_object* v___x_2918_; 
lean_dec(v_currMacroScope_2861_);
lean_dec(v_maxHeartbeats_2860_);
lean_dec(v_initHeartbeats_2859_);
lean_dec(v_openDecls_2858_);
lean_dec(v_currNamespace_2857_);
lean_dec(v_maxRecDepth_2855_);
lean_dec(v_currRecDepth_2854_);
lean_dec_ref(v_options_2853_);
lean_dec_ref(v_toCold_2852_);
lean_dec_ref(v_c_u2082_2838_);
v___x_2918_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2856_);
return v___x_2918_;
}
}
else
{
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_unsigned_to_nat(1u);
v___x_2866_ = lean_nat_add(v_currRecDepth_2854_, v___x_2865_);
lean_dec(v_currRecDepth_2854_);
v___x_2867_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2867_, 0, v_toCold_2852_);
lean_ctor_set(v___x_2867_, 1, v_options_2853_);
lean_ctor_set(v___x_2867_, 2, v___x_2866_);
lean_ctor_set(v___x_2867_, 3, v_maxRecDepth_2855_);
lean_ctor_set(v___x_2867_, 4, v_ref_2856_);
lean_ctor_set(v___x_2867_, 5, v_currNamespace_2857_);
lean_ctor_set(v___x_2867_, 6, v_openDecls_2858_);
lean_ctor_set(v___x_2867_, 7, v_initHeartbeats_2859_);
lean_ctor_set(v___x_2867_, 8, v_maxHeartbeats_2860_);
lean_ctor_set(v___x_2867_, 9, v_currMacroScope_2861_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*10, v_diag_2862_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*10 + 1, v_suppressElabErrors_2863_);
v___x_2868_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2851_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2867_, v_a_2849_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2906_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2906_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2906_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_val_2873_; lean_object* v_snd_2874_; lean_object* v_snd_2875_; lean_object* v_fst_2876_; lean_object* v_fst_2877_; lean_object* v_p_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2871_);
v_val_2873_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_val_2873_);
lean_dec_ref_known(v_a_2869_, 1);
v_snd_2874_ = lean_ctor_get(v_val_2873_, 1);
lean_inc(v_snd_2874_);
v_snd_2875_ = lean_ctor_get(v_snd_2874_, 1);
lean_inc(v_snd_2875_);
v_fst_2876_ = lean_ctor_get(v_val_2873_, 0);
lean_inc(v_fst_2876_);
lean_dec(v_val_2873_);
v_fst_2877_ = lean_ctor_get(v_snd_2874_, 0);
lean_inc(v_fst_2877_);
lean_dec(v_snd_2874_);
v_p_2878_ = lean_ctor_get(v_snd_2875_, 0);
v___x_2879_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2878_, v_fst_2877_);
lean_inc_ref(v_c_u2082_2838_);
v___x_2880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2879_, v_fst_2877_, v_snd_2875_, v_fst_2876_, v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2867_, v_a_2849_);
lean_dec(v_fst_2877_);
lean_dec(v___x_2879_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
if (lean_obj_tag(v_a_2881_) == 1)
{
lean_object* v_val_2882_; 
lean_dec_ref(v_c_u2082_2838_);
v_val_2882_ = lean_ctor_get(v_a_2881_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v_a_2881_, 1);
v_c_u2082_2838_ = v_val_2882_;
v_a_2848_ = v___x_2867_;
goto _start;
}
else
{
lean_object* v___x_2884_; 
lean_dec(v_a_2881_);
v___x_2884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2867_, v_a_2849_);
lean_dec_ref_known(v___x_2867_, 10);
lean_dec_ref(v_c_u2082_2838_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2893_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_box(0);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2884_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2884_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2867_, 10);
lean_dec_ref(v_c_u2082_2838_);
return v___x_2880_;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_dec(v_a_2869_);
lean_dec_ref_known(v___x_2867_, 10);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_c_u2082_2838_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2902_);
v___x_2904_ = v___x_2871_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
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
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref_known(v___x_2867_, 10);
lean_dec_ref(v_c_u2082_2838_);
v_a_2907_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2868_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2868_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec(v_a_2920_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2933_, lean_object* v_x_2934_, size_t v_x_2935_, size_t v_x_2936_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v_cs_2937_; size_t v_j_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v_cs_2937_ = lean_ctor_get(v_x_2934_, 0);
v_j_2938_ = lean_usize_shift_right(v_x_2935_, v_x_2936_);
v___x_2939_ = lean_usize_to_nat(v_j_2938_);
v___x_2940_ = lean_array_get_size(v_cs_2937_);
v___x_2941_ = lean_nat_dec_lt(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec(v___x_2939_);
lean_dec_ref(v_val_2933_);
return v_x_2934_;
}
else
{
lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2959_; 
lean_inc_ref(v_cs_2937_);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_x_2934_, 0);
lean_dec(v_unused_2960_);
v___x_2943_ = v_x_2934_;
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
else
{
lean_dec(v_x_2934_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
size_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v_i_2948_; size_t v___x_2949_; size_t v_shift_2950_; lean_object* v_v_2951_; lean_object* v___x_2952_; lean_object* v_xs_x27_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_shift_left(v___x_2945_, v_x_2936_);
v___x_2947_ = lean_usize_sub(v___x_2946_, v___x_2945_);
v_i_2948_ = lean_usize_land(v_x_2935_, v___x_2947_);
v___x_2949_ = ((size_t)5ULL);
v_shift_2950_ = lean_usize_sub(v_x_2936_, v___x_2949_);
v_v_2951_ = lean_array_fget(v_cs_2937_, v___x_2939_);
v___x_2952_ = lean_box(0);
v_xs_x27_2953_ = lean_array_fset(v_cs_2937_, v___x_2939_, v___x_2952_);
v___x_2954_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2933_, v_v_2951_, v_i_2948_, v_shift_2950_);
v___x_2955_ = lean_array_fset(v_xs_x27_2953_, v___x_2939_, v___x_2954_);
lean_dec(v___x_2939_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2955_);
v___x_2957_ = v___x_2943_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_vs_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_vs_2961_ = lean_ctor_get(v_x_2934_, 0);
v___x_2962_ = lean_usize_to_nat(v_x_2935_);
v___x_2963_ = lean_array_get_size(v_vs_2961_);
v___x_2964_ = lean_nat_dec_lt(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_dec(v___x_2962_);
lean_dec_ref(v_val_2933_);
return v_x_2934_;
}
else
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2976_; 
lean_inc_ref(v_vs_2961_);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_x_2934_, 0);
lean_dec(v_unused_2977_);
v___x_2966_ = v_x_2934_;
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_x_2934_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_v_2968_; lean_object* v___x_2969_; lean_object* v_xs_x27_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v_v_2968_ = lean_array_fget(v_vs_2961_, v___x_2962_);
v___x_2969_ = lean_box(0);
v_xs_x27_2970_ = lean_array_fset(v_vs_2961_, v___x_2962_, v___x_2969_);
v___x_2971_ = l_Lean_PersistentArray_push___redArg(v_v_2968_, v_val_2933_);
v___x_2972_ = lean_array_fset(v_xs_x27_2970_, v___x_2962_, v___x_2971_);
lean_dec(v___x_2962_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2972_);
v___x_2974_ = v___x_2966_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_){
_start:
{
size_t v_x_41066__boxed_2982_; size_t v_x_41067__boxed_2983_; lean_object* v_res_2984_; 
v_x_41066__boxed_2982_ = lean_unbox_usize(v_x_2980_);
lean_dec(v_x_2980_);
v_x_41067__boxed_2983_ = lean_unbox_usize(v_x_2981_);
lean_dec(v_x_2981_);
v_res_2984_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2978_, v_x_2979_, v_x_41066__boxed_2982_, v_x_41067__boxed_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2985_, lean_object* v_t_2986_, lean_object* v_i_2987_){
_start:
{
lean_object* v_root_2988_; lean_object* v_tail_2989_; lean_object* v_size_2990_; size_t v_shift_2991_; lean_object* v_tailOff_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3016_; 
v_root_2988_ = lean_ctor_get(v_t_2986_, 0);
v_tail_2989_ = lean_ctor_get(v_t_2986_, 1);
v_size_2990_ = lean_ctor_get(v_t_2986_, 2);
v_shift_2991_ = lean_ctor_get_usize(v_t_2986_, 4);
v_tailOff_2992_ = lean_ctor_get(v_t_2986_, 3);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_t_2986_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2994_ = v_t_2986_;
v_isShared_2995_ = v_isSharedCheck_3016_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_tailOff_2992_);
lean_inc(v_size_2990_);
lean_inc(v_tail_2989_);
lean_inc(v_root_2988_);
lean_dec(v_t_2986_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3016_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_nat_dec_le(v_tailOff_2992_, v_i_2987_);
if (v___x_2996_ == 0)
{
size_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2997_ = lean_usize_of_nat(v_i_2987_);
v___x_2998_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2985_, v_root_2988_, v___x_2997_, v_shift_2991_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2998_);
v___x_3000_ = v___x_2994_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_tail_2989_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_size_2990_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_tailOff_2992_);
lean_ctor_set_usize(v_reuseFailAlloc_3001_, 4, v_shift_2991_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_nat_sub(v_i_2987_, v_tailOff_2992_);
v___x_3003_ = lean_array_get_size(v_tail_2989_);
v___x_3004_ = lean_nat_dec_lt(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3006_; 
lean_dec(v___x_3002_);
lean_dec_ref(v_val_2985_);
if (v_isShared_2995_ == 0)
{
v___x_3006_ = v___x_2994_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_root_2988_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_tail_2989_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_size_2990_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v_tailOff_2992_);
lean_ctor_set_usize(v_reuseFailAlloc_3007_, 4, v_shift_2991_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
else
{
lean_object* v_v_3008_; lean_object* v___x_3009_; lean_object* v_xs_x27_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v_v_3008_ = lean_array_fget(v_tail_2989_, v___x_3002_);
v___x_3009_ = lean_box(0);
v_xs_x27_3010_ = lean_array_fset(v_tail_2989_, v___x_3002_, v___x_3009_);
v___x_3011_ = l_Lean_PersistentArray_push___redArg(v_v_3008_, v_val_2985_);
v___x_3012_ = lean_array_fset(v_xs_x27_3010_, v___x_3002_, v___x_3011_);
lean_dec(v___x_3002_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v___x_3012_);
v___x_3014_ = v___x_2994_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_root_2988_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3015_, 2, v_size_2990_);
lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_tailOff_2992_);
lean_ctor_set_usize(v_reuseFailAlloc_3015_, 4, v_shift_2991_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3017_, lean_object* v_t_3018_, lean_object* v_i_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3017_, v_t_3018_, v_i_3019_);
lean_dec(v_i_3019_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3021_, lean_object* v_val_3022_, lean_object* v_v_3023_, lean_object* v_s_3024_){
_start:
{
lean_object* v_structs_3025_; lean_object* v_typeIdOf_3026_; lean_object* v_exprToStructId_3027_; lean_object* v_exprToStructIdEntries_3028_; lean_object* v_forbiddenNatModules_3029_; lean_object* v_natStructs_3030_; lean_object* v_natTypeIdOf_3031_; lean_object* v_exprToNatStructId_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_structs_3025_ = lean_ctor_get(v_s_3024_, 0);
v_typeIdOf_3026_ = lean_ctor_get(v_s_3024_, 1);
v_exprToStructId_3027_ = lean_ctor_get(v_s_3024_, 2);
v_exprToStructIdEntries_3028_ = lean_ctor_get(v_s_3024_, 3);
v_forbiddenNatModules_3029_ = lean_ctor_get(v_s_3024_, 4);
v_natStructs_3030_ = lean_ctor_get(v_s_3024_, 5);
v_natTypeIdOf_3031_ = lean_ctor_get(v_s_3024_, 6);
v_exprToNatStructId_3032_ = lean_ctor_get(v_s_3024_, 7);
v___x_3033_ = lean_array_get_size(v_structs_3025_);
v___x_3034_ = lean_nat_dec_lt(v___y_3021_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_dec_ref(v_val_3022_);
return v_s_3024_;
}
else
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3096_; 
lean_inc_ref(v_exprToNatStructId_3032_);
lean_inc_ref(v_natTypeIdOf_3031_);
lean_inc_ref(v_natStructs_3030_);
lean_inc_ref(v_forbiddenNatModules_3029_);
lean_inc_ref(v_exprToStructIdEntries_3028_);
lean_inc_ref(v_exprToStructId_3027_);
lean_inc_ref(v_typeIdOf_3026_);
lean_inc_ref(v_structs_3025_);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_s_3024_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; 
v_unused_3097_ = lean_ctor_get(v_s_3024_, 7);
lean_dec(v_unused_3097_);
v_unused_3098_ = lean_ctor_get(v_s_3024_, 6);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_s_3024_, 5);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_s_3024_, 4);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_s_3024_, 3);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_s_3024_, 2);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_s_3024_, 1);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_s_3024_, 0);
lean_dec(v_unused_3104_);
v___x_3036_ = v_s_3024_;
v_isShared_3037_ = v_isSharedCheck_3096_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v_s_3024_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3096_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_v_3038_; lean_object* v_id_3039_; lean_object* v_ringId_x3f_3040_; lean_object* v_type_3041_; lean_object* v_u_3042_; lean_object* v_intModuleInst_3043_; lean_object* v_leInst_x3f_3044_; lean_object* v_ltInst_x3f_3045_; lean_object* v_lawfulOrderLTInst_x3f_3046_; lean_object* v_isPreorderInst_x3f_3047_; lean_object* v_orderedAddInst_x3f_3048_; lean_object* v_isLinearInst_x3f_3049_; lean_object* v_noNatDivInst_x3f_3050_; lean_object* v_ringInst_x3f_3051_; lean_object* v_commRingInst_x3f_3052_; lean_object* v_orderedRingInst_x3f_3053_; lean_object* v_fieldInst_x3f_3054_; lean_object* v_charInst_x3f_3055_; lean_object* v_zero_3056_; lean_object* v_ofNatZero_3057_; lean_object* v_one_x3f_3058_; lean_object* v_leFn_x3f_3059_; lean_object* v_ltFn_x3f_3060_; lean_object* v_addFn_3061_; lean_object* v_zsmulFn_3062_; lean_object* v_nsmulFn_3063_; lean_object* v_zsmulFn_x3f_3064_; lean_object* v_nsmulFn_x3f_3065_; lean_object* v_homomulFn_x3f_3066_; lean_object* v_subFn_3067_; lean_object* v_negFn_3068_; lean_object* v_vars_3069_; lean_object* v_varMap_3070_; lean_object* v_lowers_3071_; lean_object* v_uppers_3072_; lean_object* v_diseqs_3073_; lean_object* v_assignment_3074_; uint8_t v_caseSplits_3075_; lean_object* v_conflict_x3f_3076_; lean_object* v_diseqSplits_3077_; lean_object* v_elimEqs_3078_; lean_object* v_elimStack_3079_; lean_object* v_occurs_3080_; lean_object* v_ignored_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3095_; 
v_v_3038_ = lean_array_fget(v_structs_3025_, v___y_3021_);
v_id_3039_ = lean_ctor_get(v_v_3038_, 0);
v_ringId_x3f_3040_ = lean_ctor_get(v_v_3038_, 1);
v_type_3041_ = lean_ctor_get(v_v_3038_, 2);
v_u_3042_ = lean_ctor_get(v_v_3038_, 3);
v_intModuleInst_3043_ = lean_ctor_get(v_v_3038_, 4);
v_leInst_x3f_3044_ = lean_ctor_get(v_v_3038_, 5);
v_ltInst_x3f_3045_ = lean_ctor_get(v_v_3038_, 6);
v_lawfulOrderLTInst_x3f_3046_ = lean_ctor_get(v_v_3038_, 7);
v_isPreorderInst_x3f_3047_ = lean_ctor_get(v_v_3038_, 8);
v_orderedAddInst_x3f_3048_ = lean_ctor_get(v_v_3038_, 9);
v_isLinearInst_x3f_3049_ = lean_ctor_get(v_v_3038_, 10);
v_noNatDivInst_x3f_3050_ = lean_ctor_get(v_v_3038_, 11);
v_ringInst_x3f_3051_ = lean_ctor_get(v_v_3038_, 12);
v_commRingInst_x3f_3052_ = lean_ctor_get(v_v_3038_, 13);
v_orderedRingInst_x3f_3053_ = lean_ctor_get(v_v_3038_, 14);
v_fieldInst_x3f_3054_ = lean_ctor_get(v_v_3038_, 15);
v_charInst_x3f_3055_ = lean_ctor_get(v_v_3038_, 16);
v_zero_3056_ = lean_ctor_get(v_v_3038_, 17);
v_ofNatZero_3057_ = lean_ctor_get(v_v_3038_, 18);
v_one_x3f_3058_ = lean_ctor_get(v_v_3038_, 19);
v_leFn_x3f_3059_ = lean_ctor_get(v_v_3038_, 20);
v_ltFn_x3f_3060_ = lean_ctor_get(v_v_3038_, 21);
v_addFn_3061_ = lean_ctor_get(v_v_3038_, 22);
v_zsmulFn_3062_ = lean_ctor_get(v_v_3038_, 23);
v_nsmulFn_3063_ = lean_ctor_get(v_v_3038_, 24);
v_zsmulFn_x3f_3064_ = lean_ctor_get(v_v_3038_, 25);
v_nsmulFn_x3f_3065_ = lean_ctor_get(v_v_3038_, 26);
v_homomulFn_x3f_3066_ = lean_ctor_get(v_v_3038_, 27);
v_subFn_3067_ = lean_ctor_get(v_v_3038_, 28);
v_negFn_3068_ = lean_ctor_get(v_v_3038_, 29);
v_vars_3069_ = lean_ctor_get(v_v_3038_, 30);
v_varMap_3070_ = lean_ctor_get(v_v_3038_, 31);
v_lowers_3071_ = lean_ctor_get(v_v_3038_, 32);
v_uppers_3072_ = lean_ctor_get(v_v_3038_, 33);
v_diseqs_3073_ = lean_ctor_get(v_v_3038_, 34);
v_assignment_3074_ = lean_ctor_get(v_v_3038_, 35);
v_caseSplits_3075_ = lean_ctor_get_uint8(v_v_3038_, sizeof(void*)*42);
v_conflict_x3f_3076_ = lean_ctor_get(v_v_3038_, 36);
v_diseqSplits_3077_ = lean_ctor_get(v_v_3038_, 37);
v_elimEqs_3078_ = lean_ctor_get(v_v_3038_, 38);
v_elimStack_3079_ = lean_ctor_get(v_v_3038_, 39);
v_occurs_3080_ = lean_ctor_get(v_v_3038_, 40);
v_ignored_3081_ = lean_ctor_get(v_v_3038_, 41);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_v_3038_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3083_ = v_v_3038_;
v_isShared_3084_ = v_isSharedCheck_3095_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_ignored_3081_);
lean_inc(v_occurs_3080_);
lean_inc(v_elimStack_3079_);
lean_inc(v_elimEqs_3078_);
lean_inc(v_diseqSplits_3077_);
lean_inc(v_conflict_x3f_3076_);
lean_inc(v_assignment_3074_);
lean_inc(v_diseqs_3073_);
lean_inc(v_uppers_3072_);
lean_inc(v_lowers_3071_);
lean_inc(v_varMap_3070_);
lean_inc(v_vars_3069_);
lean_inc(v_negFn_3068_);
lean_inc(v_subFn_3067_);
lean_inc(v_homomulFn_x3f_3066_);
lean_inc(v_nsmulFn_x3f_3065_);
lean_inc(v_zsmulFn_x3f_3064_);
lean_inc(v_nsmulFn_3063_);
lean_inc(v_zsmulFn_3062_);
lean_inc(v_addFn_3061_);
lean_inc(v_ltFn_x3f_3060_);
lean_inc(v_leFn_x3f_3059_);
lean_inc(v_one_x3f_3058_);
lean_inc(v_ofNatZero_3057_);
lean_inc(v_zero_3056_);
lean_inc(v_charInst_x3f_3055_);
lean_inc(v_fieldInst_x3f_3054_);
lean_inc(v_orderedRingInst_x3f_3053_);
lean_inc(v_commRingInst_x3f_3052_);
lean_inc(v_ringInst_x3f_3051_);
lean_inc(v_noNatDivInst_x3f_3050_);
lean_inc(v_isLinearInst_x3f_3049_);
lean_inc(v_orderedAddInst_x3f_3048_);
lean_inc(v_isPreorderInst_x3f_3047_);
lean_inc(v_lawfulOrderLTInst_x3f_3046_);
lean_inc(v_ltInst_x3f_3045_);
lean_inc(v_leInst_x3f_3044_);
lean_inc(v_intModuleInst_3043_);
lean_inc(v_u_3042_);
lean_inc(v_type_3041_);
lean_inc(v_ringId_x3f_3040_);
lean_inc(v_id_3039_);
lean_dec(v_v_3038_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3095_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v_xs_x27_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3085_ = lean_box(0);
v_xs_x27_3086_ = lean_array_fset(v_structs_3025_, v___y_3021_, v___x_3085_);
v___x_3087_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3022_, v_diseqs_3073_, v_v_3023_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 34, v___x_3087_);
v___x_3089_ = v___x_3083_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_id_3039_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_ringId_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_type_3041_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_u_3042_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_intModuleInst_3043_);
lean_ctor_set(v_reuseFailAlloc_3094_, 5, v_leInst_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3094_, 6, v_ltInst_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3094_, 7, v_lawfulOrderLTInst_x3f_3046_);
lean_ctor_set(v_reuseFailAlloc_3094_, 8, v_isPreorderInst_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3094_, 9, v_orderedAddInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3094_, 10, v_isLinearInst_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3094_, 11, v_noNatDivInst_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3094_, 12, v_ringInst_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3094_, 13, v_commRingInst_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3094_, 14, v_orderedRingInst_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3094_, 15, v_fieldInst_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3094_, 16, v_charInst_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3094_, 17, v_zero_3056_);
lean_ctor_set(v_reuseFailAlloc_3094_, 18, v_ofNatZero_3057_);
lean_ctor_set(v_reuseFailAlloc_3094_, 19, v_one_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3094_, 20, v_leFn_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3094_, 21, v_ltFn_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3094_, 22, v_addFn_3061_);
lean_ctor_set(v_reuseFailAlloc_3094_, 23, v_zsmulFn_3062_);
lean_ctor_set(v_reuseFailAlloc_3094_, 24, v_nsmulFn_3063_);
lean_ctor_set(v_reuseFailAlloc_3094_, 25, v_zsmulFn_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3094_, 26, v_nsmulFn_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3094_, 27, v_homomulFn_x3f_3066_);
lean_ctor_set(v_reuseFailAlloc_3094_, 28, v_subFn_3067_);
lean_ctor_set(v_reuseFailAlloc_3094_, 29, v_negFn_3068_);
lean_ctor_set(v_reuseFailAlloc_3094_, 30, v_vars_3069_);
lean_ctor_set(v_reuseFailAlloc_3094_, 31, v_varMap_3070_);
lean_ctor_set(v_reuseFailAlloc_3094_, 32, v_lowers_3071_);
lean_ctor_set(v_reuseFailAlloc_3094_, 33, v_uppers_3072_);
lean_ctor_set(v_reuseFailAlloc_3094_, 34, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3094_, 35, v_assignment_3074_);
lean_ctor_set(v_reuseFailAlloc_3094_, 36, v_conflict_x3f_3076_);
lean_ctor_set(v_reuseFailAlloc_3094_, 37, v_diseqSplits_3077_);
lean_ctor_set(v_reuseFailAlloc_3094_, 38, v_elimEqs_3078_);
lean_ctor_set(v_reuseFailAlloc_3094_, 39, v_elimStack_3079_);
lean_ctor_set(v_reuseFailAlloc_3094_, 40, v_occurs_3080_);
lean_ctor_set(v_reuseFailAlloc_3094_, 41, v_ignored_3081_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*42, v_caseSplits_3075_);
v___x_3089_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3090_ = lean_array_fset(v_xs_x27_3086_, v___y_3021_, v___x_3089_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3090_);
v___x_3092_ = v___x_3036_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_typeIdOf_3026_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_exprToStructId_3027_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_exprToStructIdEntries_3028_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_forbiddenNatModules_3029_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_natStructs_3030_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_natTypeIdOf_3031_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_exprToNatStructId_3032_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3105_, lean_object* v_val_3106_, lean_object* v_v_3107_, lean_object* v_s_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3105_, v_val_3106_, v_v_3107_, v_s_3108_);
lean_dec(v_v_3107_);
lean_dec(v___y_3105_);
return v_res_3109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3117_ = l_Lean_Name_append(v___x_3116_, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3126_ = l_Lean_Name_append(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_cls_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3133_ = l_Lean_Name_append(v___x_3132_, v_cls_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_options_3205_; lean_object* v_toCold_3206_; uint8_t v_hasTrace_3207_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; 
v_options_3205_ = lean_ctor_get(v_a_3144_, 1);
v_toCold_3206_ = lean_ctor_get(v_a_3144_, 0);
v_hasTrace_3207_ = lean_ctor_get_uint8(v_options_3205_, sizeof(void*)*1);
if (v_hasTrace_3207_ == 0)
{
v___y_3209_ = v_a_3135_;
v___y_3210_ = v_a_3136_;
v___y_3211_ = v_a_3137_;
v___y_3212_ = v_a_3138_;
v___y_3213_ = v_a_3139_;
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
goto v___jp_3208_;
}
else
{
lean_object* v_inheritedTraceOptions_3280_; lean_object* v_cls_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_inheritedTraceOptions_3280_ = lean_ctor_get(v_toCold_3206_, 4);
v_cls_3281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3280_, v_options_3205_, v___x_3282_);
if (v___x_3283_ == 0)
{
v___y_3209_ = v_a_3135_;
v___y_3210_ = v_a_3136_;
v___y_3211_ = v_a_3137_;
v___y_3212_ = v_a_3138_;
v___y_3213_ = v_a_3139_;
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_MessageData_ofExpr(v_a_3285_);
v___x_3287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3281_, v___x_3286_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref_known(v___x_3287_, 1);
v___y_3209_ = v_a_3135_;
v___y_3210_ = v_a_3136_;
v___y_3211_ = v_a_3137_;
v___y_3212_ = v_a_3138_;
v___y_3213_ = v_a_3139_;
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
goto v___jp_3208_;
}
else
{
lean_dec_ref(v_c_3134_);
return v___x_3287_;
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_c_3134_);
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
v___jp_3147_:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3150_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v___f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec_ref_known(v___x_3164_, 1);
lean_inc(v___y_3153_);
v___f_3165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3165_, 0, v___y_3153_);
lean_closure_set(v___f_3165_, 1, v___y_3149_);
lean_closure_set(v___f_3165_, 2, v___y_3148_);
v___x_3166_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3167_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3166_, v___f_3165_, v___y_3154_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref_known(v___x_3167_, 1);
v___x_3168_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3181_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3181_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3181_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
uint8_t v___x_3173_; uint8_t v___x_3174_; uint8_t v___x_3175_; 
v___x_3173_ = 0;
v___x_3174_ = lean_unbox(v_a_3169_);
lean_dec(v_a_3169_);
v___x_3175_ = l_Lean_instBEqLBool_beq(v___x_3174_, v___x_3173_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_dec(v___y_3151_);
v___x_3176_ = lean_box(0);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3176_);
v___x_3178_ = v___x_3171_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
else
{
lean_object* v___x_3180_; 
lean_del_object(v___x_3171_);
v___x_3180_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3151_, v___y_3153_, v___y_3154_);
return v___x_3180_;
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v___y_3151_);
v_a_3182_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3168_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3168_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
return v___x_3167_;
}
}
else
{
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
return v___x_3164_;
}
}
v___jp_3190_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___y_3191_);
v___x_3204_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3203_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
v___jp_3208_:
{
lean_object* v___x_3220_; 
lean_inc_ref(v___y_3218_);
v___x_3220_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3134_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3271_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3271_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3271_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
if (lean_obj_tag(v_a_3221_) == 1)
{
lean_object* v_val_3225_; lean_object* v_p_3226_; 
lean_del_object(v___x_3223_);
v_val_3225_ = lean_ctor_get(v_a_3221_, 0);
lean_inc(v_val_3225_);
lean_dec_ref_known(v_a_3221_, 1);
v_p_3226_ = lean_ctor_get(v_val_3225_, 0);
if (lean_obj_tag(v_p_3226_) == 0)
{
lean_object* v_options_3227_; uint8_t v_hasTrace_3228_; 
v_options_3227_ = lean_ctor_get(v___y_3218_, 1);
v_hasTrace_3228_ = lean_ctor_get_uint8(v_options_3227_, sizeof(void*)*1);
if (v_hasTrace_3228_ == 0)
{
v___y_3191_ = v_val_3225_;
v___y_3192_ = v___y_3209_;
v___y_3193_ = v___y_3210_;
v___y_3194_ = v___y_3211_;
v___y_3195_ = v___y_3212_;
v___y_3196_ = v___y_3213_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
goto v___jp_3190_;
}
else
{
lean_object* v_toCold_3229_; lean_object* v_inheritedTraceOptions_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_toCold_3229_ = lean_ctor_get(v___y_3218_, 0);
v_inheritedTraceOptions_3230_ = lean_ctor_get(v_toCold_3229_, 4);
v___x_3231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3230_, v_options_3227_, v___x_3232_);
if (v___x_3233_ == 0)
{
v___y_3191_ = v_val_3225_;
v___y_3192_ = v___y_3209_;
v___y_3193_ = v___y_3210_;
v___y_3194_ = v___y_3211_;
v___y_3195_ = v___y_3212_;
v___y_3196_ = v___y_3213_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
goto v___jp_3190_;
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3225_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l_Lean_MessageData_ofExpr(v_a_3235_);
v___x_3237_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3231_, v___x_3236_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_dec_ref_known(v___x_3237_, 1);
v___y_3191_ = v_val_3225_;
v___y_3192_ = v___y_3209_;
v___y_3193_ = v___y_3210_;
v___y_3194_ = v___y_3211_;
v___y_3195_ = v___y_3212_;
v___y_3196_ = v___y_3213_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
goto v___jp_3190_;
}
else
{
lean_dec(v_val_3225_);
return v___x_3237_;
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v_val_3225_);
v_a_3238_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3234_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3234_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
else
{
lean_object* v_options_3246_; uint8_t v_hasTrace_3247_; 
lean_inc_ref(v_p_3226_);
v_options_3246_ = lean_ctor_get(v___y_3218_, 1);
v_hasTrace_3247_ = lean_ctor_get_uint8(v_options_3246_, sizeof(void*)*1);
if (v_hasTrace_3247_ == 0)
{
lean_object* v_v_3248_; 
v_v_3248_ = lean_ctor_get(v_p_3226_, 1);
lean_inc_n(v_v_3248_, 2);
lean_inc(v_val_3225_);
v___y_3148_ = v_v_3248_;
v___y_3149_ = v_val_3225_;
v___y_3150_ = v_p_3226_;
v___y_3151_ = v_v_3248_;
v___y_3152_ = v_val_3225_;
v___y_3153_ = v___y_3209_;
v___y_3154_ = v___y_3210_;
v___y_3155_ = v___y_3211_;
v___y_3156_ = v___y_3212_;
v___y_3157_ = v___y_3213_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
goto v___jp_3147_;
}
else
{
lean_object* v_toCold_3249_; lean_object* v_v_3250_; lean_object* v_inheritedTraceOptions_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_toCold_3249_ = lean_ctor_get(v___y_3218_, 0);
v_v_3250_ = lean_ctor_get(v_p_3226_, 1);
lean_inc(v_v_3250_);
v_inheritedTraceOptions_3251_ = lean_ctor_get(v_toCold_3249_, 4);
v___x_3252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3254_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3251_, v_options_3246_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_inc(v_val_3225_);
lean_inc(v_v_3250_);
v___y_3148_ = v_v_3250_;
v___y_3149_ = v_val_3225_;
v___y_3150_ = v_p_3226_;
v___y_3151_ = v_v_3250_;
v___y_3152_ = v_val_3225_;
v___y_3153_ = v___y_3209_;
v___y_3154_ = v___y_3210_;
v___y_3155_ = v___y_3211_;
v___y_3156_ = v___y_3212_;
v___y_3157_ = v___y_3213_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3225_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = l_Lean_MessageData_ofExpr(v_a_3256_);
v___x_3258_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3252_, v___x_3257_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
lean_inc(v_val_3225_);
lean_inc(v_v_3250_);
v___y_3148_ = v_v_3250_;
v___y_3149_ = v_val_3225_;
v___y_3150_ = v_p_3226_;
v___y_3151_ = v_v_3250_;
v___y_3152_ = v_val_3225_;
v___y_3153_ = v___y_3209_;
v___y_3154_ = v___y_3210_;
v___y_3155_ = v___y_3211_;
v___y_3156_ = v___y_3212_;
v___y_3157_ = v___y_3213_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
goto v___jp_3147_;
}
else
{
lean_dec(v_v_3250_);
lean_dec_ref_known(v_p_3226_, 3);
lean_dec(v_val_3225_);
return v___x_3258_;
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_v_3250_);
lean_dec_ref_known(v_p_3226_, 3);
lean_dec(v_val_3225_);
v_a_3259_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3255_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3255_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
lean_dec(v_a_3221_);
v___x_3267_ = lean_box(0);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3267_);
v___x_3269_ = v___x_3223_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
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
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_a_3272_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3220_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3220_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
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
lean_object* v_cs_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; size_t v_sz_3545_; size_t v___x_3546_; lean_object* v___x_3547_; lean_object* v_fst_3548_; 
v_cs_3542_ = lean_ctor_get(v_n_3540_, 0);
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v_b_3541_);
v_sz_3545_ = lean_array_size(v_cs_3542_);
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3538_, v_x_3539_, v_cs_3542_, v_sz_3545_, v___x_3546_, v___x_3544_);
v_fst_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_fst_3548_);
if (lean_obj_tag(v_fst_3548_) == 0)
{
lean_object* v_snd_3549_; lean_object* v___x_3550_; 
v_snd_3549_ = lean_ctor_get(v___x_3547_, 1);
lean_inc(v_snd_3549_);
lean_dec_ref(v___x_3547_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_snd_3549_);
return v___x_3550_;
}
else
{
lean_object* v_val_3551_; 
lean_dec_ref(v___x_3547_);
v_val_3551_ = lean_ctor_get(v_fst_3548_, 0);
lean_inc(v_val_3551_);
lean_dec_ref_known(v_fst_3548_, 1);
return v_val_3551_;
}
}
else
{
lean_object* v_vs_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; size_t v_sz_3555_; size_t v___x_3556_; lean_object* v___x_3557_; lean_object* v_fst_3558_; 
v_vs_3552_ = lean_ctor_get(v_n_3540_, 0);
v___x_3553_ = lean_box(0);
v___x_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
lean_ctor_set(v___x_3554_, 1, v_b_3541_);
v_sz_3555_ = lean_array_size(v_vs_3552_);
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3539_, v_vs_3552_, v_sz_3555_, v___x_3556_, v___x_3554_);
v_fst_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_fst_3558_);
if (lean_obj_tag(v_fst_3558_) == 0)
{
lean_object* v_snd_3559_; lean_object* v___x_3560_; 
v_snd_3559_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_snd_3559_);
lean_dec_ref(v___x_3557_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_snd_3559_);
return v___x_3560_;
}
else
{
lean_object* v_val_3561_; 
lean_dec_ref(v___x_3557_);
v_val_3561_ = lean_ctor_get(v_fst_3558_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v_fst_3558_, 1);
return v_val_3561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3562_, lean_object* v_x_3563_, lean_object* v_as_3564_, size_t v_sz_3565_, size_t v_i_3566_, lean_object* v_b_3567_){
_start:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_usize_dec_lt(v_i_3566_, v_sz_3565_);
if (v___x_3568_ == 0)
{
return v_b_3567_;
}
else
{
lean_object* v_snd_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3587_; 
v_snd_3569_ = lean_ctor_get(v_b_3567_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_b_3567_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v_b_3567_, 0);
lean_dec(v_unused_3588_);
v___x_3571_ = v_b_3567_;
v_isShared_3572_ = v_isSharedCheck_3587_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snd_3569_);
lean_dec(v_b_3567_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3587_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_array_uget_borrowed(v_as_3564_, v_i_3566_);
lean_inc(v_snd_3569_);
v___x_3574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3562_, v_x_3563_, v_a_3573_, v_snd_3569_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3575_);
v___x_3577_ = v___x_3571_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_snd_3569_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
lean_dec(v_snd_3569_);
v_a_3579_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3580_ = lean_box(0);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v_a_3579_);
lean_ctor_set(v___x_3571_, 0, v___x_3580_);
v___x_3582_ = v___x_3571_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_a_3579_);
v___x_3582_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
size_t v___x_3583_; size_t v___x_3584_; 
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_add(v_i_3566_, v___x_3583_);
v_i_3566_ = v___x_3584_;
v_b_3567_ = v___x_3582_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3589_, lean_object* v_x_3590_, lean_object* v_as_3591_, lean_object* v_sz_3592_, lean_object* v_i_3593_, lean_object* v_b_3594_){
_start:
{
size_t v_sz_boxed_3595_; size_t v_i_boxed_3596_; lean_object* v_res_3597_; 
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3592_);
lean_dec(v_sz_3592_);
v_i_boxed_3596_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_res_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3589_, v_x_3590_, v_as_3591_, v_sz_boxed_3595_, v_i_boxed_3596_, v_b_3594_);
lean_dec_ref(v_as_3591_);
lean_dec(v_x_3590_);
lean_dec_ref(v_init_3589_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3598_, lean_object* v_x_3599_, lean_object* v_n_3600_, lean_object* v_b_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3598_, v_x_3599_, v_n_3600_, v_b_3601_);
lean_dec_ref(v_n_3600_);
lean_dec(v_x_3599_);
lean_dec_ref(v_init_3598_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3603_, lean_object* v_t_3604_, lean_object* v_init_3605_){
_start:
{
lean_object* v_root_3606_; lean_object* v_tail_3607_; lean_object* v___x_3608_; 
v_root_3606_ = lean_ctor_get(v_t_3604_, 0);
v_tail_3607_ = lean_ctor_get(v_t_3604_, 1);
lean_inc_ref(v_init_3605_);
v___x_3608_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3605_, v_x_3603_, v_root_3606_, v_init_3605_);
lean_dec_ref(v_init_3605_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
return v_a_3609_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; size_t v_sz_3613_; size_t v___x_3614_; lean_object* v___x_3615_; lean_object* v_fst_3616_; 
v_a_3610_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3611_ = lean_box(0);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v_a_3610_);
v_sz_3613_ = lean_array_size(v_tail_3607_);
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3603_, v_tail_3607_, v_sz_3613_, v___x_3614_, v___x_3612_);
v_fst_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_fst_3616_);
if (lean_obj_tag(v_fst_3616_) == 0)
{
lean_object* v_snd_3617_; 
v_snd_3617_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_snd_3617_);
lean_dec_ref(v___x_3615_);
return v_snd_3617_;
}
else
{
lean_object* v_val_3618_; 
lean_dec_ref(v___x_3615_);
v_val_3618_ = lean_ctor_get(v_fst_3616_, 0);
lean_inc(v_val_3618_);
lean_dec_ref_known(v_fst_3616_, 1);
return v_val_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3619_, lean_object* v_t_3620_, lean_object* v_init_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3619_, v_t_3620_, v_init_3621_);
lean_dec_ref(v_t_3620_);
lean_dec(v_x_3619_);
return v_res_3622_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3623_ = lean_unsigned_to_nat(32u);
v___x_3624_ = lean_mk_empty_array_with_capacity(v___x_3623_);
v___x_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_cs_x27_3631_; 
v___x_3626_ = ((size_t)5ULL);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_unsigned_to_nat(32u);
v___x_3629_ = lean_mk_empty_array_with_capacity(v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3631_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3631_, 0, v___x_3630_);
lean_ctor_set(v_cs_x27_3631_, 1, v___x_3629_);
lean_ctor_set(v_cs_x27_3631_, 2, v___x_3627_);
lean_ctor_set(v_cs_x27_3631_, 3, v___x_3627_);
lean_ctor_set_usize(v_cs_x27_3631_, 4, v___x_3626_);
return v_cs_x27_3631_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3634_; lean_object* v_cs_x27_3635_; lean_object* v___x_3636_; 
v_todo_3634_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3635_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v_cs_x27_3635_);
lean_ctor_set(v___x_3636_, 1, v_todo_3634_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3637_, lean_object* v_cs_3638_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v_fst_3641_; lean_object* v_snd_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v___x_3639_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3640_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3637_, v_cs_3638_, v___x_3639_);
v_fst_3641_ = lean_ctor_get(v___x_3640_, 0);
v_snd_3642_ = lean_ctor_get(v___x_3640_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3640_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snd_3642_);
lean_inc(v_fst_3641_);
lean_dec(v___x_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_fst_3641_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_snd_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3650_, lean_object* v_cs_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3650_, v_cs_3651_);
lean_dec_ref(v_cs_3651_);
lean_dec(v_x_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3653_, lean_object* v_cs_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3653_, v_cs_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3656_, lean_object* v_cs_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3656_, v_cs_3657_);
lean_dec_ref(v_cs_3657_);
lean_dec(v_x_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3659_, lean_object* v_y_3660_, lean_object* v_fst_3661_, lean_object* v_s_3662_){
_start:
{
lean_object* v_structs_3663_; lean_object* v_typeIdOf_3664_; lean_object* v_exprToStructId_3665_; lean_object* v_exprToStructIdEntries_3666_; lean_object* v_forbiddenNatModules_3667_; lean_object* v_natStructs_3668_; lean_object* v_natTypeIdOf_3669_; lean_object* v_exprToNatStructId_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v_structs_3663_ = lean_ctor_get(v_s_3662_, 0);
v_typeIdOf_3664_ = lean_ctor_get(v_s_3662_, 1);
v_exprToStructId_3665_ = lean_ctor_get(v_s_3662_, 2);
v_exprToStructIdEntries_3666_ = lean_ctor_get(v_s_3662_, 3);
v_forbiddenNatModules_3667_ = lean_ctor_get(v_s_3662_, 4);
v_natStructs_3668_ = lean_ctor_get(v_s_3662_, 5);
v_natTypeIdOf_3669_ = lean_ctor_get(v_s_3662_, 6);
v_exprToNatStructId_3670_ = lean_ctor_get(v_s_3662_, 7);
v___x_3671_ = lean_array_get_size(v_structs_3663_);
v___x_3672_ = lean_nat_dec_lt(v_a_3659_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_dec_ref(v_fst_3661_);
return v_s_3662_;
}
else
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3734_; 
lean_inc_ref(v_exprToNatStructId_3670_);
lean_inc_ref(v_natTypeIdOf_3669_);
lean_inc_ref(v_natStructs_3668_);
lean_inc_ref(v_forbiddenNatModules_3667_);
lean_inc_ref(v_exprToStructIdEntries_3666_);
lean_inc_ref(v_exprToStructId_3665_);
lean_inc_ref(v_typeIdOf_3664_);
lean_inc_ref(v_structs_3663_);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_s_3662_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3735_ = lean_ctor_get(v_s_3662_, 7);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_s_3662_, 6);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_s_3662_, 5);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_s_3662_, 4);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_s_3662_, 3);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_s_3662_, 2);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_s_3662_, 1);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_s_3662_, 0);
lean_dec(v_unused_3742_);
v___x_3674_ = v_s_3662_;
v_isShared_3675_ = v_isSharedCheck_3734_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v_s_3662_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3734_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v_v_3676_; lean_object* v_id_3677_; lean_object* v_ringId_x3f_3678_; lean_object* v_type_3679_; lean_object* v_u_3680_; lean_object* v_intModuleInst_3681_; lean_object* v_leInst_x3f_3682_; lean_object* v_ltInst_x3f_3683_; lean_object* v_lawfulOrderLTInst_x3f_3684_; lean_object* v_isPreorderInst_x3f_3685_; lean_object* v_orderedAddInst_x3f_3686_; lean_object* v_isLinearInst_x3f_3687_; lean_object* v_noNatDivInst_x3f_3688_; lean_object* v_ringInst_x3f_3689_; lean_object* v_commRingInst_x3f_3690_; lean_object* v_orderedRingInst_x3f_3691_; lean_object* v_fieldInst_x3f_3692_; lean_object* v_charInst_x3f_3693_; lean_object* v_zero_3694_; lean_object* v_ofNatZero_3695_; lean_object* v_one_x3f_3696_; lean_object* v_leFn_x3f_3697_; lean_object* v_ltFn_x3f_3698_; lean_object* v_addFn_3699_; lean_object* v_zsmulFn_3700_; lean_object* v_nsmulFn_3701_; lean_object* v_zsmulFn_x3f_3702_; lean_object* v_nsmulFn_x3f_3703_; lean_object* v_homomulFn_x3f_3704_; lean_object* v_subFn_3705_; lean_object* v_negFn_3706_; lean_object* v_vars_3707_; lean_object* v_varMap_3708_; lean_object* v_lowers_3709_; lean_object* v_uppers_3710_; lean_object* v_diseqs_3711_; lean_object* v_assignment_3712_; uint8_t v_caseSplits_3713_; lean_object* v_conflict_x3f_3714_; lean_object* v_diseqSplits_3715_; lean_object* v_elimEqs_3716_; lean_object* v_elimStack_3717_; lean_object* v_occurs_3718_; lean_object* v_ignored_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3733_; 
v_v_3676_ = lean_array_fget(v_structs_3663_, v_a_3659_);
v_id_3677_ = lean_ctor_get(v_v_3676_, 0);
v_ringId_x3f_3678_ = lean_ctor_get(v_v_3676_, 1);
v_type_3679_ = lean_ctor_get(v_v_3676_, 2);
v_u_3680_ = lean_ctor_get(v_v_3676_, 3);
v_intModuleInst_3681_ = lean_ctor_get(v_v_3676_, 4);
v_leInst_x3f_3682_ = lean_ctor_get(v_v_3676_, 5);
v_ltInst_x3f_3683_ = lean_ctor_get(v_v_3676_, 6);
v_lawfulOrderLTInst_x3f_3684_ = lean_ctor_get(v_v_3676_, 7);
v_isPreorderInst_x3f_3685_ = lean_ctor_get(v_v_3676_, 8);
v_orderedAddInst_x3f_3686_ = lean_ctor_get(v_v_3676_, 9);
v_isLinearInst_x3f_3687_ = lean_ctor_get(v_v_3676_, 10);
v_noNatDivInst_x3f_3688_ = lean_ctor_get(v_v_3676_, 11);
v_ringInst_x3f_3689_ = lean_ctor_get(v_v_3676_, 12);
v_commRingInst_x3f_3690_ = lean_ctor_get(v_v_3676_, 13);
v_orderedRingInst_x3f_3691_ = lean_ctor_get(v_v_3676_, 14);
v_fieldInst_x3f_3692_ = lean_ctor_get(v_v_3676_, 15);
v_charInst_x3f_3693_ = lean_ctor_get(v_v_3676_, 16);
v_zero_3694_ = lean_ctor_get(v_v_3676_, 17);
v_ofNatZero_3695_ = lean_ctor_get(v_v_3676_, 18);
v_one_x3f_3696_ = lean_ctor_get(v_v_3676_, 19);
v_leFn_x3f_3697_ = lean_ctor_get(v_v_3676_, 20);
v_ltFn_x3f_3698_ = lean_ctor_get(v_v_3676_, 21);
v_addFn_3699_ = lean_ctor_get(v_v_3676_, 22);
v_zsmulFn_3700_ = lean_ctor_get(v_v_3676_, 23);
v_nsmulFn_3701_ = lean_ctor_get(v_v_3676_, 24);
v_zsmulFn_x3f_3702_ = lean_ctor_get(v_v_3676_, 25);
v_nsmulFn_x3f_3703_ = lean_ctor_get(v_v_3676_, 26);
v_homomulFn_x3f_3704_ = lean_ctor_get(v_v_3676_, 27);
v_subFn_3705_ = lean_ctor_get(v_v_3676_, 28);
v_negFn_3706_ = lean_ctor_get(v_v_3676_, 29);
v_vars_3707_ = lean_ctor_get(v_v_3676_, 30);
v_varMap_3708_ = lean_ctor_get(v_v_3676_, 31);
v_lowers_3709_ = lean_ctor_get(v_v_3676_, 32);
v_uppers_3710_ = lean_ctor_get(v_v_3676_, 33);
v_diseqs_3711_ = lean_ctor_get(v_v_3676_, 34);
v_assignment_3712_ = lean_ctor_get(v_v_3676_, 35);
v_caseSplits_3713_ = lean_ctor_get_uint8(v_v_3676_, sizeof(void*)*42);
v_conflict_x3f_3714_ = lean_ctor_get(v_v_3676_, 36);
v_diseqSplits_3715_ = lean_ctor_get(v_v_3676_, 37);
v_elimEqs_3716_ = lean_ctor_get(v_v_3676_, 38);
v_elimStack_3717_ = lean_ctor_get(v_v_3676_, 39);
v_occurs_3718_ = lean_ctor_get(v_v_3676_, 40);
v_ignored_3719_ = lean_ctor_get(v_v_3676_, 41);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_v_3676_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3721_ = v_v_3676_;
v_isShared_3722_ = v_isSharedCheck_3733_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_ignored_3719_);
lean_inc(v_occurs_3718_);
lean_inc(v_elimStack_3717_);
lean_inc(v_elimEqs_3716_);
lean_inc(v_diseqSplits_3715_);
lean_inc(v_conflict_x3f_3714_);
lean_inc(v_assignment_3712_);
lean_inc(v_diseqs_3711_);
lean_inc(v_uppers_3710_);
lean_inc(v_lowers_3709_);
lean_inc(v_varMap_3708_);
lean_inc(v_vars_3707_);
lean_inc(v_negFn_3706_);
lean_inc(v_subFn_3705_);
lean_inc(v_homomulFn_x3f_3704_);
lean_inc(v_nsmulFn_x3f_3703_);
lean_inc(v_zsmulFn_x3f_3702_);
lean_inc(v_nsmulFn_3701_);
lean_inc(v_zsmulFn_3700_);
lean_inc(v_addFn_3699_);
lean_inc(v_ltFn_x3f_3698_);
lean_inc(v_leFn_x3f_3697_);
lean_inc(v_one_x3f_3696_);
lean_inc(v_ofNatZero_3695_);
lean_inc(v_zero_3694_);
lean_inc(v_charInst_x3f_3693_);
lean_inc(v_fieldInst_x3f_3692_);
lean_inc(v_orderedRingInst_x3f_3691_);
lean_inc(v_commRingInst_x3f_3690_);
lean_inc(v_ringInst_x3f_3689_);
lean_inc(v_noNatDivInst_x3f_3688_);
lean_inc(v_isLinearInst_x3f_3687_);
lean_inc(v_orderedAddInst_x3f_3686_);
lean_inc(v_isPreorderInst_x3f_3685_);
lean_inc(v_lawfulOrderLTInst_x3f_3684_);
lean_inc(v_ltInst_x3f_3683_);
lean_inc(v_leInst_x3f_3682_);
lean_inc(v_intModuleInst_3681_);
lean_inc(v_u_3680_);
lean_inc(v_type_3679_);
lean_inc(v_ringId_x3f_3678_);
lean_inc(v_id_3677_);
lean_dec(v_v_3676_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3733_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3723_; lean_object* v_xs_x27_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3723_ = lean_box(0);
v_xs_x27_3724_ = lean_array_fset(v_structs_3663_, v_a_3659_, v___x_3723_);
v___x_3725_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3711_, v_y_3660_, v_fst_3661_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 34, v___x_3725_);
v___x_3727_ = v___x_3721_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_id_3677_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_ringId_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_type_3679_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_u_3680_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_intModuleInst_3681_);
lean_ctor_set(v_reuseFailAlloc_3732_, 5, v_leInst_x3f_3682_);
lean_ctor_set(v_reuseFailAlloc_3732_, 6, v_ltInst_x3f_3683_);
lean_ctor_set(v_reuseFailAlloc_3732_, 7, v_lawfulOrderLTInst_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3732_, 8, v_isPreorderInst_x3f_3685_);
lean_ctor_set(v_reuseFailAlloc_3732_, 9, v_orderedAddInst_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3732_, 10, v_isLinearInst_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3732_, 11, v_noNatDivInst_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3732_, 12, v_ringInst_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3732_, 13, v_commRingInst_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3732_, 14, v_orderedRingInst_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3732_, 15, v_fieldInst_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3732_, 16, v_charInst_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3732_, 17, v_zero_3694_);
lean_ctor_set(v_reuseFailAlloc_3732_, 18, v_ofNatZero_3695_);
lean_ctor_set(v_reuseFailAlloc_3732_, 19, v_one_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3732_, 20, v_leFn_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3732_, 21, v_ltFn_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3732_, 22, v_addFn_3699_);
lean_ctor_set(v_reuseFailAlloc_3732_, 23, v_zsmulFn_3700_);
lean_ctor_set(v_reuseFailAlloc_3732_, 24, v_nsmulFn_3701_);
lean_ctor_set(v_reuseFailAlloc_3732_, 25, v_zsmulFn_x3f_3702_);
lean_ctor_set(v_reuseFailAlloc_3732_, 26, v_nsmulFn_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3732_, 27, v_homomulFn_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3732_, 28, v_subFn_3705_);
lean_ctor_set(v_reuseFailAlloc_3732_, 29, v_negFn_3706_);
lean_ctor_set(v_reuseFailAlloc_3732_, 30, v_vars_3707_);
lean_ctor_set(v_reuseFailAlloc_3732_, 31, v_varMap_3708_);
lean_ctor_set(v_reuseFailAlloc_3732_, 32, v_lowers_3709_);
lean_ctor_set(v_reuseFailAlloc_3732_, 33, v_uppers_3710_);
lean_ctor_set(v_reuseFailAlloc_3732_, 34, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3732_, 35, v_assignment_3712_);
lean_ctor_set(v_reuseFailAlloc_3732_, 36, v_conflict_x3f_3714_);
lean_ctor_set(v_reuseFailAlloc_3732_, 37, v_diseqSplits_3715_);
lean_ctor_set(v_reuseFailAlloc_3732_, 38, v_elimEqs_3716_);
lean_ctor_set(v_reuseFailAlloc_3732_, 39, v_elimStack_3717_);
lean_ctor_set(v_reuseFailAlloc_3732_, 40, v_occurs_3718_);
lean_ctor_set(v_reuseFailAlloc_3732_, 41, v_ignored_3719_);
lean_ctor_set_uint8(v_reuseFailAlloc_3732_, sizeof(void*)*42, v_caseSplits_3713_);
v___x_3727_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = lean_array_fset(v_xs_x27_3724_, v_a_3659_, v___x_3727_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3728_);
v___x_3730_ = v___x_3674_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_typeIdOf_3664_);
lean_ctor_set(v_reuseFailAlloc_3731_, 2, v_exprToStructId_3665_);
lean_ctor_set(v_reuseFailAlloc_3731_, 3, v_exprToStructIdEntries_3666_);
lean_ctor_set(v_reuseFailAlloc_3731_, 4, v_forbiddenNatModules_3667_);
lean_ctor_set(v_reuseFailAlloc_3731_, 5, v_natStructs_3668_);
lean_ctor_set(v_reuseFailAlloc_3731_, 6, v_natTypeIdOf_3669_);
lean_ctor_set(v_reuseFailAlloc_3731_, 7, v_exprToNatStructId_3670_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3743_, lean_object* v_y_3744_, lean_object* v_fst_3745_, lean_object* v_s_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3743_, v_y_3744_, v_fst_3745_, v_s_3746_);
lean_dec(v_y_3744_);
lean_dec(v_a_3743_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3748_, lean_object* v_x_3749_, lean_object* v_c_3750_, lean_object* v_as_3751_, size_t v_sz_3752_, size_t v_i_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_a_3768_; uint8_t v___x_3772_; 
v___x_3772_ = lean_usize_dec_lt(v_i_3753_, v_sz_3752_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; 
lean_dec_ref(v_c_3750_);
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v_b_3754_);
return v___x_3773_;
}
else
{
lean_object* v_a_3774_; lean_object* v_fst_3775_; lean_object* v_snd_3776_; lean_object* v___x_3777_; 
lean_dec_ref(v_b_3754_);
v_a_3774_ = lean_array_uget_borrowed(v_as_3751_, v_i_3753_);
v_fst_3775_ = lean_ctor_get(v_a_3774_, 0);
v_snd_3776_ = lean_ctor_get(v_a_3774_, 1);
lean_inc(v_snd_3776_);
lean_inc(v_fst_3775_);
lean_inc_ref(v_c_3750_);
v___x_3777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3748_, v_x_3749_, v_c_3750_, v_fst_3775_, v_snd_3776_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___x_3779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3778_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; 
v_val_3780_ = lean_ctor_get(v_a_3778_, 0);
lean_inc(v_val_3780_);
lean_dec_ref_known(v_a_3778_, 1);
v___x_3781_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3780_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3782_; 
lean_dec_ref_known(v___x_3781_, 1);
v___x_3782_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3792_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3792_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3792_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_unbox(v_a_3783_);
lean_dec(v_a_3783_);
if (v___x_3787_ == 0)
{
lean_del_object(v___x_3785_);
v_a_3768_ = v___x_3779_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
lean_dec_ref(v_c_3750_);
v___x_3788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3788_);
v___x_3790_ = v___x_3785_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v_c_3750_);
v_a_3793_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3782_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3782_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_c_3750_);
v_a_3801_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3781_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3781_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v___x_3809_; 
lean_dec(v_a_3778_);
v___x_3809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3776_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_dec_ref_known(v___x_3809_, 1);
v_a_3768_ = v___x_3779_;
goto v___jp_3767_;
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v_c_3750_);
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
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
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v_c_3750_);
v_a_3818_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3777_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3777_);
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
v___jp_3767_:
{
size_t v___x_3769_; size_t v___x_3770_; 
v___x_3769_ = ((size_t)1ULL);
v___x_3770_ = lean_usize_add(v_i_3753_, v___x_3769_);
lean_inc_ref(v_a_3768_);
v_i_3753_ = v___x_3770_;
v_b_3754_ = v_a_3768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3826_ = _args[0];
lean_object* v_x_3827_ = _args[1];
lean_object* v_c_3828_ = _args[2];
lean_object* v_as_3829_ = _args[3];
lean_object* v_sz_3830_ = _args[4];
lean_object* v_i_3831_ = _args[5];
lean_object* v_b_3832_ = _args[6];
lean_object* v___y_3833_ = _args[7];
lean_object* v___y_3834_ = _args[8];
lean_object* v___y_3835_ = _args[9];
lean_object* v___y_3836_ = _args[10];
lean_object* v___y_3837_ = _args[11];
lean_object* v___y_3838_ = _args[12];
lean_object* v___y_3839_ = _args[13];
lean_object* v___y_3840_ = _args[14];
lean_object* v___y_3841_ = _args[15];
lean_object* v___y_3842_ = _args[16];
lean_object* v___y_3843_ = _args[17];
lean_object* v___y_3844_ = _args[18];
_start:
{
size_t v_sz_boxed_3845_; size_t v_i_boxed_3846_; lean_object* v_res_3847_; 
v_sz_boxed_3845_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3846_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3826_, v_x_3827_, v_c_3828_, v_as_3829_, v_sz_boxed_3845_, v_i_boxed_3846_, v_b_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v_as_3829_);
lean_dec(v_x_3827_);
lean_dec(v_a_3826_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3848_, lean_object* v_x_3849_, lean_object* v_c_3850_, lean_object* v_y_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3924_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3924_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3924_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_unbox(v_a_3865_);
lean_dec(v_a_3865_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; 
lean_del_object(v___x_3867_);
v___x_3870_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___y_3873_; lean_object* v_diseqs_3906_; lean_object* v_size_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_diseqs_3906_ = lean_ctor_get(v_a_3871_, 34);
lean_inc_ref(v_diseqs_3906_);
lean_dec(v_a_3871_);
v_size_3907_ = lean_ctor_get(v_diseqs_3906_, 2);
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3909_ = lean_nat_dec_lt(v_y_3851_, v_size_3907_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref(v_diseqs_3906_);
v___x_3910_ = l_outOfBounds___redArg(v___x_3908_);
v___y_3873_ = v___x_3910_;
goto v___jp_3872_;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3908_, v_diseqs_3906_, v_y_3851_);
lean_dec_ref(v_diseqs_3906_);
v___y_3873_ = v___x_3911_;
goto v___jp_3872_;
}
v___jp_3872_:
{
lean_object* v___x_3874_; lean_object* v_fst_3875_; lean_object* v_snd_3876_; lean_object* v___f_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3874_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3849_, v___y_3873_);
lean_dec_ref(v___y_3873_);
v_fst_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_fst_3875_);
v_snd_3876_ = lean_ctor_get(v___x_3874_, 1);
lean_inc(v_snd_3876_);
lean_dec_ref(v___x_3874_);
lean_inc(v_a_3852_);
v___f_3877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3877_, 0, v_a_3852_);
lean_closure_set(v___f_3877_, 1, v_y_3851_);
lean_closure_set(v___f_3877_, 2, v_fst_3875_);
v___x_3878_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3879_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3878_, v___f_3877_, v_a_3853_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; size_t v_sz_3882_; size_t v___x_3883_; lean_object* v___x_3884_; 
lean_dec_ref_known(v___x_3879_, 1);
v___x_3880_ = lean_box(0);
v___x_3881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3882_ = lean_array_size(v_snd_3876_);
v___x_3883_ = ((size_t)0ULL);
v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3848_, v_x_3849_, v_c_3850_, v_snd_3876_, v_sz_3882_, v___x_3883_, v___x_3881_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_snd_3876_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3897_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_fst_3889_; 
v_fst_3889_ = lean_ctor_get(v_a_3885_, 0);
lean_inc(v_fst_3889_);
lean_dec(v_a_3885_);
if (lean_obj_tag(v_fst_3889_) == 0)
{
lean_object* v___x_3891_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3880_);
v___x_3891_ = v___x_3887_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3880_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
else
{
lean_object* v_val_3893_; lean_object* v___x_3895_; 
v_val_3893_ = lean_ctor_get(v_fst_3889_, 0);
lean_inc(v_val_3893_);
lean_dec_ref_known(v_fst_3889_, 1);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v_val_3893_);
v___x_3895_ = v___x_3887_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_val_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
v_a_3898_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3884_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3884_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_dec(v_snd_3876_);
lean_dec_ref(v_c_3850_);
return v___x_3879_;
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v_y_3851_);
lean_dec_ref(v_c_3850_);
v_a_3912_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3870_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3870_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
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
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec(v_y_3851_);
lean_dec_ref(v_c_3850_);
v___x_3920_ = lean_box(0);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3920_);
v___x_3922_ = v___x_3867_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_y_3851_);
lean_dec_ref(v_c_3850_);
v_a_3925_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3864_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3864_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3933_, lean_object* v_x_3934_, lean_object* v_c_3935_, lean_object* v_y_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3933_, v_x_3934_, v_c_3935_, v_y_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec(v_x_3934_);
lean_dec(v_a_3933_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3950_, lean_object* v_x_3951_, lean_object* v_c_3952_, lean_object* v_y_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; 
lean_inc(v_y_3953_);
lean_inc_ref(v_c_3952_);
lean_inc(v_x_3951_);
lean_inc(v_a_3950_);
v___x_3966_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3950_, v_x_3951_, v_c_3952_, v_y_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___x_3967_; 
lean_dec_ref_known(v___x_3966_, 1);
lean_inc(v_y_3953_);
lean_inc_ref(v_c_3952_);
lean_inc(v_x_3951_);
lean_inc(v_a_3950_);
v___x_3967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3950_, v_x_3951_, v_c_3952_, v_y_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec_ref_known(v___x_3967_, 1);
v___x_3968_ = lean_nat_to_int(v_a_3950_);
v___x_3969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3968_, v_x_3951_, v_c_3952_, v_y_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
lean_dec(v_x_3951_);
lean_dec(v___x_3968_);
return v___x_3969_;
}
else
{
lean_dec(v_y_3953_);
lean_dec_ref(v_c_3952_);
lean_dec(v_x_3951_);
lean_dec(v_a_3950_);
return v___x_3967_;
}
}
else
{
lean_dec(v_y_3953_);
lean_dec_ref(v_c_3952_);
lean_dec(v_x_3951_);
lean_dec(v_a_3950_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3970_, lean_object* v_x_3971_, lean_object* v_c_3972_, lean_object* v_y_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3970_, v_x_3971_, v_c_3972_, v_y_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec(v_a_3974_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3987_, lean_object* v_x_3988_, lean_object* v_s_3989_){
_start:
{
lean_object* v_structs_3990_; lean_object* v_typeIdOf_3991_; lean_object* v_exprToStructId_3992_; lean_object* v_exprToStructIdEntries_3993_; lean_object* v_forbiddenNatModules_3994_; lean_object* v_natStructs_3995_; lean_object* v_natTypeIdOf_3996_; lean_object* v_exprToNatStructId_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_structs_3990_ = lean_ctor_get(v_s_3989_, 0);
v_typeIdOf_3991_ = lean_ctor_get(v_s_3989_, 1);
v_exprToStructId_3992_ = lean_ctor_get(v_s_3989_, 2);
v_exprToStructIdEntries_3993_ = lean_ctor_get(v_s_3989_, 3);
v_forbiddenNatModules_3994_ = lean_ctor_get(v_s_3989_, 4);
v_natStructs_3995_ = lean_ctor_get(v_s_3989_, 5);
v_natTypeIdOf_3996_ = lean_ctor_get(v_s_3989_, 6);
v_exprToNatStructId_3997_ = lean_ctor_get(v_s_3989_, 7);
v___x_3998_ = lean_array_get_size(v_structs_3990_);
v___x_3999_ = lean_nat_dec_lt(v_a_3987_, v___x_3998_);
if (v___x_3999_ == 0)
{
return v_s_3989_;
}
else
{
lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4062_; 
lean_inc_ref(v_exprToNatStructId_3997_);
lean_inc_ref(v_natTypeIdOf_3996_);
lean_inc_ref(v_natStructs_3995_);
lean_inc_ref(v_forbiddenNatModules_3994_);
lean_inc_ref(v_exprToStructIdEntries_3993_);
lean_inc_ref(v_exprToStructId_3992_);
lean_inc_ref(v_typeIdOf_3991_);
lean_inc_ref(v_structs_3990_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_s_3989_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; lean_object* v_unused_4070_; 
v_unused_4063_ = lean_ctor_get(v_s_3989_, 7);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_s_3989_, 6);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_s_3989_, 5);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_s_3989_, 4);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_s_3989_, 3);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_s_3989_, 2);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_s_3989_, 1);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_s_3989_, 0);
lean_dec(v_unused_4070_);
v___x_4001_ = v_s_3989_;
v_isShared_4002_ = v_isSharedCheck_4062_;
goto v_resetjp_4000_;
}
else
{
lean_dec(v_s_3989_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4062_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v_v_4003_; lean_object* v_id_4004_; lean_object* v_ringId_x3f_4005_; lean_object* v_type_4006_; lean_object* v_u_4007_; lean_object* v_intModuleInst_4008_; lean_object* v_leInst_x3f_4009_; lean_object* v_ltInst_x3f_4010_; lean_object* v_lawfulOrderLTInst_x3f_4011_; lean_object* v_isPreorderInst_x3f_4012_; lean_object* v_orderedAddInst_x3f_4013_; lean_object* v_isLinearInst_x3f_4014_; lean_object* v_noNatDivInst_x3f_4015_; lean_object* v_ringInst_x3f_4016_; lean_object* v_commRingInst_x3f_4017_; lean_object* v_orderedRingInst_x3f_4018_; lean_object* v_fieldInst_x3f_4019_; lean_object* v_charInst_x3f_4020_; lean_object* v_zero_4021_; lean_object* v_ofNatZero_4022_; lean_object* v_one_x3f_4023_; lean_object* v_leFn_x3f_4024_; lean_object* v_ltFn_x3f_4025_; lean_object* v_addFn_4026_; lean_object* v_zsmulFn_4027_; lean_object* v_nsmulFn_4028_; lean_object* v_zsmulFn_x3f_4029_; lean_object* v_nsmulFn_x3f_4030_; lean_object* v_homomulFn_x3f_4031_; lean_object* v_subFn_4032_; lean_object* v_negFn_4033_; lean_object* v_vars_4034_; lean_object* v_varMap_4035_; lean_object* v_lowers_4036_; lean_object* v_uppers_4037_; lean_object* v_diseqs_4038_; lean_object* v_assignment_4039_; uint8_t v_caseSplits_4040_; lean_object* v_conflict_x3f_4041_; lean_object* v_diseqSplits_4042_; lean_object* v_elimEqs_4043_; lean_object* v_elimStack_4044_; lean_object* v_occurs_4045_; lean_object* v_ignored_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4061_; 
v_v_4003_ = lean_array_fget(v_structs_3990_, v_a_3987_);
v_id_4004_ = lean_ctor_get(v_v_4003_, 0);
v_ringId_x3f_4005_ = lean_ctor_get(v_v_4003_, 1);
v_type_4006_ = lean_ctor_get(v_v_4003_, 2);
v_u_4007_ = lean_ctor_get(v_v_4003_, 3);
v_intModuleInst_4008_ = lean_ctor_get(v_v_4003_, 4);
v_leInst_x3f_4009_ = lean_ctor_get(v_v_4003_, 5);
v_ltInst_x3f_4010_ = lean_ctor_get(v_v_4003_, 6);
v_lawfulOrderLTInst_x3f_4011_ = lean_ctor_get(v_v_4003_, 7);
v_isPreorderInst_x3f_4012_ = lean_ctor_get(v_v_4003_, 8);
v_orderedAddInst_x3f_4013_ = lean_ctor_get(v_v_4003_, 9);
v_isLinearInst_x3f_4014_ = lean_ctor_get(v_v_4003_, 10);
v_noNatDivInst_x3f_4015_ = lean_ctor_get(v_v_4003_, 11);
v_ringInst_x3f_4016_ = lean_ctor_get(v_v_4003_, 12);
v_commRingInst_x3f_4017_ = lean_ctor_get(v_v_4003_, 13);
v_orderedRingInst_x3f_4018_ = lean_ctor_get(v_v_4003_, 14);
v_fieldInst_x3f_4019_ = lean_ctor_get(v_v_4003_, 15);
v_charInst_x3f_4020_ = lean_ctor_get(v_v_4003_, 16);
v_zero_4021_ = lean_ctor_get(v_v_4003_, 17);
v_ofNatZero_4022_ = lean_ctor_get(v_v_4003_, 18);
v_one_x3f_4023_ = lean_ctor_get(v_v_4003_, 19);
v_leFn_x3f_4024_ = lean_ctor_get(v_v_4003_, 20);
v_ltFn_x3f_4025_ = lean_ctor_get(v_v_4003_, 21);
v_addFn_4026_ = lean_ctor_get(v_v_4003_, 22);
v_zsmulFn_4027_ = lean_ctor_get(v_v_4003_, 23);
v_nsmulFn_4028_ = lean_ctor_get(v_v_4003_, 24);
v_zsmulFn_x3f_4029_ = lean_ctor_get(v_v_4003_, 25);
v_nsmulFn_x3f_4030_ = lean_ctor_get(v_v_4003_, 26);
v_homomulFn_x3f_4031_ = lean_ctor_get(v_v_4003_, 27);
v_subFn_4032_ = lean_ctor_get(v_v_4003_, 28);
v_negFn_4033_ = lean_ctor_get(v_v_4003_, 29);
v_vars_4034_ = lean_ctor_get(v_v_4003_, 30);
v_varMap_4035_ = lean_ctor_get(v_v_4003_, 31);
v_lowers_4036_ = lean_ctor_get(v_v_4003_, 32);
v_uppers_4037_ = lean_ctor_get(v_v_4003_, 33);
v_diseqs_4038_ = lean_ctor_get(v_v_4003_, 34);
v_assignment_4039_ = lean_ctor_get(v_v_4003_, 35);
v_caseSplits_4040_ = lean_ctor_get_uint8(v_v_4003_, sizeof(void*)*42);
v_conflict_x3f_4041_ = lean_ctor_get(v_v_4003_, 36);
v_diseqSplits_4042_ = lean_ctor_get(v_v_4003_, 37);
v_elimEqs_4043_ = lean_ctor_get(v_v_4003_, 38);
v_elimStack_4044_ = lean_ctor_get(v_v_4003_, 39);
v_occurs_4045_ = lean_ctor_get(v_v_4003_, 40);
v_ignored_4046_ = lean_ctor_get(v_v_4003_, 41);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_v_4003_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4048_ = v_v_4003_;
v_isShared_4049_ = v_isSharedCheck_4061_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_ignored_4046_);
lean_inc(v_occurs_4045_);
lean_inc(v_elimStack_4044_);
lean_inc(v_elimEqs_4043_);
lean_inc(v_diseqSplits_4042_);
lean_inc(v_conflict_x3f_4041_);
lean_inc(v_assignment_4039_);
lean_inc(v_diseqs_4038_);
lean_inc(v_uppers_4037_);
lean_inc(v_lowers_4036_);
lean_inc(v_varMap_4035_);
lean_inc(v_vars_4034_);
lean_inc(v_negFn_4033_);
lean_inc(v_subFn_4032_);
lean_inc(v_homomulFn_x3f_4031_);
lean_inc(v_nsmulFn_x3f_4030_);
lean_inc(v_zsmulFn_x3f_4029_);
lean_inc(v_nsmulFn_4028_);
lean_inc(v_zsmulFn_4027_);
lean_inc(v_addFn_4026_);
lean_inc(v_ltFn_x3f_4025_);
lean_inc(v_leFn_x3f_4024_);
lean_inc(v_one_x3f_4023_);
lean_inc(v_ofNatZero_4022_);
lean_inc(v_zero_4021_);
lean_inc(v_charInst_x3f_4020_);
lean_inc(v_fieldInst_x3f_4019_);
lean_inc(v_orderedRingInst_x3f_4018_);
lean_inc(v_commRingInst_x3f_4017_);
lean_inc(v_ringInst_x3f_4016_);
lean_inc(v_noNatDivInst_x3f_4015_);
lean_inc(v_isLinearInst_x3f_4014_);
lean_inc(v_orderedAddInst_x3f_4013_);
lean_inc(v_isPreorderInst_x3f_4012_);
lean_inc(v_lawfulOrderLTInst_x3f_4011_);
lean_inc(v_ltInst_x3f_4010_);
lean_inc(v_leInst_x3f_4009_);
lean_inc(v_intModuleInst_4008_);
lean_inc(v_u_4007_);
lean_inc(v_type_4006_);
lean_inc(v_ringId_x3f_4005_);
lean_inc(v_id_4004_);
lean_dec(v_v_4003_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4061_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v_xs_x27_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4050_ = lean_box(0);
v_xs_x27_4051_ = lean_array_fset(v_structs_3990_, v_a_3987_, v___x_4050_);
v___x_4052_ = lean_box(1);
v___x_4053_ = l_Lean_PersistentArray_set___redArg(v_occurs_4045_, v_x_3988_, v___x_4052_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 40, v___x_4053_);
v___x_4055_ = v___x_4048_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_id_4004_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_ringId_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_type_4006_);
lean_ctor_set(v_reuseFailAlloc_4060_, 3, v_u_4007_);
lean_ctor_set(v_reuseFailAlloc_4060_, 4, v_intModuleInst_4008_);
lean_ctor_set(v_reuseFailAlloc_4060_, 5, v_leInst_x3f_4009_);
lean_ctor_set(v_reuseFailAlloc_4060_, 6, v_ltInst_x3f_4010_);
lean_ctor_set(v_reuseFailAlloc_4060_, 7, v_lawfulOrderLTInst_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4060_, 8, v_isPreorderInst_x3f_4012_);
lean_ctor_set(v_reuseFailAlloc_4060_, 9, v_orderedAddInst_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4060_, 10, v_isLinearInst_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4060_, 11, v_noNatDivInst_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4060_, 12, v_ringInst_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4060_, 13, v_commRingInst_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4060_, 14, v_orderedRingInst_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4060_, 15, v_fieldInst_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4060_, 16, v_charInst_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4060_, 17, v_zero_4021_);
lean_ctor_set(v_reuseFailAlloc_4060_, 18, v_ofNatZero_4022_);
lean_ctor_set(v_reuseFailAlloc_4060_, 19, v_one_x3f_4023_);
lean_ctor_set(v_reuseFailAlloc_4060_, 20, v_leFn_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4060_, 21, v_ltFn_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4060_, 22, v_addFn_4026_);
lean_ctor_set(v_reuseFailAlloc_4060_, 23, v_zsmulFn_4027_);
lean_ctor_set(v_reuseFailAlloc_4060_, 24, v_nsmulFn_4028_);
lean_ctor_set(v_reuseFailAlloc_4060_, 25, v_zsmulFn_x3f_4029_);
lean_ctor_set(v_reuseFailAlloc_4060_, 26, v_nsmulFn_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4060_, 27, v_homomulFn_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4060_, 28, v_subFn_4032_);
lean_ctor_set(v_reuseFailAlloc_4060_, 29, v_negFn_4033_);
lean_ctor_set(v_reuseFailAlloc_4060_, 30, v_vars_4034_);
lean_ctor_set(v_reuseFailAlloc_4060_, 31, v_varMap_4035_);
lean_ctor_set(v_reuseFailAlloc_4060_, 32, v_lowers_4036_);
lean_ctor_set(v_reuseFailAlloc_4060_, 33, v_uppers_4037_);
lean_ctor_set(v_reuseFailAlloc_4060_, 34, v_diseqs_4038_);
lean_ctor_set(v_reuseFailAlloc_4060_, 35, v_assignment_4039_);
lean_ctor_set(v_reuseFailAlloc_4060_, 36, v_conflict_x3f_4041_);
lean_ctor_set(v_reuseFailAlloc_4060_, 37, v_diseqSplits_4042_);
lean_ctor_set(v_reuseFailAlloc_4060_, 38, v_elimEqs_4043_);
lean_ctor_set(v_reuseFailAlloc_4060_, 39, v_elimStack_4044_);
lean_ctor_set(v_reuseFailAlloc_4060_, 40, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4060_, 41, v_ignored_4046_);
lean_ctor_set_uint8(v_reuseFailAlloc_4060_, sizeof(void*)*42, v_caseSplits_4040_);
v___x_4055_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4056_ = lean_array_fset(v_xs_x27_4051_, v_a_3987_, v___x_4055_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4056_);
v___x_4058_ = v___x_4001_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_typeIdOf_3991_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_exprToStructId_3992_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_exprToStructIdEntries_3993_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_forbiddenNatModules_3994_);
lean_ctor_set(v_reuseFailAlloc_4059_, 5, v_natStructs_3995_);
lean_ctor_set(v_reuseFailAlloc_4059_, 6, v_natTypeIdOf_3996_);
lean_ctor_set(v_reuseFailAlloc_4059_, 7, v_exprToNatStructId_3997_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4071_, lean_object* v_x_4072_, lean_object* v_s_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4071_, v_x_4072_, v_s_4073_);
lean_dec(v_x_4072_);
lean_dec(v_a_4071_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4075_, lean_object* v_x_4076_, lean_object* v_c_4077_, lean_object* v_init_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
if (lean_obj_tag(v_x_4079_) == 0)
{
lean_object* v_k_4092_; lean_object* v_l_4093_; lean_object* v_r_4094_; lean_object* v___x_4095_; 
v_k_4092_ = lean_ctor_get(v_x_4079_, 1);
lean_inc(v_k_4092_);
v_l_4093_ = lean_ctor_get(v_x_4079_, 3);
lean_inc(v_l_4093_);
v_r_4094_ = lean_ctor_get(v_x_4079_, 4);
lean_inc(v_r_4094_);
lean_dec_ref_known(v_x_4079_, 5);
lean_inc_ref(v_c_4077_);
lean_inc(v_x_4076_);
lean_inc(v_a_4075_);
v___x_4095_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4075_, v_x_4076_, v_c_4077_, v_init_4078_, v_l_4093_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v___x_4096_; 
lean_dec_ref_known(v___x_4095_, 1);
lean_inc_ref(v_c_4077_);
lean_inc(v_x_4076_);
lean_inc(v_a_4075_);
v___x_4096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4075_, v_x_4076_, v_c_4077_, v_k_4092_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; 
lean_dec_ref_known(v___x_4096_, 1);
v___x_4097_ = lean_box(0);
v_init_4078_ = v___x_4097_;
v_x_4079_ = v_r_4094_;
goto _start;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_r_4094_);
lean_dec_ref(v_c_4077_);
lean_dec(v_x_4076_);
lean_dec(v_a_4075_);
v_a_4099_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4096_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4096_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_dec(v_r_4094_);
lean_dec(v_k_4092_);
lean_dec_ref(v_c_4077_);
lean_dec(v_x_4076_);
lean_dec(v_a_4075_);
return v___x_4095_;
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v_c_4077_);
lean_dec(v_x_4076_);
lean_dec(v_a_4075_);
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_init_4078_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4109_ = _args[0];
lean_object* v_x_4110_ = _args[1];
lean_object* v_c_4111_ = _args[2];
lean_object* v_init_4112_ = _args[3];
lean_object* v_x_4113_ = _args[4];
lean_object* v___y_4114_ = _args[5];
lean_object* v___y_4115_ = _args[6];
lean_object* v___y_4116_ = _args[7];
lean_object* v___y_4117_ = _args[8];
lean_object* v___y_4118_ = _args[9];
lean_object* v___y_4119_ = _args[10];
lean_object* v___y_4120_ = _args[11];
lean_object* v___y_4121_ = _args[12];
lean_object* v___y_4122_ = _args[13];
lean_object* v___y_4123_ = _args[14];
lean_object* v___y_4124_ = _args[15];
lean_object* v___y_4125_ = _args[16];
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4109_, v_x_4110_, v_c_4111_, v_init_4112_, v_x_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec(v___y_4114_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4127_, lean_object* v_x_4128_, lean_object* v_c_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v_occurs_4144_; lean_object* v_size_4145_; lean_object* v___f_4146_; lean_object* v___y_4148_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v_occurs_4144_ = lean_ctor_get(v_a_4143_, 40);
lean_inc_ref(v_occurs_4144_);
lean_dec(v_a_4143_);
v_size_4145_ = lean_ctor_get(v_occurs_4144_, 2);
lean_inc(v_x_4128_);
lean_inc(v_a_4130_);
v___f_4146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4146_, 0, v_a_4130_);
lean_closure_set(v___f_4146_, 1, v_x_4128_);
v___x_4170_ = lean_box(1);
v___x_4171_ = lean_nat_dec_lt(v_x_4128_, v_size_4145_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v_occurs_4144_);
v___x_4172_ = l_outOfBounds___redArg(v___x_4170_);
v___y_4148_ = v___x_4172_;
goto v___jp_4147_;
}
else
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4170_, v_occurs_4144_, v_x_4128_);
lean_dec_ref(v_occurs_4144_);
v___y_4148_ = v___x_4173_;
goto v___jp_4147_;
}
v___jp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4150_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4149_, v___f_4146_, v_a_4131_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v___x_4151_; 
lean_dec_ref_known(v___x_4150_, 1);
lean_inc_ref(v_c_4129_);
lean_inc_n(v_x_4128_, 2);
lean_inc(v_a_4127_);
v___x_4151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4127_, v_x_4128_, v_c_4129_, v_x_4128_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec_ref_known(v___x_4151_, 1);
v___x_4152_ = lean_box(0);
v___x_4153_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4127_, v_x_4128_, v_c_4129_, v___x_4152_, v___y_4148_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v___x_4153_, 0);
lean_dec(v_unused_4161_);
v___x_4155_ = v___x_4153_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_dec(v___x_4153_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4152_);
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4152_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
v_a_4162_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4153_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4153_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
else
{
lean_dec(v___y_4148_);
lean_dec_ref(v_c_4129_);
lean_dec(v_x_4128_);
lean_dec(v_a_4127_);
return v___x_4151_;
}
}
else
{
lean_dec(v___y_4148_);
lean_dec_ref(v_c_4129_);
lean_dec(v_x_4128_);
lean_dec(v_a_4127_);
return v___x_4150_;
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_dec_ref(v_c_4129_);
lean_dec(v_x_4128_);
lean_dec(v_a_4127_);
v_a_4174_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4142_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4142_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4182_, lean_object* v_x_4183_, lean_object* v_c_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4182_, v_x_4183_, v_c_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec(v_a_4185_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_p_4215_; 
v_p_4215_ = lean_ctor_get(v_c_4198_, 0);
if (lean_obj_tag(v_p_4215_) == 1)
{
lean_object* v_k_4216_; lean_object* v_v_4217_; lean_object* v_p_4218_; lean_object* v_y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v_k_4216_ = lean_ctor_get(v_p_4215_, 0);
v_v_4217_ = lean_ctor_get(v_p_4215_, 1);
v_p_4218_ = lean_ctor_get(v_p_4215_, 2);
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4271_ = lean_int_dec_eq(v_k_4216_, v___x_4270_);
if (v___x_4271_ == 0)
{
uint8_t v___x_4272_; 
v___x_4272_ = lean_int_dec_eq(v_k_4216_, v___x_4269_);
if (v___x_4272_ == 0)
{
goto v___jp_4211_;
}
else
{
if (lean_obj_tag(v_p_4218_) == 1)
{
lean_object* v_k_4273_; lean_object* v_v_4274_; lean_object* v_p_4275_; uint8_t v___x_4276_; 
v_k_4273_ = lean_ctor_get(v_p_4218_, 0);
v_v_4274_ = lean_ctor_get(v_p_4218_, 1);
v_p_4275_ = lean_ctor_get(v_p_4218_, 2);
v___x_4276_ = lean_int_dec_eq(v_k_4273_, v___x_4270_);
if (v___x_4276_ == 0)
{
goto v___jp_4211_;
}
else
{
if (lean_obj_tag(v_p_4275_) == 0)
{
v_y_4220_ = v_v_4274_;
v___y_4221_ = v_a_4199_;
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
goto v___jp_4219_;
}
else
{
goto v___jp_4211_;
}
}
}
else
{
goto v___jp_4211_;
}
}
}
else
{
if (lean_obj_tag(v_p_4218_) == 1)
{
lean_object* v_k_4277_; lean_object* v_v_4278_; lean_object* v_p_4279_; uint8_t v___x_4280_; 
v_k_4277_ = lean_ctor_get(v_p_4218_, 0);
v_v_4278_ = lean_ctor_get(v_p_4218_, 1);
v_p_4279_ = lean_ctor_get(v_p_4218_, 2);
v___x_4280_ = lean_int_dec_eq(v_k_4277_, v___x_4269_);
if (v___x_4280_ == 0)
{
goto v___jp_4211_;
}
else
{
if (lean_obj_tag(v_p_4279_) == 0)
{
v_y_4220_ = v_v_4278_;
v___y_4221_ = v_a_4199_;
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
goto v___jp_4219_;
}
else
{
goto v___jp_4211_;
}
}
}
else
{
goto v___jp_4211_;
}
}
v___jp_4219_:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4217_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4232_, 1);
v___x_4234_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v___x_4236_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4233_, v_a_4235_, v___y_4222_);
lean_dec(v_a_4235_);
lean_dec(v_a_4233_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4252_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4252_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4252_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
uint8_t v___x_4241_; 
v___x_4241_ = lean_unbox(v_a_4237_);
lean_dec(v_a_4237_);
if (v___x_4241_ == 0)
{
uint8_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4242_ = 1;
v___x_4243_ = lean_box(v___x_4242_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4243_);
v___x_4245_ = v___x_4239_;
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
else
{
uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4247_ = 0;
v___x_4248_ = lean_box(v___x_4247_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4248_);
v___x_4250_ = v___x_4239_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
return v___x_4236_;
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v_a_4233_);
v_a_4253_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4234_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4234_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
v_a_4261_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4232_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4232_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
else
{
goto v___jp_4211_;
}
v___jp_4211_:
{
uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = 0;
v___x_4213_ = lean_box(v___x_4212_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_c_4281_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4295_){
_start:
{
lean_object* v_p_4297_; 
v_p_4297_ = lean_ctor_get(v_c_4295_, 0);
if (lean_obj_tag(v_p_4297_) == 1)
{
lean_object* v_k_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v_k_4298_ = lean_ctor_get(v_p_4297_, 0);
v___x_4299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4300_ = lean_int_dec_lt(v_k_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_c_4295_);
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4302_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4297_);
v___x_4303_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4297_, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_c_4295_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
else
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_c_4295_);
return v___x_4307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4308_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4311_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec(v_a_4326_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4339_, lean_object* v_snd_4340_, lean_object* v_fst_4341_, lean_object* v_s_4342_){
_start:
{
lean_object* v_structs_4343_; lean_object* v_typeIdOf_4344_; lean_object* v_exprToStructId_4345_; lean_object* v_exprToStructIdEntries_4346_; lean_object* v_forbiddenNatModules_4347_; lean_object* v_natStructs_4348_; lean_object* v_natTypeIdOf_4349_; lean_object* v_exprToNatStructId_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_structs_4343_ = lean_ctor_get(v_s_4342_, 0);
v_typeIdOf_4344_ = lean_ctor_get(v_s_4342_, 1);
v_exprToStructId_4345_ = lean_ctor_get(v_s_4342_, 2);
v_exprToStructIdEntries_4346_ = lean_ctor_get(v_s_4342_, 3);
v_forbiddenNatModules_4347_ = lean_ctor_get(v_s_4342_, 4);
v_natStructs_4348_ = lean_ctor_get(v_s_4342_, 5);
v_natTypeIdOf_4349_ = lean_ctor_get(v_s_4342_, 6);
v_exprToNatStructId_4350_ = lean_ctor_get(v_s_4342_, 7);
v___x_4351_ = lean_array_get_size(v_structs_4343_);
v___x_4352_ = lean_nat_dec_lt(v___y_4339_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_dec(v_fst_4341_);
lean_dec_ref(v_snd_4340_);
return v_s_4342_;
}
else
{
lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4416_; 
lean_inc_ref(v_exprToNatStructId_4350_);
lean_inc_ref(v_natTypeIdOf_4349_);
lean_inc_ref(v_natStructs_4348_);
lean_inc_ref(v_forbiddenNatModules_4347_);
lean_inc_ref(v_exprToStructIdEntries_4346_);
lean_inc_ref(v_exprToStructId_4345_);
lean_inc_ref(v_typeIdOf_4344_);
lean_inc_ref(v_structs_4343_);
v_isSharedCheck_4416_ = !lean_is_exclusive(v_s_4342_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; lean_object* v_unused_4418_; lean_object* v_unused_4419_; lean_object* v_unused_4420_; lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; lean_object* v_unused_4424_; 
v_unused_4417_ = lean_ctor_get(v_s_4342_, 7);
lean_dec(v_unused_4417_);
v_unused_4418_ = lean_ctor_get(v_s_4342_, 6);
lean_dec(v_unused_4418_);
v_unused_4419_ = lean_ctor_get(v_s_4342_, 5);
lean_dec(v_unused_4419_);
v_unused_4420_ = lean_ctor_get(v_s_4342_, 4);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_s_4342_, 3);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_s_4342_, 2);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_s_4342_, 1);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_s_4342_, 0);
lean_dec(v_unused_4424_);
v___x_4354_ = v_s_4342_;
v_isShared_4355_ = v_isSharedCheck_4416_;
goto v_resetjp_4353_;
}
else
{
lean_dec(v_s_4342_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4416_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v_v_4356_; lean_object* v_id_4357_; lean_object* v_ringId_x3f_4358_; lean_object* v_type_4359_; lean_object* v_u_4360_; lean_object* v_intModuleInst_4361_; lean_object* v_leInst_x3f_4362_; lean_object* v_ltInst_x3f_4363_; lean_object* v_lawfulOrderLTInst_x3f_4364_; lean_object* v_isPreorderInst_x3f_4365_; lean_object* v_orderedAddInst_x3f_4366_; lean_object* v_isLinearInst_x3f_4367_; lean_object* v_noNatDivInst_x3f_4368_; lean_object* v_ringInst_x3f_4369_; lean_object* v_commRingInst_x3f_4370_; lean_object* v_orderedRingInst_x3f_4371_; lean_object* v_fieldInst_x3f_4372_; lean_object* v_charInst_x3f_4373_; lean_object* v_zero_4374_; lean_object* v_ofNatZero_4375_; lean_object* v_one_x3f_4376_; lean_object* v_leFn_x3f_4377_; lean_object* v_ltFn_x3f_4378_; lean_object* v_addFn_4379_; lean_object* v_zsmulFn_4380_; lean_object* v_nsmulFn_4381_; lean_object* v_zsmulFn_x3f_4382_; lean_object* v_nsmulFn_x3f_4383_; lean_object* v_homomulFn_x3f_4384_; lean_object* v_subFn_4385_; lean_object* v_negFn_4386_; lean_object* v_vars_4387_; lean_object* v_varMap_4388_; lean_object* v_lowers_4389_; lean_object* v_uppers_4390_; lean_object* v_diseqs_4391_; lean_object* v_assignment_4392_; uint8_t v_caseSplits_4393_; lean_object* v_conflict_x3f_4394_; lean_object* v_diseqSplits_4395_; lean_object* v_elimEqs_4396_; lean_object* v_elimStack_4397_; lean_object* v_occurs_4398_; lean_object* v_ignored_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4415_; 
v_v_4356_ = lean_array_fget(v_structs_4343_, v___y_4339_);
v_id_4357_ = lean_ctor_get(v_v_4356_, 0);
v_ringId_x3f_4358_ = lean_ctor_get(v_v_4356_, 1);
v_type_4359_ = lean_ctor_get(v_v_4356_, 2);
v_u_4360_ = lean_ctor_get(v_v_4356_, 3);
v_intModuleInst_4361_ = lean_ctor_get(v_v_4356_, 4);
v_leInst_x3f_4362_ = lean_ctor_get(v_v_4356_, 5);
v_ltInst_x3f_4363_ = lean_ctor_get(v_v_4356_, 6);
v_lawfulOrderLTInst_x3f_4364_ = lean_ctor_get(v_v_4356_, 7);
v_isPreorderInst_x3f_4365_ = lean_ctor_get(v_v_4356_, 8);
v_orderedAddInst_x3f_4366_ = lean_ctor_get(v_v_4356_, 9);
v_isLinearInst_x3f_4367_ = lean_ctor_get(v_v_4356_, 10);
v_noNatDivInst_x3f_4368_ = lean_ctor_get(v_v_4356_, 11);
v_ringInst_x3f_4369_ = lean_ctor_get(v_v_4356_, 12);
v_commRingInst_x3f_4370_ = lean_ctor_get(v_v_4356_, 13);
v_orderedRingInst_x3f_4371_ = lean_ctor_get(v_v_4356_, 14);
v_fieldInst_x3f_4372_ = lean_ctor_get(v_v_4356_, 15);
v_charInst_x3f_4373_ = lean_ctor_get(v_v_4356_, 16);
v_zero_4374_ = lean_ctor_get(v_v_4356_, 17);
v_ofNatZero_4375_ = lean_ctor_get(v_v_4356_, 18);
v_one_x3f_4376_ = lean_ctor_get(v_v_4356_, 19);
v_leFn_x3f_4377_ = lean_ctor_get(v_v_4356_, 20);
v_ltFn_x3f_4378_ = lean_ctor_get(v_v_4356_, 21);
v_addFn_4379_ = lean_ctor_get(v_v_4356_, 22);
v_zsmulFn_4380_ = lean_ctor_get(v_v_4356_, 23);
v_nsmulFn_4381_ = lean_ctor_get(v_v_4356_, 24);
v_zsmulFn_x3f_4382_ = lean_ctor_get(v_v_4356_, 25);
v_nsmulFn_x3f_4383_ = lean_ctor_get(v_v_4356_, 26);
v_homomulFn_x3f_4384_ = lean_ctor_get(v_v_4356_, 27);
v_subFn_4385_ = lean_ctor_get(v_v_4356_, 28);
v_negFn_4386_ = lean_ctor_get(v_v_4356_, 29);
v_vars_4387_ = lean_ctor_get(v_v_4356_, 30);
v_varMap_4388_ = lean_ctor_get(v_v_4356_, 31);
v_lowers_4389_ = lean_ctor_get(v_v_4356_, 32);
v_uppers_4390_ = lean_ctor_get(v_v_4356_, 33);
v_diseqs_4391_ = lean_ctor_get(v_v_4356_, 34);
v_assignment_4392_ = lean_ctor_get(v_v_4356_, 35);
v_caseSplits_4393_ = lean_ctor_get_uint8(v_v_4356_, sizeof(void*)*42);
v_conflict_x3f_4394_ = lean_ctor_get(v_v_4356_, 36);
v_diseqSplits_4395_ = lean_ctor_get(v_v_4356_, 37);
v_elimEqs_4396_ = lean_ctor_get(v_v_4356_, 38);
v_elimStack_4397_ = lean_ctor_get(v_v_4356_, 39);
v_occurs_4398_ = lean_ctor_get(v_v_4356_, 40);
v_ignored_4399_ = lean_ctor_get(v_v_4356_, 41);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_v_4356_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4401_ = v_v_4356_;
v_isShared_4402_ = v_isSharedCheck_4415_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_ignored_4399_);
lean_inc(v_occurs_4398_);
lean_inc(v_elimStack_4397_);
lean_inc(v_elimEqs_4396_);
lean_inc(v_diseqSplits_4395_);
lean_inc(v_conflict_x3f_4394_);
lean_inc(v_assignment_4392_);
lean_inc(v_diseqs_4391_);
lean_inc(v_uppers_4390_);
lean_inc(v_lowers_4389_);
lean_inc(v_varMap_4388_);
lean_inc(v_vars_4387_);
lean_inc(v_negFn_4386_);
lean_inc(v_subFn_4385_);
lean_inc(v_homomulFn_x3f_4384_);
lean_inc(v_nsmulFn_x3f_4383_);
lean_inc(v_zsmulFn_x3f_4382_);
lean_inc(v_nsmulFn_4381_);
lean_inc(v_zsmulFn_4380_);
lean_inc(v_addFn_4379_);
lean_inc(v_ltFn_x3f_4378_);
lean_inc(v_leFn_x3f_4377_);
lean_inc(v_one_x3f_4376_);
lean_inc(v_ofNatZero_4375_);
lean_inc(v_zero_4374_);
lean_inc(v_charInst_x3f_4373_);
lean_inc(v_fieldInst_x3f_4372_);
lean_inc(v_orderedRingInst_x3f_4371_);
lean_inc(v_commRingInst_x3f_4370_);
lean_inc(v_ringInst_x3f_4369_);
lean_inc(v_noNatDivInst_x3f_4368_);
lean_inc(v_isLinearInst_x3f_4367_);
lean_inc(v_orderedAddInst_x3f_4366_);
lean_inc(v_isPreorderInst_x3f_4365_);
lean_inc(v_lawfulOrderLTInst_x3f_4364_);
lean_inc(v_ltInst_x3f_4363_);
lean_inc(v_leInst_x3f_4362_);
lean_inc(v_intModuleInst_4361_);
lean_inc(v_u_4360_);
lean_inc(v_type_4359_);
lean_inc(v_ringId_x3f_4358_);
lean_inc(v_id_4357_);
lean_dec(v_v_4356_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4415_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v_xs_x27_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4403_ = lean_box(0);
v_xs_x27_4404_ = lean_array_fset(v_structs_4343_, v___y_4339_, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v_snd_4340_);
v___x_4406_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4396_, v_fst_4341_, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_fst_4341_);
lean_ctor_set(v___x_4407_, 1, v_elimStack_4397_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 39, v___x_4407_);
lean_ctor_set(v___x_4401_, 38, v___x_4406_);
v___x_4409_ = v___x_4401_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_id_4357_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_ringId_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4414_, 2, v_type_4359_);
lean_ctor_set(v_reuseFailAlloc_4414_, 3, v_u_4360_);
lean_ctor_set(v_reuseFailAlloc_4414_, 4, v_intModuleInst_4361_);
lean_ctor_set(v_reuseFailAlloc_4414_, 5, v_leInst_x3f_4362_);
lean_ctor_set(v_reuseFailAlloc_4414_, 6, v_ltInst_x3f_4363_);
lean_ctor_set(v_reuseFailAlloc_4414_, 7, v_lawfulOrderLTInst_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4414_, 8, v_isPreorderInst_x3f_4365_);
lean_ctor_set(v_reuseFailAlloc_4414_, 9, v_orderedAddInst_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4414_, 10, v_isLinearInst_x3f_4367_);
lean_ctor_set(v_reuseFailAlloc_4414_, 11, v_noNatDivInst_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4414_, 12, v_ringInst_x3f_4369_);
lean_ctor_set(v_reuseFailAlloc_4414_, 13, v_commRingInst_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4414_, 14, v_orderedRingInst_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4414_, 15, v_fieldInst_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4414_, 16, v_charInst_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4414_, 17, v_zero_4374_);
lean_ctor_set(v_reuseFailAlloc_4414_, 18, v_ofNatZero_4375_);
lean_ctor_set(v_reuseFailAlloc_4414_, 19, v_one_x3f_4376_);
lean_ctor_set(v_reuseFailAlloc_4414_, 20, v_leFn_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4414_, 21, v_ltFn_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4414_, 22, v_addFn_4379_);
lean_ctor_set(v_reuseFailAlloc_4414_, 23, v_zsmulFn_4380_);
lean_ctor_set(v_reuseFailAlloc_4414_, 24, v_nsmulFn_4381_);
lean_ctor_set(v_reuseFailAlloc_4414_, 25, v_zsmulFn_x3f_4382_);
lean_ctor_set(v_reuseFailAlloc_4414_, 26, v_nsmulFn_x3f_4383_);
lean_ctor_set(v_reuseFailAlloc_4414_, 27, v_homomulFn_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4414_, 28, v_subFn_4385_);
lean_ctor_set(v_reuseFailAlloc_4414_, 29, v_negFn_4386_);
lean_ctor_set(v_reuseFailAlloc_4414_, 30, v_vars_4387_);
lean_ctor_set(v_reuseFailAlloc_4414_, 31, v_varMap_4388_);
lean_ctor_set(v_reuseFailAlloc_4414_, 32, v_lowers_4389_);
lean_ctor_set(v_reuseFailAlloc_4414_, 33, v_uppers_4390_);
lean_ctor_set(v_reuseFailAlloc_4414_, 34, v_diseqs_4391_);
lean_ctor_set(v_reuseFailAlloc_4414_, 35, v_assignment_4392_);
lean_ctor_set(v_reuseFailAlloc_4414_, 36, v_conflict_x3f_4394_);
lean_ctor_set(v_reuseFailAlloc_4414_, 37, v_diseqSplits_4395_);
lean_ctor_set(v_reuseFailAlloc_4414_, 38, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4414_, 39, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4414_, 40, v_occurs_4398_);
lean_ctor_set(v_reuseFailAlloc_4414_, 41, v_ignored_4399_);
lean_ctor_set_uint8(v_reuseFailAlloc_4414_, sizeof(void*)*42, v_caseSplits_4393_);
v___x_4409_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4412_; 
v___x_4410_ = lean_array_fset(v_xs_x27_4404_, v___y_4339_, v___x_4409_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4410_);
v___x_4412_ = v___x_4354_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_typeIdOf_4344_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_exprToStructId_4345_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v_exprToStructIdEntries_4346_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_forbiddenNatModules_4347_);
lean_ctor_set(v_reuseFailAlloc_4413_, 5, v_natStructs_4348_);
lean_ctor_set(v_reuseFailAlloc_4413_, 6, v_natTypeIdOf_4349_);
lean_ctor_set(v_reuseFailAlloc_4413_, 7, v_exprToNatStructId_4350_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4425_, lean_object* v_snd_4426_, lean_object* v_fst_4427_, lean_object* v_s_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4425_, v_snd_4426_, v_fst_4427_, v_s_4428_);
lean_dec(v___y_4425_);
return v_res_4429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4432_ = l_Lean_stringToMessageData(v___x_4431_);
return v___x_4432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4440_ = l_Lean_Name_append(v___x_4439_, v___x_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v_options_4520_; lean_object* v_toCold_4521_; uint8_t v_hasTrace_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v_inheritedTraceOptions_4539_; lean_object* v_options_4540_; lean_object* v___y_4541_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; 
v_options_4520_ = lean_ctor_get(v_a_4451_, 1);
v_toCold_4521_ = lean_ctor_get(v_a_4451_, 0);
v_hasTrace_4522_ = lean_ctor_get_uint8(v_options_4520_, sizeof(void*)*1);
if (v_hasTrace_4522_ == 0)
{
v___y_4558_ = v_a_4442_;
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
goto v___jp_4557_;
}
else
{
lean_object* v_inheritedTraceOptions_4666_; lean_object* v_cls_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v_inheritedTraceOptions_4666_ = lean_ctor_get(v_toCold_4521_, 4);
v_cls_4667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4666_, v_options_4520_, v___x_4668_);
if (v___x_4669_ == 0)
{
v___y_4558_ = v_a_4442_;
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
goto v___jp_4557_;
}
else
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = l_Lean_MessageData_ofExpr(v_a_4671_);
v___x_4673_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4667_, v___x_4672_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_dec_ref_known(v___x_4673_, 1);
v___y_4558_ = v_a_4442_;
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
goto v___jp_4557_;
}
else
{
lean_dec_ref(v_c_4441_);
return v___x_4673_;
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec_ref(v_c_4441_);
v_a_4674_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4670_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4670_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
v___jp_4454_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4455_ = lean_box(0);
v___x_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
return v___x_4456_;
}
v___jp_4457_:
{
lean_object* v___f_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_inc(v___y_4463_);
v___f_4474_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4474_, 0, v___y_4463_);
lean_closure_set(v___f_4474_, 1, v___y_4459_);
lean_closure_set(v___f_4474_, 2, v___y_4458_);
v___x_4475_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4476_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4475_, v___f_4474_, v___y_4464_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v___x_4477_; 
lean_dec_ref_known(v___x_4476_, 1);
v___x_4477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4461_, v___y_4460_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4477_;
}
else
{
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec(v___y_4460_);
return v___x_4476_;
}
}
v___jp_4478_:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; uint8_t v_caseSplits_4497_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v_caseSplits_4497_ = lean_ctor_get_uint8(v_a_4496_, sizeof(void*)*42);
lean_dec(v_a_4496_);
if (v_caseSplits_4497_ == 0)
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; uint8_t v___x_4500_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = lean_unbox(v_a_4499_);
lean_dec(v_a_4499_);
if (v___x_4500_ == 0)
{
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4501_; lean_object* v_a_4502_; lean_object* v___x_4503_; 
lean_inc_ref(v___y_4483_);
v___x_4501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4483_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4501_);
v___x_4503_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4502_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_dec_ref_known(v___x_4503_, 1);
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
goto v___jp_4457_;
}
else
{
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
return v___x_4503_;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
v_a_4504_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4498_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4498_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
goto v___jp_4457_;
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
v_a_4512_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4495_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4495_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
v___jp_4523_:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4544_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4539_, v_options_4540_, v___x_4543_);
if (v___x_4544_ == 0)
{
v___y_4479_ = v___y_4524_;
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
v___y_4494_ = v___y_4541_;
goto v___jp_4478_;
}
else
{
lean_object* v___x_4545_; 
v___x_4545_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4541_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v___x_4547_ = l_Lean_MessageData_ofExpr(v_a_4546_);
v___x_4548_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4542_, v___x_4547_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4541_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref_known(v___x_4548_, 1);
v___y_4479_ = v___y_4524_;
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
v___y_4494_ = v___y_4541_;
goto v___jp_4478_;
}
else
{
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
return v___x_4548_;
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
v_a_4549_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4545_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4545_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
v___jp_4557_:
{
lean_object* v___x_4569_; 
lean_inc_ref(v___y_4567_);
v___x_4569_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4441_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v_p_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v___x_4569_, 1);
v_p_4571_ = lean_ctor_get(v_a_4570_, 0);
v___x_4572_ = lean_box(0);
v___x_4573_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4571_, v___x_4572_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; 
v___x_4574_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4570_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_snd_4576_; lean_object* v_options_4577_; uint8_t v_hasTrace_4578_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
v_snd_4576_ = lean_ctor_get(v_a_4575_, 1);
lean_inc(v_snd_4576_);
v_options_4577_ = lean_ctor_get(v___y_4567_, 1);
v_hasTrace_4578_ = lean_ctor_get_uint8(v_options_4577_, sizeof(void*)*1);
if (v_hasTrace_4578_ == 0)
{
lean_object* v_fst_4579_; lean_object* v_fst_4580_; lean_object* v_snd_4581_; 
v_fst_4579_ = lean_ctor_get(v_a_4575_, 0);
lean_inc(v_fst_4579_);
lean_dec(v_a_4575_);
v_fst_4580_ = lean_ctor_get(v_snd_4576_, 0);
lean_inc_n(v_fst_4580_, 2);
v_snd_4581_ = lean_ctor_get(v_snd_4576_, 1);
lean_inc_n(v_snd_4581_, 2);
lean_dec(v_snd_4576_);
v___y_4479_ = v_fst_4580_;
v___y_4480_ = v_snd_4581_;
v___y_4481_ = v_fst_4580_;
v___y_4482_ = v_fst_4579_;
v___y_4483_ = v_snd_4581_;
v___y_4484_ = v___y_4558_;
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
goto v___jp_4478_;
}
else
{
lean_object* v_toCold_4582_; lean_object* v_fst_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4629_; 
v_toCold_4582_ = lean_ctor_get(v___y_4567_, 0);
v_fst_4583_ = lean_ctor_get(v_a_4575_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_a_4575_);
if (v_isSharedCheck_4629_ == 0)
{
lean_object* v_unused_4630_; 
v_unused_4630_ = lean_ctor_get(v_a_4575_, 1);
lean_dec(v_unused_4630_);
v___x_4585_ = v_a_4575_;
v_isShared_4586_ = v_isSharedCheck_4629_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_fst_4583_);
lean_dec(v_a_4575_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4629_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v_fst_4587_; lean_object* v_snd_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4628_; 
v_fst_4587_ = lean_ctor_get(v_snd_4576_, 0);
v_snd_4588_ = lean_ctor_get(v_snd_4576_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_snd_4576_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4590_ = v_snd_4576_;
v_isShared_4591_ = v_isSharedCheck_4628_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_snd_4588_);
lean_inc(v_fst_4587_);
lean_dec(v_snd_4576_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4628_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_inheritedTraceOptions_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; 
v_inheritedTraceOptions_4592_ = lean_ctor_get(v_toCold_4582_, 4);
v___x_4593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4592_, v_options_4577_, v___x_4594_);
if (v___x_4595_ == 0)
{
lean_del_object(v___x_4590_);
lean_del_object(v___x_4585_);
lean_inc(v_snd_4588_);
lean_inc(v_fst_4587_);
v___y_4524_ = v_fst_4587_;
v___y_4525_ = v_snd_4588_;
v___y_4526_ = v_fst_4587_;
v___y_4527_ = v_fst_4583_;
v___y_4528_ = v_snd_4588_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v_inheritedTraceOptions_4539_ = v_inheritedTraceOptions_4592_;
v_options_4540_ = v_options_4577_;
v___y_4541_ = v___y_4568_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4587_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v___x_4598_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4588_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
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
v___x_4609_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4593_, v___x_4608_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_dec_ref_known(v___x_4609_, 1);
lean_inc(v_snd_4588_);
lean_inc(v_fst_4587_);
v___y_4524_ = v_fst_4587_;
v___y_4525_ = v_snd_4588_;
v___y_4526_ = v_fst_4587_;
v___y_4527_ = v_fst_4583_;
v___y_4528_ = v_snd_4588_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v_inheritedTraceOptions_4539_ = v_inheritedTraceOptions_4592_;
v_options_4540_ = v_options_4577_;
v___y_4541_ = v___y_4568_;
goto v___jp_4523_;
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
v_a_4631_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4574_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4574_);
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
v_options_4639_ = lean_ctor_get(v___y_4567_, 1);
v_hasTrace_4640_ = lean_ctor_get_uint8(v_options_4639_, sizeof(void*)*1);
if (v_hasTrace_4640_ == 0)
{
lean_dec(v_a_4570_);
goto v___jp_4454_;
}
else
{
lean_object* v_toCold_4641_; lean_object* v_inheritedTraceOptions_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_toCold_4641_ = lean_ctor_get(v___y_4567_, 0);
v_inheritedTraceOptions_4642_ = lean_ctor_get(v_toCold_4641_, 4);
v___x_4643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4642_, v_options_4639_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_dec(v_a_4570_);
goto v___jp_4454_;
}
else
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4570_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v_a_4570_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v___x_4648_ = l_Lean_MessageData_ofExpr(v_a_4647_);
v___x_4649_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4643_, v___x_4648_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_dec_ref_known(v___x_4649_, 1);
goto v___jp_4454_;
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
v_a_4658_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4569_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4569_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec(v_a_4683_);
return v_res_4695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v_cls_4700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4702_ = l_Lean_Name_append(v___x_4701_, v_cls_4700_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4703_, lean_object* v_b_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_options_4713_; uint8_t v_hasTrace_4714_; 
v_options_4713_ = lean_ctor_get(v_a_4707_, 1);
v_hasTrace_4714_ = lean_ctor_get_uint8(v_options_4713_, sizeof(void*)*1);
if (v_hasTrace_4714_ == 0)
{
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
goto v___jp_4710_;
}
else
{
lean_object* v_toCold_4715_; lean_object* v_inheritedTraceOptions_4716_; lean_object* v_cls_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; 
v_toCold_4715_ = lean_ctor_get(v_a_4707_, 0);
v_inheritedTraceOptions_4716_ = lean_ctor_get(v_toCold_4715_, 4);
v_cls_4717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4716_, v_options_4713_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
goto v___jp_4710_;
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4720_ = l_Lean_MessageData_ofExpr(v_a_4703_);
v___x_4721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = l_Lean_MessageData_ofExpr(v_b_4704_);
v___x_4724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4717_, v___x_4724_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4725_;
}
}
v___jp_4710_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4726_, lean_object* v_b_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4726_, v_b_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4734_, lean_object* v_b_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4734_, v_b_4735_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4749_, lean_object* v_b_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4749_, v_b_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec(v_a_4751_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4764_, lean_object* v_b_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4764_, v_a_4767_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref_known(v___x_4778_, 1);
v___x_4780_ = 0;
lean_inc_ref(v_a_4764_);
v___x_4781_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4764_, v___x_4780_, v_a_4779_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4831_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4784_ = v___x_4781_;
v_isShared_4785_ = v_isSharedCheck_4831_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4781_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4831_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
if (lean_obj_tag(v_a_4782_) == 1)
{
lean_object* v_val_4786_; lean_object* v___x_4787_; 
lean_del_object(v___x_4784_);
v_val_4786_ = lean_ctor_get(v_a_4782_, 0);
lean_inc(v_val_4786_);
lean_dec_ref_known(v_a_4782_, 1);
v___x_4787_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4765_, v_a_4767_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4789_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
lean_inc_ref(v_b_4765_);
v___x_4789_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4765_, v___x_4780_, v_a_4788_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4810_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4810_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4810_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
if (lean_obj_tag(v_a_4790_) == 1)
{
lean_object* v_val_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v_val_4794_ = lean_ctor_get(v_a_4790_, 0);
lean_inc_n(v_val_4794_, 2);
lean_dec_ref_known(v_a_4790_, 1);
lean_inc(v_val_4786_);
v___x_4795_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4795_, 0, v_val_4786_);
lean_ctor_set(v___x_4795_, 1, v_val_4794_);
v___x_4796_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4795_);
v___x_4797_ = lean_box(0);
v___x_4798_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4796_, v___x_4797_);
if (v___x_4798_ == 0)
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
lean_del_object(v___x_4792_);
v___x_4799_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4799_, 0, v_a_4764_);
lean_ctor_set(v___x_4799_, 1, v_b_4765_);
lean_ctor_set(v___x_4799_, 2, v_val_4786_);
lean_ctor_set(v___x_4799_, 3, v_val_4794_);
v___x_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4796_);
lean_ctor_set(v___x_4800_, 1, v___x_4799_);
v___x_4801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4800_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
return v___x_4801_;
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v___x_4796_);
lean_dec(v_val_4794_);
lean_dec(v_val_4786_);
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v___x_4802_ = lean_box(0);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4802_);
v___x_4804_ = v___x_4792_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_dec(v_a_4790_);
lean_dec(v_val_4786_);
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v___x_4806_ = lean_box(0);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4806_);
v___x_4808_ = v___x_4792_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec(v_val_4786_);
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v_a_4811_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4789_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4789_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
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
lean_dec(v_val_4786_);
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v_a_4819_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4787_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4787_);
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
lean_object* v___x_4827_; lean_object* v___x_4829_; 
lean_dec(v_a_4782_);
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v___x_4827_ = lean_box(0);
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v___x_4827_);
v___x_4829_ = v___x_4784_;
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
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v_a_4832_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4781_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4781_);
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
lean_dec_ref(v_b_4765_);
lean_dec_ref(v_a_4764_);
v_a_4840_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4778_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4778_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4848_, lean_object* v_b_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4848_, v_b_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec(v_a_4850_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4863_, lean_object* v_b_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4879_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
lean_inc_ref(v_a_4863_);
v___x_4879_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4863_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v_fst_4881_; lean_object* v___x_4882_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4879_, 1);
v_fst_4881_ = lean_ctor_get(v_a_4880_, 0);
lean_inc(v_fst_4881_);
lean_dec(v_a_4880_);
lean_inc_ref(v_b_4864_);
v___x_4882_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v_fst_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4967_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v___x_4882_, 1);
v_fst_4884_ = lean_ctor_get(v_a_4883_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v_a_4883_);
if (v_isSharedCheck_4967_ == 0)
{
lean_object* v_unused_4968_; 
v_unused_4968_ = lean_ctor_get(v_a_4883_, 1);
lean_dec(v_unused_4968_);
v___x_4886_ = v_a_4883_;
v_isShared_4887_ = v_isSharedCheck_4967_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_fst_4884_);
lean_dec(v_a_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4967_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4863_, v_a_4866_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v_id_4890_; lean_object* v_structId_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v_id_4890_ = lean_ctor_get(v_a_4878_, 0);
lean_inc(v_id_4890_);
v_structId_4891_ = lean_ctor_get(v_a_4878_, 1);
lean_inc(v_structId_4891_);
lean_dec(v_a_4878_);
v___x_4892_ = 0;
v___x_4893_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4881_, v___x_4892_, v_a_4889_, v_structId_4891_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4950_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4950_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4950_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
if (lean_obj_tag(v_a_4894_) == 1)
{
lean_object* v_val_4898_; lean_object* v___x_4899_; 
lean_del_object(v___x_4896_);
v_val_4898_ = lean_ctor_get(v_a_4894_, 0);
lean_inc(v_val_4898_);
lean_dec_ref_known(v_a_4894_, 1);
v___x_4899_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4864_, v_a_4866_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4901_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref_known(v___x_4899_, 1);
v___x_4901_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4884_, v___x_4892_, v_a_4900_, v_structId_4891_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4929_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4929_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4929_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
if (lean_obj_tag(v_a_4902_) == 1)
{
lean_object* v_val_4906_; lean_object* v___x_4908_; 
v_val_4906_ = lean_ctor_get(v_a_4902_, 0);
lean_inc_n(v_val_4906_, 2);
lean_dec_ref_known(v_a_4902_, 1);
lean_inc(v_val_4898_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set_tag(v___x_4886_, 3);
lean_ctor_set(v___x_4886_, 1, v_val_4906_);
lean_ctor_set(v___x_4886_, 0, v_val_4898_);
v___x_4908_ = v___x_4886_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_val_4898_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v_val_4906_);
v___x_4908_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; uint8_t v___x_4911_; 
v___x_4909_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4908_);
v___x_4910_ = lean_box(0);
v___x_4911_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4909_, v___x_4910_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
lean_del_object(v___x_4904_);
lean_inc(v_val_4906_);
lean_inc(v_val_4898_);
lean_inc(v_id_4890_);
lean_inc_ref(v_b_4864_);
lean_inc_ref(v_a_4863_);
v___x_4912_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4912_, 0, v_a_4863_);
lean_ctor_set(v___x_4912_, 1, v_b_4864_);
lean_ctor_set(v___x_4912_, 2, v_id_4890_);
lean_ctor_set(v___x_4912_, 3, v_val_4898_);
lean_ctor_set(v___x_4912_, 4, v_val_4906_);
lean_inc(v___x_4909_);
v___x_4913_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4913_, 0, v___x_4909_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*2, v___x_4892_);
v___x_4914_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4913_, v_structId_4891_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
lean_dec_ref_known(v___x_4914_, 1);
v___x_4915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4916_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4909_, v___x_4915_);
v___x_4917_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4917_, 0, v_b_4864_);
lean_ctor_set(v___x_4917_, 1, v_a_4863_);
lean_ctor_set(v___x_4917_, 2, v_id_4890_);
lean_ctor_set(v___x_4917_, 3, v_val_4906_);
lean_ctor_set(v___x_4917_, 4, v_val_4898_);
v___x_4918_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4918_, 0, v___x_4916_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
lean_ctor_set_uint8(v___x_4918_, sizeof(void*)*2, v___x_4892_);
v___x_4919_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4918_, v_structId_4891_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec(v_structId_4891_);
return v___x_4919_;
}
else
{
lean_dec(v___x_4909_);
lean_dec(v_val_4906_);
lean_dec(v_val_4898_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
return v___x_4914_;
}
}
else
{
lean_object* v___x_4920_; lean_object* v___x_4922_; 
lean_dec(v___x_4909_);
lean_dec(v_val_4906_);
lean_dec(v_val_4898_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v___x_4920_ = lean_box(0);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4920_);
v___x_4922_ = v___x_4904_;
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
lean_object* v___x_4925_; lean_object* v___x_4927_; 
lean_dec(v_a_4902_);
lean_dec(v_val_4898_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_del_object(v___x_4886_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v___x_4925_ = lean_box(0);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4925_);
v___x_4927_ = v___x_4904_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec(v_val_4898_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_del_object(v___x_4886_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4930_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4901_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4901_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
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
lean_dec(v_val_4898_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_del_object(v___x_4886_);
lean_dec(v_fst_4884_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4938_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4899_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4899_);
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
lean_object* v___x_4946_; lean_object* v___x_4948_; 
lean_dec(v_a_4894_);
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_del_object(v___x_4886_);
lean_dec(v_fst_4884_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v___x_4946_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4946_);
v___x_4948_ = v___x_4896_;
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
lean_dec(v_structId_4891_);
lean_dec(v_id_4890_);
lean_del_object(v___x_4886_);
lean_dec(v_fst_4884_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4951_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v___x_4893_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4893_);
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
lean_del_object(v___x_4886_);
lean_dec(v_fst_4884_);
lean_dec(v_fst_4881_);
lean_dec(v_a_4878_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4959_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4888_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4888_);
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
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v_fst_4881_);
lean_dec(v_a_4878_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4969_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4882_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4882_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec(v_a_4878_);
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4977_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4879_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4879_);
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
lean_dec_ref(v_b_4864_);
lean_dec_ref(v_a_4863_);
v_a_4985_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4877_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4877_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4993_, lean_object* v_b_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4993_, v_b_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec(v_a_4995_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5008_, lean_object* v_b_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5024_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v___x_5022_, 1);
lean_inc_ref(v_a_5008_);
v___x_5024_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5008_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v_fst_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5122_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_5024_, 1);
v_fst_5026_ = lean_ctor_get(v_a_5025_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_a_5025_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; 
v_unused_5123_ = lean_ctor_get(v_a_5025_, 1);
lean_dec(v_unused_5123_);
v___x_5028_ = v_a_5025_;
v_isShared_5029_ = v_isSharedCheck_5122_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_fst_5026_);
lean_dec(v_a_5025_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5122_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5030_; 
lean_inc_ref(v_b_5009_);
v___x_5030_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v_fst_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5112_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v_fst_5032_ = lean_ctor_get(v_a_5031_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_a_5031_);
if (v_isSharedCheck_5112_ == 0)
{
lean_object* v_unused_5113_; 
v_unused_5113_ = lean_ctor_get(v_a_5031_, 1);
lean_dec(v_unused_5113_);
v___x_5034_ = v_a_5031_;
v_isShared_5035_ = v_isSharedCheck_5112_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_fst_5032_);
lean_dec(v_a_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5112_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; 
v___x_5036_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5008_, v_a_5011_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v_id_5038_; lean_object* v_structId_5039_; uint8_t v___x_5040_; lean_object* v___x_5041_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v_id_5038_ = lean_ctor_get(v_a_5023_, 0);
lean_inc(v_id_5038_);
v_structId_5039_ = lean_ctor_get(v_a_5023_, 1);
lean_inc(v_structId_5039_);
lean_dec(v_a_5023_);
v___x_5040_ = 0;
v___x_5041_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5026_, v___x_5040_, v_a_5037_, v_structId_5039_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5095_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5095_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5095_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
if (lean_obj_tag(v_a_5042_) == 1)
{
lean_object* v_val_5046_; lean_object* v___x_5047_; 
lean_del_object(v___x_5044_);
v_val_5046_ = lean_ctor_get(v_a_5042_, 0);
lean_inc(v_val_5046_);
lean_dec_ref_known(v_a_5042_, 1);
v___x_5047_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5009_, v_a_5011_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v___x_5049_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5032_, v___x_5040_, v_a_5048_, v_structId_5039_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5074_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5074_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5074_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
if (lean_obj_tag(v_a_5050_) == 1)
{
lean_object* v_val_5054_; lean_object* v___x_5056_; 
v_val_5054_ = lean_ctor_get(v_a_5050_, 0);
lean_inc_n(v_val_5054_, 2);
lean_dec_ref_known(v_a_5050_, 1);
lean_inc(v_val_5046_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set_tag(v___x_5034_, 3);
lean_ctor_set(v___x_5034_, 1, v_val_5054_);
lean_ctor_set(v___x_5034_, 0, v_val_5046_);
v___x_5056_ = v___x_5034_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_val_5046_);
lean_ctor_set(v_reuseFailAlloc_5069_, 1, v_val_5054_);
v___x_5056_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; uint8_t v___x_5059_; 
v___x_5057_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5056_);
v___x_5058_ = lean_box(0);
v___x_5059_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5057_, v___x_5058_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
lean_del_object(v___x_5052_);
v___x_5060_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5060_, 0, v_a_5008_);
lean_ctor_set(v___x_5060_, 1, v_b_5009_);
lean_ctor_set(v___x_5060_, 2, v_id_5038_);
lean_ctor_set(v___x_5060_, 3, v_val_5046_);
lean_ctor_set(v___x_5060_, 4, v_val_5054_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 1, v___x_5060_);
lean_ctor_set(v___x_5028_, 0, v___x_5057_);
v___x_5062_ = v___x_5028_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5063_; 
v___x_5063_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5062_, v_structId_5039_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
lean_dec(v_structId_5039_);
return v___x_5063_;
}
}
else
{
lean_object* v___x_5065_; lean_object* v___x_5067_; 
lean_dec(v___x_5057_);
lean_dec(v_val_5054_);
lean_dec(v_val_5046_);
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v___x_5065_ = lean_box(0);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5065_);
v___x_5067_ = v___x_5052_;
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
lean_object* v___x_5070_; lean_object* v___x_5072_; 
lean_dec(v_a_5050_);
lean_dec(v_val_5046_);
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5034_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v___x_5070_ = lean_box(0);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5070_);
v___x_5072_ = v___x_5052_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec(v_val_5046_);
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5034_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5075_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5049_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5049_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
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
lean_dec(v_val_5046_);
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5034_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5083_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5047_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5047_);
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
lean_object* v___x_5091_; lean_object* v___x_5093_; 
lean_dec(v_a_5042_);
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5034_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v___x_5091_ = lean_box(0);
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5091_);
v___x_5093_ = v___x_5044_;
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
lean_dec(v_structId_5039_);
lean_dec(v_id_5038_);
lean_del_object(v___x_5034_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5096_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5041_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5041_);
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
lean_del_object(v___x_5034_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_dec(v_fst_5026_);
lean_dec(v_a_5023_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5104_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5036_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5036_);
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
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_del_object(v___x_5028_);
lean_dec(v_fst_5026_);
lean_dec(v_a_5023_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5114_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5030_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5030_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
lean_dec(v_a_5023_);
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5124_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5024_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5024_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec_ref(v_b_5009_);
lean_dec_ref(v_a_5008_);
v_a_5132_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5022_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5022_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5140_, lean_object* v_b_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5140_, v_b_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec(v_a_5142_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5155_, lean_object* v_b_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
size_t v___x_5168_; size_t v___x_5169_; uint8_t v___x_5170_; 
v___x_5168_ = lean_ptr_addr(v_a_5155_);
v___x_5169_ = lean_ptr_addr(v_b_5156_);
v___x_5170_ = lean_usize_dec_eq(v___x_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
v___x_5171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5155_, v_b_5156_, v_a_5157_, v_a_5165_);
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
v___x_5174_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
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
v___x_5177_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
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
v___x_5180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5155_, v_b_5156_, v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_val_5173_);
return v___x_5180_;
}
else
{
lean_object* v___x_5181_; 
lean_dec(v_val_5173_);
v___x_5181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5155_, v_b_5156_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
return v___x_5181_;
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v_val_5173_);
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
v___x_5190_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
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
v___x_5193_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5155_, v_b_5156_, v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_val_5173_);
return v___x_5193_;
}
else
{
lean_object* v___x_5194_; 
v___x_5194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5155_, v_b_5156_, v_val_5173_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_val_5173_);
return v___x_5194_;
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_val_5173_);
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
v___x_5211_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5155_, v_b_5156_, v_a_5157_, v_a_5165_);
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
v___x_5217_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5216_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
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
v___x_5220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5155_, v_b_5156_, v_val_5216_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_val_5216_);
return v___x_5220_;
}
else
{
lean_object* v___x_5221_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5219_, 1);
v___x_5221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5155_, v_b_5156_, v_val_5216_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_val_5216_);
return v___x_5221_;
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_val_5216_);
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
lean_dec_ref(v_b_5156_);
lean_dec_ref(v_a_5155_);
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
