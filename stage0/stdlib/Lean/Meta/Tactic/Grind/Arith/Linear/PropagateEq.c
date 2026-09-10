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
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v___x_303_; lean_object* v_toCold_304_; lean_object* v_mctx_305_; lean_object* v_lctx_306_; lean_object* v_options_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v___x_303_ = lean_st_ref_get(v___y_297_);
v_toCold_304_ = lean_ctor_get(v___y_298_, 0);
v_mctx_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_mctx_305_);
lean_dec(v___x_303_);
v_lctx_306_ = lean_ctor_get(v___y_296_, 2);
v_options_307_ = lean_ctor_get(v_toCold_304_, 2);
lean_inc_ref(v_options_307_);
lean_inc_ref(v_lctx_306_);
v___x_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_308_, 0, v_env_302_);
lean_ctor_set(v___x_308_, 1, v_mctx_305_);
lean_ctor_set(v___x_308_, 2, v_lctx_306_);
lean_ctor_set(v___x_308_, 3, v_options_307_);
v___x_309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_msgData_295_);
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
v_ref_330_ = lean_ctor_get(v___y_327_, 2);
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
v___x_367_ = lean_st_ref_put(v___y_328_, v___x_366_);
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
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_540_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_540_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_540_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_540_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_535_; 
v_val_421_ = lean_ctor_get(v_a_417_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_535_ == 0)
{
v___x_423_ = v_a_417_;
v_isShared_424_ = v_isSharedCheck_535_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_a_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_535_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_snd_425_; lean_object* v_snd_426_; lean_object* v_toCold_427_; lean_object* v_options_428_; lean_object* v_fst_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_533_; 
v_snd_425_ = lean_ctor_get(v_val_421_, 1);
lean_inc(v_snd_425_);
v_snd_426_ = lean_ctor_get(v_snd_425_, 1);
lean_inc(v_snd_426_);
v_toCold_427_ = lean_ctor_get(v_a_413_, 0);
v_options_428_ = lean_ctor_get(v_toCold_427_, 2);
v_fst_429_ = lean_ctor_get(v_val_421_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_val_421_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_val_421_, 1);
lean_dec(v_unused_534_);
v___x_431_ = v_val_421_;
v_isShared_432_ = v_isSharedCheck_533_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_fst_429_);
lean_dec(v_val_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_533_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_531_; 
v_fst_433_ = lean_ctor_get(v_snd_425_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_snd_425_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_snd_425_, 1);
lean_dec(v_unused_532_);
v___x_435_ = v_snd_425_;
v_isShared_436_ = v_isSharedCheck_531_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_fst_433_);
lean_dec(v_snd_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_531_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_p_437_; lean_object* v_inheritedTraceOptions_438_; uint8_t v_hasTrace_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_p_437_ = lean_ctor_get(v_snd_426_, 0);
v_inheritedTraceOptions_438_ = lean_ctor_get(v_toCold_427_, 11);
v_hasTrace_439_ = lean_ctor_get_uint8(v_options_428_, sizeof(void*)*1);
v___x_440_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_437_, v_fst_433_);
lean_inc(v_p_403_);
v___x_441_ = l_Lean_Grind_Linarith_Poly_mul(v_p_403_, v___x_440_);
v___x_442_ = lean_int_neg(v_fst_429_);
lean_inc(v_p_437_);
v___x_443_ = l_Lean_Grind_Linarith_Poly_mul(v_p_437_, v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = l_Lean_Grind_Linarith_Poly_combine(v___x_441_, v___x_443_);
if (v_hasTrace_439_ == 0)
{
lean_dec(v___x_440_);
lean_dec(v_fst_429_);
lean_dec(v_p_403_);
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
lean_dec(v_p_403_);
goto v___jp_445_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_p_403_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_433_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_426_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_444_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
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
v___x_490_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_458_, v___x_489_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref_known(v___x_490_, 1);
goto v___jp_445_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___x_444_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
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
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
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
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
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
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
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
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
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
lean_ctor_set(v___x_435_, 0, v_snd_426_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_snd_426_);
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
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_449_);
v___x_451_ = v___x_423_;
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
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_451_);
v___x_453_ = v___x_419_;
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
lean_dec(v_a_417_);
lean_dec(v_p_403_);
v___x_536_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_536_);
v___x_538_ = v___x_419_;
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
lean_dec(v_p_403_);
v_a_541_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_416_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_416_);
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
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_ofNatZero_611_; lean_object* v___x_612_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
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
lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v_toCold_724_; lean_object* v_options_725_; uint8_t v_hasTrace_726_; 
v_toCold_724_ = lean_ctor_get(v_a_667_, 0);
v_options_725_ = lean_ctor_get(v_toCold_724_, 2);
v_hasTrace_726_ = lean_ctor_get_uint8(v_options_725_, sizeof(void*)*1);
if (v_hasTrace_726_ == 0)
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
lean_object* v_inheritedTraceOptions_727_; lean_object* v_cls_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_inheritedTraceOptions_727_ = lean_ctor_get(v_toCold_724_, 11);
v_cls_728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_727_, v_options_725_, v___x_729_);
if (v___x_730_ == 0)
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
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_654_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_655_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_MessageData_ofExpr(v_a_732_);
v___x_738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_MessageData_ofExpr(v_a_734_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
v___x_743_ = l_Lean_MessageData_ofExpr(v_a_736_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_728_, v___x_744_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec_ref_known(v___x_745_, 1);
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
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_734_);
lean_dec(v_a_732_);
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_754_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_735_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_735_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_732_);
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_762_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_733_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_733_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_770_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_731_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_731_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
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
lean_object* v_a_778_ = _args[0];
lean_object* v_x_779_ = _args[1];
lean_object* v_c_u2081_780_ = _args[2];
lean_object* v_b_781_ = _args[3];
lean_object* v_c_u2082_782_ = _args[4];
lean_object* v_a_783_ = _args[5];
lean_object* v_a_784_ = _args[6];
lean_object* v_a_785_ = _args[7];
lean_object* v_a_786_ = _args[8];
lean_object* v_a_787_ = _args[9];
lean_object* v_a_788_ = _args[10];
lean_object* v_a_789_ = _args[11];
lean_object* v_a_790_ = _args[12];
lean_object* v_a_791_ = _args[13];
lean_object* v_a_792_ = _args[14];
lean_object* v_a_793_ = _args[15];
lean_object* v_a_794_ = _args[16];
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_778_, v_x_779_, v_c_u2081_780_, v_b_781_, v_c_u2082_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_x_779_);
lean_dec(v_a_778_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_796_, lean_object* v_b_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_796_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_830_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_830_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
if (lean_obj_tag(v_a_802_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_807_; 
lean_del_object(v___x_804_);
v_val_806_ = lean_ctor_get(v_a_802_, 0);
v___x_807_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_825_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_825_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 1)
{
lean_object* v_val_812_; uint8_t v___x_813_; 
v_val_812_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_a_808_, 1);
v___x_813_ = lean_nat_dec_eq(v_val_806_, v_val_812_);
lean_dec(v_val_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec_ref_known(v_a_802_, 1);
v___x_814_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_814_);
v___x_816_ = v___x_810_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_819_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_a_802_);
v___x_819_ = v___x_810_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_802_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v_a_808_);
lean_dec_ref_known(v_a_802_, 1);
v___x_821_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_821_);
v___x_823_ = v___x_810_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_802_, 1);
return v___x_807_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_a_802_);
v___x_826_ = lean_box(0);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_826_);
v___x_828_ = v___x_804_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_831_, v_b_832_, v_a_833_, v_a_834_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_b_832_);
lean_dec_ref(v_a_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_837_, lean_object* v_b_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_837_, v_b_838_, v_a_839_, v_a_847_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_851_, v_b_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_b_852_);
lean_dec_ref(v_a_851_);
return v_res_864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_866_ = lean_int_neg(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_867_, lean_object* v_b_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_881_ = 0;
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_box(v___x_881_);
lean_inc_ref(v_a_867_);
v___x_884_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_884_, 0, v_a_867_);
lean_closure_set(v___x_884_, 1, v___x_883_);
lean_closure_set(v___x_884_, 2, v___x_882_);
v___x_885_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_884_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_1037_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_1037_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_1037_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_del_object(v___x_888_);
v_val_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_a_886_, 1);
v___x_891_ = lean_box(v___x_881_);
lean_inc_ref(v_b_868_);
v___x_892_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_892_, 0, v_b_868_);
lean_closure_set(v___x_892_, 1, v___x_891_);
lean_closure_set(v___x_892_, 2, v___x_882_);
v___x_893_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_892_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_1024_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_1024_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_1024_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 1)
{
lean_object* v_val_898_; lean_object* v___x_899_; 
lean_del_object(v___x_896_);
v_val_898_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v_a_894_, 1);
v___x_899_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_867_, v_a_870_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_868_, v_a_870_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___y_904_; uint8_t v___x_1003_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_1003_ = lean_nat_dec_le(v_a_900_, v_a_902_);
if (v___x_1003_ == 0)
{
lean_dec(v_a_902_);
v___y_904_ = v_a_900_;
goto v___jp_903_;
}
else
{
lean_dec(v_a_900_);
v___y_904_ = v_a_902_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc(v_val_898_);
lean_inc(v_val_890_);
v___x_905_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_905_, 0, v_val_890_);
lean_ctor_set(v___x_905_, 1, v_val_898_);
v___x_906_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_907_, 0, v_a_867_);
lean_ctor_set(v___x_907_, 1, v_b_868_);
lean_ctor_set(v___x_907_, 2, v_val_890_);
lean_ctor_set(v___x_907_, 3, v_val_898_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_908_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_p_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v_p_911_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v___y_904_);
lean_inc_ref(v_p_911_);
v___x_912_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_911_, v___y_904_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
lean_inc(v___y_904_);
v___x_914_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_913_, v___x_881_, v___y_904_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_978_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_978_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_978_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_978_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 1)
{
lean_object* v_val_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_val_919_ = lean_ctor_get(v_a_915_, 0);
lean_inc_n(v_val_919_, 2);
lean_dec_ref_known(v_a_915_, 1);
v___x_920_ = l_Lean_Grind_Linarith_Expr_norm(v_val_919_);
v___x_921_ = lean_box(0);
v___x_922_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_del_object(v___x_917_);
lean_inc(v_a_910_);
v___x_923_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_923_, 0, v_a_910_);
lean_ctor_set(v___x_923_, 1, v_val_919_);
lean_inc(v___x_920_);
v___x_924_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*2, v___x_881_);
v___x_925_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_924_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_969_);
v___x_927_ = v___x_925_;
v_isShared_928_ = v_isSharedCheck_968_;
goto v_resetjp_926_;
}
else
{
lean_dec(v___x_925_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_968_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_911_);
v___x_930_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_929_, v_p_911_);
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 0, v_a_910_);
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_910_);
v___x_932_ = v_reuseFailAlloc_967_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc_ref(v___x_930_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_inc(v___y_904_);
v___x_934_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_930_, v___y_904_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_935_, v___x_881_, v___y_904_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_950_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 1)
{
lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_939_);
v_val_941_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v_a_937_, 1);
v___x_942_ = l_Lean_Grind_Linarith_Poly_mul(v___x_920_, v___x_929_);
v___x_943_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_933_);
lean_ctor_set(v___x_943_, 1, v_val_941_);
v___x_944_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
lean_ctor_set_uint8(v___x_944_, sizeof(void*)*2, v___x_881_);
v___x_945_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_944_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_a_937_);
lean_dec_ref_known(v___x_933_, 2);
lean_dec(v___x_920_);
v___x_946_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref_known(v___x_933_, 2);
lean_dec(v___x_920_);
v_a_951_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_936_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_936_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref_known(v___x_933_, 2);
lean_dec(v___x_920_);
lean_dec(v___y_904_);
v_a_959_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_934_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_934_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
else
{
lean_dec(v___x_920_);
lean_dec(v_a_910_);
lean_dec(v___y_904_);
return v___x_925_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v___x_920_);
lean_dec(v_val_919_);
lean_dec(v_a_910_);
lean_dec(v___y_904_);
v___x_970_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_970_);
v___x_972_ = v___x_917_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_dec(v_a_915_);
lean_dec(v_a_910_);
lean_dec(v___y_904_);
v___x_974_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_974_);
v___x_976_ = v___x_917_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_a_910_);
lean_dec(v___y_904_);
v_a_979_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_914_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_914_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_a_910_);
lean_dec(v___y_904_);
v_a_987_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_912_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_912_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v___y_904_);
v_a_995_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_909_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_909_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_900_);
lean_dec(v_val_898_);
lean_dec(v_val_890_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v_a_1004_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_901_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_901_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_val_898_);
lean_dec(v_val_890_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v_a_1012_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_899_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_899_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_dec(v_a_894_);
lean_dec(v_val_890_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v___x_1020_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_1020_);
v___x_1022_ = v___x_896_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_val_890_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v_a_1025_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_893_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_893_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec(v_a_886_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v___x_1033_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_1033_);
v___x_1035_ = v___x_888_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
v_a_1038_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_885_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_885_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1046_, v_b_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1061_, lean_object* v_b_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1061_, v_a_1064_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = 0;
lean_inc_ref(v_a_1061_);
v___x_1078_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1061_, v___x_1077_, v_a_1076_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1133_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1133_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1133_;
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
v___x_1084_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1062_, v_a_1064_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
lean_inc_ref(v_b_1062_);
v___x_1086_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1062_, v___x_1077_, v_a_1085_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1112_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_val_1091_ = lean_ctor_get(v_a_1087_, 0);
lean_inc_n(v_val_1091_, 2);
lean_dec_ref_known(v_a_1087_, 1);
lean_inc(v_val_1083_);
v___x_1092_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_val_1083_);
lean_ctor_set(v___x_1092_, 1, v_val_1091_);
v___x_1093_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1092_);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1093_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1089_);
lean_inc(v_val_1091_);
lean_inc(v_val_1083_);
lean_inc_ref(v_b_1062_);
lean_inc_ref(v_a_1061_);
v___x_1096_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1061_);
lean_ctor_set(v___x_1096_, 1, v_b_1062_);
lean_ctor_set(v___x_1096_, 2, v_val_1083_);
lean_ctor_set(v___x_1096_, 3, v_val_1091_);
lean_inc(v___x_1093_);
v___x_1097_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1093_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*2, v___x_1077_);
v___x_1098_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1097_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1100_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1093_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1101_, 0, v_b_1062_);
lean_ctor_set(v___x_1101_, 1, v_a_1061_);
lean_ctor_set(v___x_1101_, 2, v_val_1091_);
lean_ctor_set(v___x_1101_, 3, v_val_1083_);
v___x_1102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*2, v___x_1077_);
v___x_1103_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1102_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
return v___x_1103_;
}
else
{
lean_dec(v___x_1093_);
lean_dec(v_val_1091_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
return v___x_1098_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v___x_1093_);
lean_dec(v_val_1091_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v___x_1104_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1104_);
v___x_1106_ = v___x_1089_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec(v_a_1087_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v___x_1108_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1108_);
v___x_1110_ = v___x_1089_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v_a_1113_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1086_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1086_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v_a_1121_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1084_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1084_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_dec(v_a_1079_);
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v___x_1129_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1129_);
v___x_1131_ = v___x_1081_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v_a_1134_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1078_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1078_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_b_1062_);
lean_dec_ref(v_a_1061_);
v_a_1142_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1075_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1075_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1150_, lean_object* v_b_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1150_, v_b_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_a_1152_);
return v_res_1164_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___x_2795__overap_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1180_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1180_, 0, v___x_1179_);
v___x_2795__overap_1181_ = lean_panic_fn_borrowed(v___f_1180_, v_msg_1166_);
lean_dec_ref(v___f_1180_);
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc(v___y_1168_);
lean_inc(v___y_1167_);
v___x_1182_ = lean_apply_12(v___x_2795__overap_1181_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, lean_box(0));
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_nat_to_int(v_a_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1203_ = lean_unsigned_to_nat(42u);
v___x_1204_ = lean_unsigned_to_nat(87u);
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1207_ = l_mkPanicMessageWithDecl(v___x_1206_, v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v_c_1224_; lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v_c_1232_; lean_object* v_p_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; uint8_t v___x_1269_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1269_ = lean_unbox(v_a_1230_);
lean_dec(v_a_1230_);
if (v___x_1269_ == 0)
{
lean_object* v_p_1270_; 
v_p_1270_ = lean_ctor_get(v_c_1208_, 0);
lean_inc(v_p_1270_);
v_c_1232_ = v_c_1208_;
v_p_1233_ = v_p_1270_;
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
v___y_1244_ = v_a_1219_;
goto v___jp_1231_;
}
else
{
lean_object* v_p_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_p_1271_ = lean_ctor_get(v_c_1208_, 0);
v___x_1272_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1271_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_inc(v___x_1272_);
v___x_1275_ = lean_nat_to_int(v___x_1272_);
lean_inc(v_p_1271_);
v___x_1276_ = l_Lean_Grind_Linarith_Poly_div(v_p_1271_, v___x_1275_);
lean_dec(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
lean_ctor_set(v___x_1277_, 1, v_c_1208_);
lean_inc(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v_c_1232_ = v___x_1278_;
v_p_1233_ = v___x_1276_;
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
v___y_1244_ = v_a_1219_;
goto v___jp_1231_;
}
else
{
lean_inc(v_p_1271_);
lean_dec(v___x_1272_);
v_c_1232_ = v_c_1208_;
v_p_1233_ = v_p_1271_;
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
v___y_1244_ = v_a_1219_;
goto v___jp_1231_;
}
}
v___jp_1231_:
{
lean_object* v___x_1245_; 
lean_inc(v_p_1233_);
v___x_1245_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1233_);
if (lean_obj_tag(v___x_1245_) == 1)
{
lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1266_; 
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1266_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1266_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1265_; 
v_fst_1250_ = lean_ctor_get(v_val_1246_, 0);
v_snd_1251_ = lean_ctor_get(v_val_1246_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_val_1246_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1253_ = v_val_1246_;
v_isShared_1254_ = v_isSharedCheck_1265_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1251_);
lean_inc(v_fst_1250_);
lean_dec(v_val_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1265_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1256_ = lean_int_dec_lt(v_fst_1250_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_del_object(v___x_1253_);
lean_del_object(v___x_1248_);
lean_dec(v_p_1233_);
v___y_1222_ = v_fst_1250_;
v___y_1223_ = v_snd_1251_;
v_c_1224_ = v_c_1232_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1258_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1233_, v___x_1257_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 3);
lean_ctor_set(v___x_1248_, 0, v_c_1232_);
v___x_1260_ = v___x_1248_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_c_1232_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1260_);
lean_ctor_set(v___x_1253_, 0, v___x_1258_);
v___x_1262_ = v___x_1253_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v___y_1222_ = v_fst_1250_;
v___y_1223_ = v_snd_1251_;
v_c_1224_ = v___x_1262_;
goto v___jp_1221_;
}
}
}
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v___x_1245_);
lean_dec(v_p_1233_);
lean_dec_ref(v_c_1232_);
v___x_1267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1268_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1267_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_c_1208_);
v_a_1279_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1229_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1229_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
v___jp_1221_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1225_ = lean_nat_abs(v___y_1222_);
lean_dec(v___y_1222_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1223_);
lean_ctor_set(v___x_1226_, 1, v_c_1224_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec(v_a_1288_);
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = l_Lean_maxRecDepthErrorMessage;
v___x_1307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1311_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1312_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_ref_1313_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1322_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_ref_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1336_, v_ref_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v_toCold_1382_; lean_object* v_p_1383_; lean_object* v_currRecDepth_1384_; lean_object* v_ref_1385_; uint8_t v_diag_1386_; uint8_t v_suppressElabErrors_1387_; lean_object* v_options_1388_; lean_object* v_maxRecDepth_1389_; lean_object* v_inheritedTraceOptions_1390_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_toCold_1382_ = lean_ctor_get(v_a_1361_, 0);
lean_inc_ref(v_toCold_1382_);
v_p_1383_ = lean_ctor_get(v_c_1351_, 0);
v_currRecDepth_1384_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_currRecDepth_1384_);
v_ref_1385_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_ref_1385_);
v_diag_1386_ = lean_ctor_get_uint8(v_a_1361_, sizeof(void*)*3);
v_suppressElabErrors_1387_ = lean_ctor_get_uint8(v_a_1361_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_1361_);
v_options_1388_ = lean_ctor_get(v_toCold_1382_, 2);
lean_inc_ref(v_options_1388_);
v_maxRecDepth_1389_ = lean_ctor_get(v_toCold_1382_, 3);
v_inheritedTraceOptions_1390_ = lean_ctor_get(v_toCold_1382_, 11);
lean_inc_ref(v_inheritedTraceOptions_1390_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_nat_dec_eq(v_maxRecDepth_1389_, v___x_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_eq(v_currRecDepth_1384_, v_maxRecDepth_1389_);
if (v___x_1486_ == 0)
{
goto v___jp_1391_;
}
else
{
lean_object* v___x_1487_; 
lean_dec_ref(v_inheritedTraceOptions_1390_);
lean_dec_ref(v_options_1388_);
lean_dec(v_currRecDepth_1384_);
lean_dec_ref(v_toCold_1382_);
lean_dec_ref(v_c_1351_);
v___x_1487_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1385_);
return v___x_1487_;
}
}
else
{
goto v___jp_1391_;
}
v___jp_1364_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1367_);
lean_ctor_set(v___x_1379_, 1, v___y_1365_);
lean_ctor_set(v___x_1379_, 2, v_c_1351_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___y_1366_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v_c_1351_ = v___x_1380_;
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
v_a_1362_ = v___y_1378_;
goto _start;
}
v___jp_1391_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_currRecDepth_1384_, v___x_1392_);
lean_dec(v_currRecDepth_1384_);
v___x_1394_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1394_, 0, v_toCold_1382_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
lean_ctor_set(v___x_1394_, 2, v_ref_1385_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3, v_diag_1386_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3 + 1, v_suppressElabErrors_1387_);
lean_inc(v_p_1383_);
v___x_1395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1383_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v___x_1394_, v_a_1362_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1475_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1475_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1475_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 1)
{
lean_object* v_val_1400_; lean_object* v_snd_1401_; uint8_t v_hasTrace_1402_; 
lean_del_object(v___x_1398_);
v_val_1400_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v_a_1396_, 1);
v_snd_1401_ = lean_ctor_get(v_val_1400_, 1);
lean_inc(v_snd_1401_);
v_hasTrace_1402_ = lean_ctor_get_uint8(v_options_1388_, sizeof(void*)*1);
if (v_hasTrace_1402_ == 0)
{
lean_object* v_fst_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; 
lean_dec_ref(v_inheritedTraceOptions_1390_);
lean_dec_ref(v_options_1388_);
v_fst_1403_ = lean_ctor_get(v_val_1400_, 0);
lean_inc(v_fst_1403_);
lean_dec(v_val_1400_);
v_fst_1404_ = lean_ctor_get(v_snd_1401_, 0);
lean_inc(v_fst_1404_);
v_snd_1405_ = lean_ctor_get(v_snd_1401_, 1);
lean_inc(v_snd_1405_);
lean_dec(v_snd_1401_);
v___y_1365_ = v_fst_1404_;
v___y_1366_ = v_snd_1405_;
v___y_1367_ = v_fst_1403_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v___x_1394_;
v___y_1378_ = v_a_1362_;
goto v___jp_1364_;
}
else
{
lean_object* v_fst_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1470_; 
v_fst_1406_ = lean_ctor_get(v_val_1400_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_val_1400_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_val_1400_, 1);
lean_dec(v_unused_1471_);
v___x_1408_ = v_val_1400_;
v_isShared_1409_ = v_isSharedCheck_1470_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_fst_1406_);
lean_dec(v_val_1400_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1470_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1469_; 
v_fst_1410_ = lean_ctor_get(v_snd_1401_, 0);
v_snd_1411_ = lean_ctor_get(v_snd_1401_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1401_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1413_ = v_snd_1401_;
v_isShared_1414_ = v_isSharedCheck_1469_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_inc(v_fst_1410_);
lean_dec(v_snd_1401_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1469_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1390_, v_options_1388_, v___x_1416_);
lean_dec_ref(v_options_1388_);
lean_dec_ref(v_inheritedTraceOptions_1390_);
if (v___x_1417_ == 0)
{
lean_del_object(v___x_1413_);
lean_del_object(v___x_1408_);
v___y_1365_ = v_fst_1410_;
v___y_1366_ = v_snd_1411_;
v___y_1367_ = v_fst_1406_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v___x_1394_;
v___y_1378_ = v_a_1362_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1406_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v___x_1394_, v_a_1362_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v___x_1394_, v_a_1362_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1410_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v___x_1394_, v_a_1362_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_MessageData_ofExpr(v_a_1419_);
v___x_1425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 7);
lean_ctor_set(v___x_1413_, 1, v___x_1425_);
lean_ctor_set(v___x_1413_, 0, v___x_1424_);
v___x_1427_ = v___x_1413_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = l_Lean_MessageData_ofExpr(v_a_1421_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 7);
lean_ctor_set(v___x_1408_, 1, v___x_1428_);
lean_ctor_set(v___x_1408_, 0, v___x_1427_);
v___x_1430_ = v___x_1408_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1425_);
v___x_1432_ = l_Lean_MessageData_ofExpr(v_a_1423_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1415_, v___x_1433_, v_a_1359_, v_a_1360_, v___x_1394_, v_a_1362_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v___y_1365_ = v_fst_1410_;
v___y_1366_ = v_snd_1411_;
v___y_1367_ = v_fst_1406_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v___x_1394_;
v___y_1378_ = v_a_1362_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_c_1351_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_a_1421_);
lean_dec(v_a_1419_);
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_c_1351_);
v_a_1445_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1422_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1422_);
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
lean_dec(v_a_1419_);
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_c_1351_);
v_a_1453_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1420_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1420_);
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
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec(v_fst_1406_);
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_c_1351_);
v_a_1461_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1418_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1418_);
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
}
}
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_a_1396_);
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_inheritedTraceOptions_1390_);
lean_dec_ref(v_options_1388_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_c_1351_);
v___x_1473_ = v___x_1398_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_c_1351_);
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
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref_known(v___x_1394_, 3);
lean_dec_ref(v_inheritedTraceOptions_1390_);
lean_dec_ref(v_options_1388_);
lean_dec_ref(v_c_1351_);
v_a_1476_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1395_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1395_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec(v_a_1489_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_ref_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_ref_1508_ = lean_ctor_get(v___y_1505_, 2);
v___x_1509_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_inc(v_ref_1508_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_ref_1508_);
lean_ctor_set(v___x_1514_, 1, v_a_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 1);
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1553_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1553_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1553_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_leFn_x3f_1546_; 
v_leFn_x3f_1546_ = lean_ctor_get(v_a_1542_, 20);
lean_inc(v_leFn_x3f_1546_);
lean_dec(v_a_1542_);
if (lean_obj_tag(v_leFn_x3f_1546_) == 1)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
v_val_1547_ = lean_ctor_get(v_leFn_x3f_1546_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_leFn_x3f_1546_, 1);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v_val_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_val_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v_leFn_x3f_1546_);
lean_del_object(v___x_1544_);
v___x_1551_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1552_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1551_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_a_1554_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1541_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1541_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1602_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_ltFn_x3f_1595_; 
v_ltFn_x3f_1595_ = lean_ctor_get(v_a_1591_, 21);
lean_inc(v_ltFn_x3f_1595_);
lean_dec(v_a_1591_);
if (lean_obj_tag(v_ltFn_x3f_1595_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1598_; 
v_val_1596_ = lean_ctor_get(v_ltFn_x3f_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_ltFn_x3f_1595_, 1);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_val_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_val_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_ltFn_x3f_1595_);
lean_del_object(v___x_1593_);
v___x_1600_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1601_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1600_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1590_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1590_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec(v___y_1611_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1624_, uint8_t v_strict_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
if (v_strict_1625_ == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1652_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1652_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1652_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_ofNatZero_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v_ofNatZero_1647_ = lean_ctor_get(v_a_1643_, 18);
lean_inc_ref(v_ofNatZero_1647_);
lean_dec(v_a_1643_);
v___x_1648_ = l_Lean_mkAppB(v_a_1639_, v_a_1641_, v_ofNatZero_1647_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1641_);
lean_dec(v_a_1639_);
v_a_1653_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1642_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1642_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec(v_a_1639_);
return v___x_1640_;
}
}
else
{
return v___x_1638_;
}
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1675_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_ofNatZero_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v_ofNatZero_1670_ = lean_ctor_get(v_a_1666_, 18);
lean_inc_ref(v_ofNatZero_1670_);
lean_dec(v_a_1666_);
v___x_1671_ = l_Lean_mkAppB(v_a_1662_, v_a_1664_, v_ofNatZero_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_a_1664_);
lean_dec(v_a_1662_);
v_a_1676_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1665_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1665_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_dec(v_a_1662_);
return v___x_1663_;
}
}
else
{
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1684_, lean_object* v_strict_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v_strict_boxed_1698_; lean_object* v_res_1699_; 
v_strict_boxed_1698_ = lean_unbox(v_strict_1685_);
v_res_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1684_, v_strict_boxed_1698_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v_p_1684_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_p_1713_; uint8_t v_strict_1714_; lean_object* v___x_1715_; 
v_p_1713_ = lean_ctor_get(v_c_1700_, 0);
v_strict_1714_ = lean_ctor_get_uint8(v_c_1700_, sizeof(void*)*2);
v___x_1715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1713_, v_strict_1714_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v_c_1716_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1730_, lean_object* v_x_1731_, lean_object* v_c_u2081_1732_, lean_object* v_b_1733_, lean_object* v_c_u2082_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_toCold_1747_; lean_object* v_options_1748_; lean_object* v_p_1749_; lean_object* v_p_1750_; uint8_t v_strict_1751_; lean_object* v_inheritedTraceOptions_1752_; uint8_t v_hasTrace_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_p_1758_; 
v_toCold_1747_ = lean_ctor_get(v_a_1744_, 0);
v_options_1748_ = lean_ctor_get(v_toCold_1747_, 2);
v_p_1749_ = lean_ctor_get(v_c_u2081_1732_, 0);
v_p_1750_ = lean_ctor_get(v_c_u2082_1734_, 0);
v_strict_1751_ = lean_ctor_get_uint8(v_c_u2082_1734_, sizeof(void*)*2);
v_inheritedTraceOptions_1752_ = lean_ctor_get(v_toCold_1747_, 11);
v_hasTrace_1753_ = lean_ctor_get_uint8(v_options_1748_, sizeof(void*)*1);
v___x_1754_ = lean_nat_to_int(v_a_1730_);
lean_inc(v_p_1750_);
v___x_1755_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1750_, v___x_1754_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_int_neg(v_b_1733_);
lean_inc(v_p_1749_);
v___x_1757_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1749_, v___x_1756_);
lean_dec(v___x_1756_);
v_p_1758_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1755_, v___x_1757_);
if (v_hasTrace_1753_ == 0)
{
goto v___jp_1759_;
}
else
{
lean_object* v_cls_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_cls_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1752_, v_options_1748_, v___x_1764_);
if (v___x_1765_ == 0)
{
goto v___jp_1759_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1731_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1732_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_MessageData_ofExpr(v_a_1767_);
v___x_1773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_MessageData_ofExpr(v_a_1769_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v___x_1773_);
v___x_1778_ = l_Lean_MessageData_ofExpr(v_a_1771_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1763_, v___x_1779_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref_known(v___x_1780_, 1);
goto v___jp_1759_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_p_1758_);
lean_dec_ref(v_c_u2082_1734_);
lean_dec_ref(v_c_u2081_1732_);
lean_dec(v_x_1731_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
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
lean_dec(v_a_1769_);
lean_dec(v_a_1767_);
lean_dec(v_p_1758_);
lean_dec_ref(v_c_u2082_1734_);
lean_dec_ref(v_c_u2081_1732_);
lean_dec(v_x_1731_);
v_a_1789_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1770_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1770_);
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
lean_dec(v_a_1767_);
lean_dec(v_p_1758_);
lean_dec_ref(v_c_u2082_1734_);
lean_dec_ref(v_c_u2081_1732_);
lean_dec(v_x_1731_);
v_a_1797_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1768_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1768_);
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
lean_dec(v_p_1758_);
lean_dec_ref(v_c_u2082_1734_);
lean_dec_ref(v_c_u2081_1732_);
lean_dec(v_x_1731_);
v_a_1805_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1766_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1766_);
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
}
v___jp_1759_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1760_, 0, v_x_1731_);
lean_ctor_set(v___x_1760_, 1, v_c_u2081_1732_);
lean_ctor_set(v___x_1760_, 2, v_c_u2082_1734_);
v___x_1761_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1761_, 0, v_p_1758_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*2, v_strict_1751_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1813_ = _args[0];
lean_object* v_x_1814_ = _args[1];
lean_object* v_c_u2081_1815_ = _args[2];
lean_object* v_b_1816_ = _args[3];
lean_object* v_c_u2082_1817_ = _args[4];
lean_object* v_a_1818_ = _args[5];
lean_object* v_a_1819_ = _args[6];
lean_object* v_a_1820_ = _args[7];
lean_object* v_a_1821_ = _args[8];
lean_object* v_a_1822_ = _args[9];
lean_object* v_a_1823_ = _args[10];
lean_object* v_a_1824_ = _args[11];
lean_object* v_a_1825_ = _args[12];
lean_object* v_a_1826_ = _args[13];
lean_object* v_a_1827_ = _args[14];
lean_object* v_a_1828_ = _args[15];
lean_object* v_a_1829_ = _args[16];
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1813_, v_x_1814_, v_c_u2081_1815_, v_b_1816_, v_c_u2082_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec(v_b_1816_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1831_, lean_object* v_msg_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1832_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_msg_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1846_, v_msg_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1869_, lean_object* v_x_1870_, lean_object* v_c_u2081_1871_, lean_object* v_as_1872_, size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
lean_dec_ref(v_c_u2081_1871_);
lean_dec(v_x_1870_);
lean_dec(v_a_1869_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_b_1875_);
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1893_; 
lean_dec_ref(v_b_1875_);
v_a_1890_ = lean_array_uget_borrowed(v_as_1872_, v_i_1874_);
v_fst_1891_ = lean_ctor_get(v_a_1890_, 0);
v_snd_1892_ = lean_ctor_get(v_a_1890_, 1);
lean_inc(v_snd_1892_);
lean_inc_ref(v_c_u2081_1871_);
lean_inc(v_x_1870_);
lean_inc(v_a_1869_);
v___x_1893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1869_, v_x_1870_, v_c_u2081_1871_, v_fst_1891_, v_snd_1892_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1894_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1896_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1910_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; 
v___x_1901_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; 
lean_del_object(v___x_1899_);
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1874_, v___x_1903_);
v_i_1874_ = v___x_1904_;
v_b_1875_ = v___x_1902_;
goto _start;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_dec_ref(v_c_u2081_1871_);
lean_dec(v_x_1870_);
lean_dec(v_a_1869_);
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1906_);
v___x_1908_ = v___x_1899_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
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
lean_dec_ref(v_c_u2081_1871_);
lean_dec(v_x_1870_);
lean_dec(v_a_1869_);
v_a_1911_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1896_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1896_);
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
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_c_u2081_1871_);
lean_dec(v_x_1870_);
lean_dec(v_a_1869_);
v_a_1919_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1895_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1895_);
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
lean_dec_ref(v_c_u2081_1871_);
lean_dec(v_x_1870_);
lean_dec(v_a_1869_);
v_a_1927_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1893_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1893_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1935_ = _args[0];
lean_object* v_x_1936_ = _args[1];
lean_object* v_c_u2081_1937_ = _args[2];
lean_object* v_as_1938_ = _args[3];
lean_object* v_sz_1939_ = _args[4];
lean_object* v_i_1940_ = _args[5];
lean_object* v_b_1941_ = _args[6];
lean_object* v___y_1942_ = _args[7];
lean_object* v___y_1943_ = _args[8];
lean_object* v___y_1944_ = _args[9];
lean_object* v___y_1945_ = _args[10];
lean_object* v___y_1946_ = _args[11];
lean_object* v___y_1947_ = _args[12];
lean_object* v___y_1948_ = _args[13];
lean_object* v___y_1949_ = _args[14];
lean_object* v___y_1950_ = _args[15];
lean_object* v___y_1951_ = _args[16];
lean_object* v___y_1952_ = _args[17];
lean_object* v___y_1953_ = _args[18];
_start:
{
size_t v_sz_boxed_1954_; size_t v_i_boxed_1955_; lean_object* v_res_1956_; 
v_sz_boxed_1954_ = lean_unbox_usize(v_sz_1939_);
lean_dec(v_sz_1939_);
v_i_boxed_1955_ = lean_unbox_usize(v_i_1940_);
lean_dec(v_i_1940_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1935_, v_x_1936_, v_c_u2081_1937_, v_as_1938_, v_sz_boxed_1954_, v_i_boxed_1955_, v_b_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v_as_1938_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1957_, lean_object* v_x_1958_, lean_object* v_c_u2081_1959_, lean_object* v_todo_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; size_t v_sz_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1973_ = lean_box(0);
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1975_ = lean_array_size(v_todo_1960_);
v___x_1976_ = ((size_t)0ULL);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1957_, v_x_1958_, v_c_u2081_1959_, v_todo_1960_, v_sz_1975_, v___x_1976_, v___x_1974_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1990_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fst_1982_; 
v_fst_1982_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_fst_1982_);
lean_dec(v_a_1978_);
if (lean_obj_tag(v_fst_1982_) == 0)
{
lean_object* v___x_1984_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1973_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1973_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v_val_1986_; lean_object* v___x_1988_; 
v_val_1986_ = lean_ctor_get(v_fst_1982_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_fst_1982_, 1);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_val_1986_);
v___x_1988_ = v___x_1980_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_val_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1977_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1977_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_1999_, lean_object* v_x_2000_, lean_object* v_c_u2081_2001_, lean_object* v_todo_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_1999_, v_x_2000_, v_c_u2081_2001_, v_todo_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_todo_2002_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2016_, lean_object* v_as_2017_, size_t v_sz_2018_, size_t v_i_2019_, lean_object* v_b_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_lt(v_i_2019_, v_sz_2018_);
if (v___x_2021_ == 0)
{
return v_b_2020_;
}
else
{
lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2055_; 
v_snd_2022_ = lean_ctor_get(v_b_2020_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_b_2020_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_b_2020_, 0);
lean_dec(v_unused_2056_);
v___x_2024_ = v_b_2020_;
v_isShared_2025_ = v_isSharedCheck_2055_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_dec(v_b_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2055_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2054_; 
v_fst_2026_ = lean_ctor_get(v_snd_2022_, 0);
v_snd_2027_ = lean_ctor_get(v_snd_2022_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_snd_2022_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2029_ = v_snd_2022_;
v_isShared_2030_ = v_isSharedCheck_2054_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_inc(v_fst_2026_);
lean_dec(v_snd_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2054_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_a_2031_; lean_object* v_p_2032_; lean_object* v___x_2033_; lean_object* v_a_2035_; lean_object* v_b_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_a_2031_ = lean_array_uget_borrowed(v_as_2017_, v_i_2019_);
v_p_2032_ = lean_ctor_get(v_a_2031_, 0);
v___x_2033_ = lean_box(0);
v_b_2042_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2032_, v_x_2016_);
v___x_2043_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2044_ = lean_int_dec_eq(v_b_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2046_; 
lean_inc(v_a_2031_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2031_);
lean_ctor_set(v___x_2024_, 0, v_b_2042_);
v___x_2046_ = v___x_2024_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_b_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2031_);
v___x_2046_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v_todo_2047_; lean_object* v___x_2048_; 
v_todo_2047_ = lean_array_push(v_snd_2027_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_fst_2026_);
lean_ctor_set(v___x_2048_, 1, v_todo_2047_);
v_a_2035_ = v___x_2048_;
goto v___jp_2034_;
}
}
else
{
lean_object* v_cs_x27_2050_; lean_object* v___x_2052_; 
lean_dec(v_b_2042_);
lean_inc(v_a_2031_);
v_cs_x27_2050_ = l_Lean_PersistentArray_push___redArg(v_fst_2026_, v_a_2031_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_snd_2027_);
lean_ctor_set(v___x_2024_, 0, v_cs_x27_2050_);
v___x_2052_ = v___x_2024_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_cs_x27_2050_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_snd_2027_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
v_a_2035_ = v___x_2052_;
goto v___jp_2034_;
}
}
v___jp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v_a_2035_);
lean_ctor_set(v___x_2029_, 0, v___x_2033_);
v___x_2037_ = v___x_2029_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2035_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
size_t v___x_2038_; size_t v___x_2039_; 
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2019_, v___x_2038_);
v_i_2019_ = v___x_2039_;
v_b_2020_ = v___x_2037_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2057_, lean_object* v_as_2058_, lean_object* v_sz_2059_, lean_object* v_i_2060_, lean_object* v_b_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2059_);
lean_dec(v_sz_2059_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2057_, v_as_2058_, v_sz_boxed_2062_, v_i_boxed_2063_, v_b_2061_);
lean_dec_ref(v_as_2058_);
lean_dec(v_x_2057_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2065_, lean_object* v_as_2066_, size_t v_sz_2067_, size_t v_i_2068_, lean_object* v_b_2069_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_lt(v_i_2068_, v_sz_2067_);
if (v___x_2070_ == 0)
{
return v_b_2069_;
}
else
{
lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2104_; 
v_snd_2071_ = lean_ctor_get(v_b_2069_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_b_2069_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_b_2069_, 0);
lean_dec(v_unused_2105_);
v___x_2073_ = v_b_2069_;
v_isShared_2074_ = v_isSharedCheck_2104_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_dec(v_b_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2104_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2103_; 
v_fst_2075_ = lean_ctor_get(v_snd_2071_, 0);
v_snd_2076_ = lean_ctor_get(v_snd_2071_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_snd_2071_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2078_ = v_snd_2071_;
v_isShared_2079_ = v_isSharedCheck_2103_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_inc(v_fst_2075_);
lean_dec(v_snd_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2103_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_a_2080_; lean_object* v_p_2081_; lean_object* v___x_2082_; lean_object* v_a_2084_; lean_object* v_b_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_a_2080_ = lean_array_uget_borrowed(v_as_2066_, v_i_2068_);
v_p_2081_ = lean_ctor_get(v_a_2080_, 0);
v___x_2082_ = lean_box(0);
v_b_2091_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2081_, v_x_2065_);
v___x_2092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2093_ = lean_int_dec_eq(v_b_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2095_; 
lean_inc(v_a_2080_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_a_2080_);
lean_ctor_set(v___x_2073_, 0, v_b_2091_);
v___x_2095_ = v___x_2073_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_b_2091_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_2080_);
v___x_2095_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v_todo_2096_; lean_object* v___x_2097_; 
v_todo_2096_ = lean_array_push(v_snd_2076_, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_fst_2075_);
lean_ctor_set(v___x_2097_, 1, v_todo_2096_);
v_a_2084_ = v___x_2097_;
goto v___jp_2083_;
}
}
else
{
lean_object* v_cs_x27_2099_; lean_object* v___x_2101_; 
lean_dec(v_b_2091_);
lean_inc(v_a_2080_);
v_cs_x27_2099_ = l_Lean_PersistentArray_push___redArg(v_fst_2075_, v_a_2080_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_snd_2076_);
lean_ctor_set(v___x_2073_, 0, v_cs_x27_2099_);
v___x_2101_ = v___x_2073_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_cs_x27_2099_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_snd_2076_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v_a_2084_ = v___x_2101_;
goto v___jp_2083_;
}
}
v___jp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v_a_2084_);
lean_ctor_set(v___x_2078_, 0, v___x_2082_);
v___x_2086_ = v___x_2078_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_a_2084_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2068_, v___x_2087_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2065_, v_as_2066_, v_sz_2067_, v___x_2088_, v___x_2086_);
return v___x_2089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2106_, lean_object* v_as_2107_, lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_b_2110_){
_start:
{
size_t v_sz_boxed_2111_; size_t v_i_boxed_2112_; lean_object* v_res_2113_; 
v_sz_boxed_2111_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2112_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2106_, v_as_2107_, v_sz_boxed_2111_, v_i_boxed_2112_, v_b_2110_);
lean_dec_ref(v_as_2107_);
lean_dec(v_x_2106_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2114_, lean_object* v_as_2115_, size_t v_sz_2116_, size_t v_i_2117_, lean_object* v_b_2118_){
_start:
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_usize_dec_lt(v_i_2117_, v_sz_2116_);
if (v___x_2119_ == 0)
{
return v_b_2118_;
}
else
{
lean_object* v_snd_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2153_; 
v_snd_2120_ = lean_ctor_get(v_b_2118_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_b_2118_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; 
v_unused_2154_ = lean_ctor_get(v_b_2118_, 0);
lean_dec(v_unused_2154_);
v___x_2122_ = v_b_2118_;
v_isShared_2123_ = v_isSharedCheck_2153_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_snd_2120_);
lean_dec(v_b_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2153_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_fst_2124_; lean_object* v_snd_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2152_; 
v_fst_2124_ = lean_ctor_get(v_snd_2120_, 0);
v_snd_2125_ = lean_ctor_get(v_snd_2120_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_snd_2120_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2127_ = v_snd_2120_;
v_isShared_2128_ = v_isSharedCheck_2152_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_snd_2125_);
lean_inc(v_fst_2124_);
lean_dec(v_snd_2120_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2152_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_a_2129_; lean_object* v_p_2130_; lean_object* v___x_2131_; lean_object* v_a_2133_; lean_object* v_b_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_a_2129_ = lean_array_uget_borrowed(v_as_2115_, v_i_2117_);
v_p_2130_ = lean_ctor_get(v_a_2129_, 0);
v___x_2131_ = lean_box(0);
v_b_2140_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2130_, v_x_2114_);
v___x_2141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2142_ = lean_int_dec_eq(v_b_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; 
lean_inc(v_a_2129_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_a_2129_);
lean_ctor_set(v___x_2122_, 0, v_b_2140_);
v___x_2144_ = v___x_2122_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_b_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_a_2129_);
v___x_2144_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v_todo_2145_; lean_object* v___x_2146_; 
v_todo_2145_ = lean_array_push(v_snd_2125_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_fst_2124_);
lean_ctor_set(v___x_2146_, 1, v_todo_2145_);
v_a_2133_ = v___x_2146_;
goto v___jp_2132_;
}
}
else
{
lean_object* v_cs_x27_2148_; lean_object* v___x_2150_; 
lean_dec(v_b_2140_);
lean_inc(v_a_2129_);
v_cs_x27_2148_ = l_Lean_PersistentArray_push___redArg(v_fst_2124_, v_a_2129_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_snd_2125_);
lean_ctor_set(v___x_2122_, 0, v_cs_x27_2148_);
v___x_2150_ = v___x_2122_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_cs_x27_2148_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_snd_2125_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
v_a_2133_ = v___x_2150_;
goto v___jp_2132_;
}
}
v___jp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_a_2133_);
lean_ctor_set(v___x_2127_, 0, v___x_2131_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_a_2133_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
size_t v___x_2136_; size_t v___x_2137_; 
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2117_, v___x_2136_);
v_i_2117_ = v___x_2137_;
v_b_2118_ = v___x_2135_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2155_, lean_object* v_as_2156_, lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_b_2159_){
_start:
{
size_t v_sz_boxed_2160_; size_t v_i_boxed_2161_; lean_object* v_res_2162_; 
v_sz_boxed_2160_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2161_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2155_, v_as_2156_, v_sz_boxed_2160_, v_i_boxed_2161_, v_b_2159_);
lean_dec_ref(v_as_2156_);
lean_dec(v_x_2155_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2163_, lean_object* v_as_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_b_2167_){
_start:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_usize_dec_lt(v_i_2166_, v_sz_2165_);
if (v___x_2168_ == 0)
{
return v_b_2167_;
}
else
{
lean_object* v_snd_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2202_; 
v_snd_2169_ = lean_ctor_get(v_b_2167_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_b_2167_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v_b_2167_, 0);
lean_dec(v_unused_2203_);
v___x_2171_ = v_b_2167_;
v_isShared_2172_ = v_isSharedCheck_2202_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_snd_2169_);
lean_dec(v_b_2167_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2202_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2201_; 
v_fst_2173_ = lean_ctor_get(v_snd_2169_, 0);
v_snd_2174_ = lean_ctor_get(v_snd_2169_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_snd_2169_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2176_ = v_snd_2169_;
v_isShared_2177_ = v_isSharedCheck_2201_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_inc(v_fst_2173_);
lean_dec(v_snd_2169_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2201_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_a_2178_; lean_object* v_p_2179_; lean_object* v___x_2180_; lean_object* v_a_2182_; lean_object* v_b_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_a_2178_ = lean_array_uget_borrowed(v_as_2164_, v_i_2166_);
v_p_2179_ = lean_ctor_get(v_a_2178_, 0);
v___x_2180_ = lean_box(0);
v_b_2189_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2179_, v_x_2163_);
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2191_ = lean_int_dec_eq(v_b_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2193_; 
lean_inc(v_a_2178_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_a_2178_);
lean_ctor_set(v___x_2171_, 0, v_b_2189_);
v___x_2193_ = v___x_2171_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_b_2189_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2178_);
v___x_2193_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v_todo_2194_; lean_object* v___x_2195_; 
v_todo_2194_ = lean_array_push(v_snd_2174_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_fst_2173_);
lean_ctor_set(v___x_2195_, 1, v_todo_2194_);
v_a_2182_ = v___x_2195_;
goto v___jp_2181_;
}
}
else
{
lean_object* v_cs_x27_2197_; lean_object* v___x_2199_; 
lean_dec(v_b_2189_);
lean_inc(v_a_2178_);
v_cs_x27_2197_ = l_Lean_PersistentArray_push___redArg(v_fst_2173_, v_a_2178_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_snd_2174_);
lean_ctor_set(v___x_2171_, 0, v_cs_x27_2197_);
v___x_2199_ = v___x_2171_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_cs_x27_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_snd_2174_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
v_a_2182_ = v___x_2199_;
goto v___jp_2181_;
}
}
v___jp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_a_2182_);
lean_ctor_set(v___x_2176_, 0, v___x_2180_);
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2166_, v___x_2185_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2163_, v_as_2164_, v_sz_2165_, v___x_2186_, v___x_2184_);
return v___x_2187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2204_, lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_b_2208_){
_start:
{
size_t v_sz_boxed_2209_; size_t v_i_boxed_2210_; lean_object* v_res_2211_; 
v_sz_boxed_2209_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2210_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2204_, v_as_2205_, v_sz_boxed_2209_, v_i_boxed_2210_, v_b_2208_);
lean_dec_ref(v_as_2205_);
lean_dec(v_x_2204_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2212_, lean_object* v_x_2213_, lean_object* v_n_2214_, lean_object* v_b_2215_){
_start:
{
if (lean_obj_tag(v_n_2214_) == 0)
{
lean_object* v_cs_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v_fst_2222_; 
v_cs_2216_ = lean_ctor_get(v_n_2214_, 0);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_b_2215_);
v_sz_2219_ = lean_array_size(v_cs_2216_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2212_, v_x_2213_, v_cs_2216_, v_sz_2219_, v___x_2220_, v___x_2218_);
v_fst_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_fst_2222_);
if (lean_obj_tag(v_fst_2222_) == 0)
{
lean_object* v_snd_2223_; lean_object* v___x_2224_; 
v_snd_2223_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_snd_2223_);
lean_dec_ref(v___x_2221_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_snd_2223_);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; 
lean_dec_ref(v___x_2221_);
v_val_2225_ = lean_ctor_get(v_fst_2222_, 0);
lean_inc(v_val_2225_);
lean_dec_ref_known(v_fst_2222_, 1);
return v_val_2225_;
}
}
else
{
lean_object* v_vs_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; lean_object* v_fst_2232_; 
v_vs_2226_ = lean_ctor_get(v_n_2214_, 0);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_b_2215_);
v_sz_2229_ = lean_array_size(v_vs_2226_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2213_, v_vs_2226_, v_sz_2229_, v___x_2230_, v___x_2228_);
v_fst_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_fst_2232_);
if (lean_obj_tag(v_fst_2232_) == 0)
{
lean_object* v_snd_2233_; lean_object* v___x_2234_; 
v_snd_2233_ = lean_ctor_get(v___x_2231_, 1);
lean_inc(v_snd_2233_);
lean_dec_ref(v___x_2231_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v_snd_2233_);
return v___x_2234_;
}
else
{
lean_object* v_val_2235_; 
lean_dec_ref(v___x_2231_);
v_val_2235_ = lean_ctor_get(v_fst_2232_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v_fst_2232_, 1);
return v_val_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2236_, lean_object* v_x_2237_, lean_object* v_as_2238_, size_t v_sz_2239_, size_t v_i_2240_, lean_object* v_b_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_usize_dec_lt(v_i_2240_, v_sz_2239_);
if (v___x_2242_ == 0)
{
return v_b_2241_;
}
else
{
lean_object* v_snd_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2261_; 
v_snd_2243_ = lean_ctor_get(v_b_2241_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_b_2241_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; 
v_unused_2262_ = lean_ctor_get(v_b_2241_, 0);
lean_dec(v_unused_2262_);
v___x_2245_ = v_b_2241_;
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snd_2243_);
lean_dec(v_b_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_array_uget_borrowed(v_as_2238_, v_i_2240_);
lean_inc(v_snd_2243_);
v___x_2248_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2236_, v_x_2237_, v_a_2247_, v_snd_2243_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2249_);
v___x_2251_ = v___x_2245_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_snd_2243_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
lean_dec(v_snd_2243_);
v_a_2253_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2254_ = lean_box(0);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v_a_2253_);
lean_ctor_set(v___x_2245_, 0, v___x_2254_);
v___x_2256_ = v___x_2245_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_a_2253_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
size_t v___x_2257_; size_t v___x_2258_; 
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2240_, v___x_2257_);
v_i_2240_ = v___x_2258_;
v_b_2241_ = v___x_2256_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2263_, lean_object* v_x_2264_, lean_object* v_as_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_b_2268_){
_start:
{
size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2263_, v_x_2264_, v_as_2265_, v_sz_boxed_2269_, v_i_boxed_2270_, v_b_2268_);
lean_dec_ref(v_as_2265_);
lean_dec(v_x_2264_);
lean_dec_ref(v_init_2263_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2272_, lean_object* v_x_2273_, lean_object* v_n_2274_, lean_object* v_b_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2272_, v_x_2273_, v_n_2274_, v_b_2275_);
lean_dec_ref(v_n_2274_);
lean_dec(v_x_2273_);
lean_dec_ref(v_init_2272_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2277_, lean_object* v_t_2278_, lean_object* v_init_2279_){
_start:
{
lean_object* v_root_2280_; lean_object* v_tail_2281_; lean_object* v___x_2282_; 
v_root_2280_ = lean_ctor_get(v_t_2278_, 0);
v_tail_2281_ = lean_ctor_get(v_t_2278_, 1);
lean_inc_ref(v_init_2279_);
v___x_2282_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2279_, v_x_2277_, v_root_2280_, v_init_2279_);
lean_dec_ref(v_init_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
return v_a_2283_;
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; size_t v_sz_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v_fst_2290_; 
v_a_2284_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_a_2284_);
v_sz_2287_ = lean_array_size(v_tail_2281_);
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2277_, v_tail_2281_, v_sz_2287_, v___x_2288_, v___x_2286_);
v_fst_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_fst_2290_);
if (lean_obj_tag(v_fst_2290_) == 0)
{
lean_object* v_snd_2291_; 
v_snd_2291_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_snd_2291_);
lean_dec_ref(v___x_2289_);
return v_snd_2291_;
}
else
{
lean_object* v_val_2292_; 
lean_dec_ref(v___x_2289_);
v_val_2292_ = lean_ctor_get(v_fst_2290_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v_fst_2290_, 1);
return v_val_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2293_, lean_object* v_t_2294_, lean_object* v_init_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2293_, v_t_2294_, v_init_2295_);
lean_dec_ref(v_t_2294_);
lean_dec(v_x_2293_);
return v_res_2296_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_unsigned_to_nat(32u);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_cs_x27_2305_; 
v___x_2300_ = ((size_t)5ULL);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_unsigned_to_nat(32u);
v___x_2303_ = lean_mk_empty_array_with_capacity(v___x_2302_);
v___x_2304_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2305_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2305_, 0, v___x_2304_);
lean_ctor_set(v_cs_x27_2305_, 1, v___x_2303_);
lean_ctor_set(v_cs_x27_2305_, 2, v___x_2301_);
lean_ctor_set(v_cs_x27_2305_, 3, v___x_2301_);
lean_ctor_set_usize(v_cs_x27_2305_, 4, v___x_2300_);
return v_cs_x27_2305_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2308_; lean_object* v_cs_x27_2309_; lean_object* v___x_2310_; 
v_todo_2308_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2309_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v_cs_x27_2309_);
lean_ctor_set(v___x_2310_, 1, v_todo_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2311_, lean_object* v_cs_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_fst_2315_; lean_object* v_snd_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2314_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2311_, v_cs_2312_, v___x_2313_);
v_fst_2315_ = lean_ctor_get(v___x_2314_, 0);
v_snd_2316_ = lean_ctor_get(v___x_2314_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2314_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_snd_2316_);
lean_inc(v_fst_2315_);
lean_dec(v___x_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_snd_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2324_, lean_object* v_cs_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2324_, v_cs_2325_);
lean_dec_ref(v_cs_2325_);
lean_dec(v_x_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2327_, lean_object* v_cs_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2327_, v_cs_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2330_, lean_object* v_cs_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2330_, v_cs_2331_);
lean_dec_ref(v_cs_2331_);
lean_dec(v_x_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2333_, lean_object* v_y_2334_, lean_object* v_fst_2335_, lean_object* v_s_2336_){
_start:
{
lean_object* v_structs_2337_; lean_object* v_typeIdOf_2338_; lean_object* v_exprToStructId_2339_; lean_object* v_exprToStructIdEntries_2340_; lean_object* v_forbiddenNatModules_2341_; lean_object* v_natStructs_2342_; lean_object* v_natTypeIdOf_2343_; lean_object* v_exprToNatStructId_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_structs_2337_ = lean_ctor_get(v_s_2336_, 0);
v_typeIdOf_2338_ = lean_ctor_get(v_s_2336_, 1);
v_exprToStructId_2339_ = lean_ctor_get(v_s_2336_, 2);
v_exprToStructIdEntries_2340_ = lean_ctor_get(v_s_2336_, 3);
v_forbiddenNatModules_2341_ = lean_ctor_get(v_s_2336_, 4);
v_natStructs_2342_ = lean_ctor_get(v_s_2336_, 5);
v_natTypeIdOf_2343_ = lean_ctor_get(v_s_2336_, 6);
v_exprToNatStructId_2344_ = lean_ctor_get(v_s_2336_, 7);
v___x_2345_ = lean_array_get_size(v_structs_2337_);
v___x_2346_ = lean_nat_dec_lt(v_a_2333_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v_fst_2335_);
return v_s_2336_;
}
else
{
lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2408_; 
lean_inc_ref(v_exprToNatStructId_2344_);
lean_inc_ref(v_natTypeIdOf_2343_);
lean_inc_ref(v_natStructs_2342_);
lean_inc_ref(v_forbiddenNatModules_2341_);
lean_inc_ref(v_exprToStructIdEntries_2340_);
lean_inc_ref(v_exprToStructId_2339_);
lean_inc_ref(v_typeIdOf_2338_);
lean_inc_ref(v_structs_2337_);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_s_2336_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; 
v_unused_2409_ = lean_ctor_get(v_s_2336_, 7);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_s_2336_, 6);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_s_2336_, 5);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_s_2336_, 4);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_s_2336_, 3);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_s_2336_, 2);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2336_, 1);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2336_, 0);
lean_dec(v_unused_2416_);
v___x_2348_ = v_s_2336_;
v_isShared_2349_ = v_isSharedCheck_2408_;
goto v_resetjp_2347_;
}
else
{
lean_dec(v_s_2336_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2408_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_v_2350_; lean_object* v_id_2351_; lean_object* v_ringId_x3f_2352_; lean_object* v_type_2353_; lean_object* v_u_2354_; lean_object* v_intModuleInst_2355_; lean_object* v_leInst_x3f_2356_; lean_object* v_ltInst_x3f_2357_; lean_object* v_lawfulOrderLTInst_x3f_2358_; lean_object* v_isPreorderInst_x3f_2359_; lean_object* v_orderedAddInst_x3f_2360_; lean_object* v_isLinearInst_x3f_2361_; lean_object* v_noNatDivInst_x3f_2362_; lean_object* v_ringInst_x3f_2363_; lean_object* v_commRingInst_x3f_2364_; lean_object* v_orderedRingInst_x3f_2365_; lean_object* v_fieldInst_x3f_2366_; lean_object* v_charInst_x3f_2367_; lean_object* v_zero_2368_; lean_object* v_ofNatZero_2369_; lean_object* v_one_x3f_2370_; lean_object* v_leFn_x3f_2371_; lean_object* v_ltFn_x3f_2372_; lean_object* v_addFn_2373_; lean_object* v_zsmulFn_2374_; lean_object* v_nsmulFn_2375_; lean_object* v_zsmulFn_x3f_2376_; lean_object* v_nsmulFn_x3f_2377_; lean_object* v_homomulFn_x3f_2378_; lean_object* v_subFn_2379_; lean_object* v_negFn_2380_; lean_object* v_vars_2381_; lean_object* v_varMap_2382_; lean_object* v_lowers_2383_; lean_object* v_uppers_2384_; lean_object* v_diseqs_2385_; lean_object* v_assignment_2386_; uint8_t v_caseSplits_2387_; lean_object* v_conflict_x3f_2388_; lean_object* v_diseqSplits_2389_; lean_object* v_elimEqs_2390_; lean_object* v_elimStack_2391_; lean_object* v_occurs_2392_; lean_object* v_ignored_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2407_; 
v_v_2350_ = lean_array_fget(v_structs_2337_, v_a_2333_);
v_id_2351_ = lean_ctor_get(v_v_2350_, 0);
v_ringId_x3f_2352_ = lean_ctor_get(v_v_2350_, 1);
v_type_2353_ = lean_ctor_get(v_v_2350_, 2);
v_u_2354_ = lean_ctor_get(v_v_2350_, 3);
v_intModuleInst_2355_ = lean_ctor_get(v_v_2350_, 4);
v_leInst_x3f_2356_ = lean_ctor_get(v_v_2350_, 5);
v_ltInst_x3f_2357_ = lean_ctor_get(v_v_2350_, 6);
v_lawfulOrderLTInst_x3f_2358_ = lean_ctor_get(v_v_2350_, 7);
v_isPreorderInst_x3f_2359_ = lean_ctor_get(v_v_2350_, 8);
v_orderedAddInst_x3f_2360_ = lean_ctor_get(v_v_2350_, 9);
v_isLinearInst_x3f_2361_ = lean_ctor_get(v_v_2350_, 10);
v_noNatDivInst_x3f_2362_ = lean_ctor_get(v_v_2350_, 11);
v_ringInst_x3f_2363_ = lean_ctor_get(v_v_2350_, 12);
v_commRingInst_x3f_2364_ = lean_ctor_get(v_v_2350_, 13);
v_orderedRingInst_x3f_2365_ = lean_ctor_get(v_v_2350_, 14);
v_fieldInst_x3f_2366_ = lean_ctor_get(v_v_2350_, 15);
v_charInst_x3f_2367_ = lean_ctor_get(v_v_2350_, 16);
v_zero_2368_ = lean_ctor_get(v_v_2350_, 17);
v_ofNatZero_2369_ = lean_ctor_get(v_v_2350_, 18);
v_one_x3f_2370_ = lean_ctor_get(v_v_2350_, 19);
v_leFn_x3f_2371_ = lean_ctor_get(v_v_2350_, 20);
v_ltFn_x3f_2372_ = lean_ctor_get(v_v_2350_, 21);
v_addFn_2373_ = lean_ctor_get(v_v_2350_, 22);
v_zsmulFn_2374_ = lean_ctor_get(v_v_2350_, 23);
v_nsmulFn_2375_ = lean_ctor_get(v_v_2350_, 24);
v_zsmulFn_x3f_2376_ = lean_ctor_get(v_v_2350_, 25);
v_nsmulFn_x3f_2377_ = lean_ctor_get(v_v_2350_, 26);
v_homomulFn_x3f_2378_ = lean_ctor_get(v_v_2350_, 27);
v_subFn_2379_ = lean_ctor_get(v_v_2350_, 28);
v_negFn_2380_ = lean_ctor_get(v_v_2350_, 29);
v_vars_2381_ = lean_ctor_get(v_v_2350_, 30);
v_varMap_2382_ = lean_ctor_get(v_v_2350_, 31);
v_lowers_2383_ = lean_ctor_get(v_v_2350_, 32);
v_uppers_2384_ = lean_ctor_get(v_v_2350_, 33);
v_diseqs_2385_ = lean_ctor_get(v_v_2350_, 34);
v_assignment_2386_ = lean_ctor_get(v_v_2350_, 35);
v_caseSplits_2387_ = lean_ctor_get_uint8(v_v_2350_, sizeof(void*)*42);
v_conflict_x3f_2388_ = lean_ctor_get(v_v_2350_, 36);
v_diseqSplits_2389_ = lean_ctor_get(v_v_2350_, 37);
v_elimEqs_2390_ = lean_ctor_get(v_v_2350_, 38);
v_elimStack_2391_ = lean_ctor_get(v_v_2350_, 39);
v_occurs_2392_ = lean_ctor_get(v_v_2350_, 40);
v_ignored_2393_ = lean_ctor_get(v_v_2350_, 41);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_v_2350_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2395_ = v_v_2350_;
v_isShared_2396_ = v_isSharedCheck_2407_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_ignored_2393_);
lean_inc(v_occurs_2392_);
lean_inc(v_elimStack_2391_);
lean_inc(v_elimEqs_2390_);
lean_inc(v_diseqSplits_2389_);
lean_inc(v_conflict_x3f_2388_);
lean_inc(v_assignment_2386_);
lean_inc(v_diseqs_2385_);
lean_inc(v_uppers_2384_);
lean_inc(v_lowers_2383_);
lean_inc(v_varMap_2382_);
lean_inc(v_vars_2381_);
lean_inc(v_negFn_2380_);
lean_inc(v_subFn_2379_);
lean_inc(v_homomulFn_x3f_2378_);
lean_inc(v_nsmulFn_x3f_2377_);
lean_inc(v_zsmulFn_x3f_2376_);
lean_inc(v_nsmulFn_2375_);
lean_inc(v_zsmulFn_2374_);
lean_inc(v_addFn_2373_);
lean_inc(v_ltFn_x3f_2372_);
lean_inc(v_leFn_x3f_2371_);
lean_inc(v_one_x3f_2370_);
lean_inc(v_ofNatZero_2369_);
lean_inc(v_zero_2368_);
lean_inc(v_charInst_x3f_2367_);
lean_inc(v_fieldInst_x3f_2366_);
lean_inc(v_orderedRingInst_x3f_2365_);
lean_inc(v_commRingInst_x3f_2364_);
lean_inc(v_ringInst_x3f_2363_);
lean_inc(v_noNatDivInst_x3f_2362_);
lean_inc(v_isLinearInst_x3f_2361_);
lean_inc(v_orderedAddInst_x3f_2360_);
lean_inc(v_isPreorderInst_x3f_2359_);
lean_inc(v_lawfulOrderLTInst_x3f_2358_);
lean_inc(v_ltInst_x3f_2357_);
lean_inc(v_leInst_x3f_2356_);
lean_inc(v_intModuleInst_2355_);
lean_inc(v_u_2354_);
lean_inc(v_type_2353_);
lean_inc(v_ringId_x3f_2352_);
lean_inc(v_id_2351_);
lean_dec(v_v_2350_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2407_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v_xs_x27_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2397_ = lean_box(0);
v_xs_x27_2398_ = lean_array_fset(v_structs_2337_, v_a_2333_, v___x_2397_);
v___x_2399_ = l_Lean_PersistentArray_set___redArg(v_lowers_2383_, v_y_2334_, v_fst_2335_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 32, v___x_2399_);
v___x_2401_ = v___x_2395_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_id_2351_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_ringId_x3f_2352_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_type_2353_);
lean_ctor_set(v_reuseFailAlloc_2406_, 3, v_u_2354_);
lean_ctor_set(v_reuseFailAlloc_2406_, 4, v_intModuleInst_2355_);
lean_ctor_set(v_reuseFailAlloc_2406_, 5, v_leInst_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2406_, 6, v_ltInst_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2406_, 7, v_lawfulOrderLTInst_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2406_, 8, v_isPreorderInst_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2406_, 9, v_orderedAddInst_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2406_, 10, v_isLinearInst_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2406_, 11, v_noNatDivInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2406_, 12, v_ringInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2406_, 13, v_commRingInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2406_, 14, v_orderedRingInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2406_, 15, v_fieldInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2406_, 16, v_charInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2406_, 17, v_zero_2368_);
lean_ctor_set(v_reuseFailAlloc_2406_, 18, v_ofNatZero_2369_);
lean_ctor_set(v_reuseFailAlloc_2406_, 19, v_one_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2406_, 20, v_leFn_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2406_, 21, v_ltFn_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2406_, 22, v_addFn_2373_);
lean_ctor_set(v_reuseFailAlloc_2406_, 23, v_zsmulFn_2374_);
lean_ctor_set(v_reuseFailAlloc_2406_, 24, v_nsmulFn_2375_);
lean_ctor_set(v_reuseFailAlloc_2406_, 25, v_zsmulFn_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2406_, 26, v_nsmulFn_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2406_, 27, v_homomulFn_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2406_, 28, v_subFn_2379_);
lean_ctor_set(v_reuseFailAlloc_2406_, 29, v_negFn_2380_);
lean_ctor_set(v_reuseFailAlloc_2406_, 30, v_vars_2381_);
lean_ctor_set(v_reuseFailAlloc_2406_, 31, v_varMap_2382_);
lean_ctor_set(v_reuseFailAlloc_2406_, 32, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2406_, 33, v_uppers_2384_);
lean_ctor_set(v_reuseFailAlloc_2406_, 34, v_diseqs_2385_);
lean_ctor_set(v_reuseFailAlloc_2406_, 35, v_assignment_2386_);
lean_ctor_set(v_reuseFailAlloc_2406_, 36, v_conflict_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2406_, 37, v_diseqSplits_2389_);
lean_ctor_set(v_reuseFailAlloc_2406_, 38, v_elimEqs_2390_);
lean_ctor_set(v_reuseFailAlloc_2406_, 39, v_elimStack_2391_);
lean_ctor_set(v_reuseFailAlloc_2406_, 40, v_occurs_2392_);
lean_ctor_set(v_reuseFailAlloc_2406_, 41, v_ignored_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*42, v_caseSplits_2387_);
v___x_2401_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_array_fset(v_xs_x27_2398_, v_a_2333_, v___x_2401_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2402_);
v___x_2404_ = v___x_2348_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_typeIdOf_2338_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_exprToStructId_2339_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_exprToStructIdEntries_2340_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v_forbiddenNatModules_2341_);
lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_natStructs_2342_);
lean_ctor_set(v_reuseFailAlloc_2405_, 6, v_natTypeIdOf_2343_);
lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_exprToNatStructId_2344_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2417_, lean_object* v_y_2418_, lean_object* v_fst_2419_, lean_object* v_s_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2417_, v_y_2418_, v_fst_2419_, v_s_2420_);
lean_dec(v_y_2418_);
lean_dec(v_a_2417_);
return v_res_2421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2423_, lean_object* v_x_2424_, lean_object* v_c_2425_, lean_object* v_y_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2474_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2474_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2474_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
uint8_t v___x_2444_; 
v___x_2444_ = lean_unbox(v_a_2440_);
lean_dec(v_a_2440_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
lean_del_object(v___x_2442_);
v___x_2445_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___y_2448_; lean_object* v_lowers_2456_; lean_object* v_size_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v_lowers_2456_ = lean_ctor_get(v_a_2446_, 32);
lean_inc_ref(v_lowers_2456_);
lean_dec(v_a_2446_);
v_size_2457_ = lean_ctor_get(v_lowers_2456_, 2);
v___x_2458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2459_ = lean_nat_dec_lt(v_y_2426_, v_size_2457_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref(v_lowers_2456_);
v___x_2460_ = l_outOfBounds___redArg(v___x_2458_);
v___y_2448_ = v___x_2460_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2458_, v_lowers_2456_, v_y_2426_);
lean_dec_ref(v_lowers_2456_);
v___y_2448_ = v___x_2461_;
goto v___jp_2447_;
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v_fst_2450_; lean_object* v_snd_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2449_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2424_, v___y_2448_);
lean_dec_ref(v___y_2448_);
v_fst_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_fst_2450_);
v_snd_2451_ = lean_ctor_get(v___x_2449_, 1);
lean_inc(v_snd_2451_);
lean_dec_ref(v___x_2449_);
lean_inc(v_a_2427_);
v___f_2452_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2452_, 0, v_a_2427_);
lean_closure_set(v___f_2452_, 1, v_y_2426_);
lean_closure_set(v___f_2452_, 2, v_fst_2450_);
v___x_2453_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2454_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2453_, v___f_2452_, v_a_2428_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref_known(v___x_2454_, 1);
v___x_2455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2423_, v_x_2424_, v_c_2425_, v_snd_2451_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_snd_2451_);
return v___x_2455_;
}
else
{
lean_dec(v_snd_2451_);
lean_dec_ref(v_c_2425_);
lean_dec(v_x_2424_);
lean_dec(v_a_2423_);
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_y_2426_);
lean_dec_ref(v_c_2425_);
lean_dec(v_x_2424_);
lean_dec(v_a_2423_);
v_a_2462_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2445_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2445_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v_y_2426_);
lean_dec_ref(v_c_2425_);
lean_dec(v_x_2424_);
lean_dec(v_a_2423_);
v___x_2470_ = lean_box(0);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2470_);
v___x_2472_ = v___x_2442_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
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
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_y_2426_);
lean_dec_ref(v_c_2425_);
lean_dec(v_x_2424_);
lean_dec(v_a_2423_);
v_a_2475_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2439_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2439_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2483_, lean_object* v_x_2484_, lean_object* v_c_2485_, lean_object* v_y_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2483_, v_x_2484_, v_c_2485_, v_y_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec(v_a_2487_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2500_, lean_object* v_y_2501_, lean_object* v_fst_2502_, lean_object* v_s_2503_){
_start:
{
lean_object* v_structs_2504_; lean_object* v_typeIdOf_2505_; lean_object* v_exprToStructId_2506_; lean_object* v_exprToStructIdEntries_2507_; lean_object* v_forbiddenNatModules_2508_; lean_object* v_natStructs_2509_; lean_object* v_natTypeIdOf_2510_; lean_object* v_exprToNatStructId_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_structs_2504_ = lean_ctor_get(v_s_2503_, 0);
v_typeIdOf_2505_ = lean_ctor_get(v_s_2503_, 1);
v_exprToStructId_2506_ = lean_ctor_get(v_s_2503_, 2);
v_exprToStructIdEntries_2507_ = lean_ctor_get(v_s_2503_, 3);
v_forbiddenNatModules_2508_ = lean_ctor_get(v_s_2503_, 4);
v_natStructs_2509_ = lean_ctor_get(v_s_2503_, 5);
v_natTypeIdOf_2510_ = lean_ctor_get(v_s_2503_, 6);
v_exprToNatStructId_2511_ = lean_ctor_get(v_s_2503_, 7);
v___x_2512_ = lean_array_get_size(v_structs_2504_);
v___x_2513_ = lean_nat_dec_lt(v_a_2500_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_dec_ref(v_fst_2502_);
return v_s_2503_;
}
else
{
lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2575_; 
lean_inc_ref(v_exprToNatStructId_2511_);
lean_inc_ref(v_natTypeIdOf_2510_);
lean_inc_ref(v_natStructs_2509_);
lean_inc_ref(v_forbiddenNatModules_2508_);
lean_inc_ref(v_exprToStructIdEntries_2507_);
lean_inc_ref(v_exprToStructId_2506_);
lean_inc_ref(v_typeIdOf_2505_);
lean_inc_ref(v_structs_2504_);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_s_2503_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; lean_object* v_unused_2577_; lean_object* v_unused_2578_; lean_object* v_unused_2579_; lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; 
v_unused_2576_ = lean_ctor_get(v_s_2503_, 7);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_s_2503_, 6);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_s_2503_, 5);
lean_dec(v_unused_2578_);
v_unused_2579_ = lean_ctor_get(v_s_2503_, 4);
lean_dec(v_unused_2579_);
v_unused_2580_ = lean_ctor_get(v_s_2503_, 3);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_s_2503_, 2);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_s_2503_, 1);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_s_2503_, 0);
lean_dec(v_unused_2583_);
v___x_2515_ = v_s_2503_;
v_isShared_2516_ = v_isSharedCheck_2575_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v_s_2503_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2575_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_v_2517_; lean_object* v_id_2518_; lean_object* v_ringId_x3f_2519_; lean_object* v_type_2520_; lean_object* v_u_2521_; lean_object* v_intModuleInst_2522_; lean_object* v_leInst_x3f_2523_; lean_object* v_ltInst_x3f_2524_; lean_object* v_lawfulOrderLTInst_x3f_2525_; lean_object* v_isPreorderInst_x3f_2526_; lean_object* v_orderedAddInst_x3f_2527_; lean_object* v_isLinearInst_x3f_2528_; lean_object* v_noNatDivInst_x3f_2529_; lean_object* v_ringInst_x3f_2530_; lean_object* v_commRingInst_x3f_2531_; lean_object* v_orderedRingInst_x3f_2532_; lean_object* v_fieldInst_x3f_2533_; lean_object* v_charInst_x3f_2534_; lean_object* v_zero_2535_; lean_object* v_ofNatZero_2536_; lean_object* v_one_x3f_2537_; lean_object* v_leFn_x3f_2538_; lean_object* v_ltFn_x3f_2539_; lean_object* v_addFn_2540_; lean_object* v_zsmulFn_2541_; lean_object* v_nsmulFn_2542_; lean_object* v_zsmulFn_x3f_2543_; lean_object* v_nsmulFn_x3f_2544_; lean_object* v_homomulFn_x3f_2545_; lean_object* v_subFn_2546_; lean_object* v_negFn_2547_; lean_object* v_vars_2548_; lean_object* v_varMap_2549_; lean_object* v_lowers_2550_; lean_object* v_uppers_2551_; lean_object* v_diseqs_2552_; lean_object* v_assignment_2553_; uint8_t v_caseSplits_2554_; lean_object* v_conflict_x3f_2555_; lean_object* v_diseqSplits_2556_; lean_object* v_elimEqs_2557_; lean_object* v_elimStack_2558_; lean_object* v_occurs_2559_; lean_object* v_ignored_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2574_; 
v_v_2517_ = lean_array_fget(v_structs_2504_, v_a_2500_);
v_id_2518_ = lean_ctor_get(v_v_2517_, 0);
v_ringId_x3f_2519_ = lean_ctor_get(v_v_2517_, 1);
v_type_2520_ = lean_ctor_get(v_v_2517_, 2);
v_u_2521_ = lean_ctor_get(v_v_2517_, 3);
v_intModuleInst_2522_ = lean_ctor_get(v_v_2517_, 4);
v_leInst_x3f_2523_ = lean_ctor_get(v_v_2517_, 5);
v_ltInst_x3f_2524_ = lean_ctor_get(v_v_2517_, 6);
v_lawfulOrderLTInst_x3f_2525_ = lean_ctor_get(v_v_2517_, 7);
v_isPreorderInst_x3f_2526_ = lean_ctor_get(v_v_2517_, 8);
v_orderedAddInst_x3f_2527_ = lean_ctor_get(v_v_2517_, 9);
v_isLinearInst_x3f_2528_ = lean_ctor_get(v_v_2517_, 10);
v_noNatDivInst_x3f_2529_ = lean_ctor_get(v_v_2517_, 11);
v_ringInst_x3f_2530_ = lean_ctor_get(v_v_2517_, 12);
v_commRingInst_x3f_2531_ = lean_ctor_get(v_v_2517_, 13);
v_orderedRingInst_x3f_2532_ = lean_ctor_get(v_v_2517_, 14);
v_fieldInst_x3f_2533_ = lean_ctor_get(v_v_2517_, 15);
v_charInst_x3f_2534_ = lean_ctor_get(v_v_2517_, 16);
v_zero_2535_ = lean_ctor_get(v_v_2517_, 17);
v_ofNatZero_2536_ = lean_ctor_get(v_v_2517_, 18);
v_one_x3f_2537_ = lean_ctor_get(v_v_2517_, 19);
v_leFn_x3f_2538_ = lean_ctor_get(v_v_2517_, 20);
v_ltFn_x3f_2539_ = lean_ctor_get(v_v_2517_, 21);
v_addFn_2540_ = lean_ctor_get(v_v_2517_, 22);
v_zsmulFn_2541_ = lean_ctor_get(v_v_2517_, 23);
v_nsmulFn_2542_ = lean_ctor_get(v_v_2517_, 24);
v_zsmulFn_x3f_2543_ = lean_ctor_get(v_v_2517_, 25);
v_nsmulFn_x3f_2544_ = lean_ctor_get(v_v_2517_, 26);
v_homomulFn_x3f_2545_ = lean_ctor_get(v_v_2517_, 27);
v_subFn_2546_ = lean_ctor_get(v_v_2517_, 28);
v_negFn_2547_ = lean_ctor_get(v_v_2517_, 29);
v_vars_2548_ = lean_ctor_get(v_v_2517_, 30);
v_varMap_2549_ = lean_ctor_get(v_v_2517_, 31);
v_lowers_2550_ = lean_ctor_get(v_v_2517_, 32);
v_uppers_2551_ = lean_ctor_get(v_v_2517_, 33);
v_diseqs_2552_ = lean_ctor_get(v_v_2517_, 34);
v_assignment_2553_ = lean_ctor_get(v_v_2517_, 35);
v_caseSplits_2554_ = lean_ctor_get_uint8(v_v_2517_, sizeof(void*)*42);
v_conflict_x3f_2555_ = lean_ctor_get(v_v_2517_, 36);
v_diseqSplits_2556_ = lean_ctor_get(v_v_2517_, 37);
v_elimEqs_2557_ = lean_ctor_get(v_v_2517_, 38);
v_elimStack_2558_ = lean_ctor_get(v_v_2517_, 39);
v_occurs_2559_ = lean_ctor_get(v_v_2517_, 40);
v_ignored_2560_ = lean_ctor_get(v_v_2517_, 41);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_v_2517_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2562_ = v_v_2517_;
v_isShared_2563_ = v_isSharedCheck_2574_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_ignored_2560_);
lean_inc(v_occurs_2559_);
lean_inc(v_elimStack_2558_);
lean_inc(v_elimEqs_2557_);
lean_inc(v_diseqSplits_2556_);
lean_inc(v_conflict_x3f_2555_);
lean_inc(v_assignment_2553_);
lean_inc(v_diseqs_2552_);
lean_inc(v_uppers_2551_);
lean_inc(v_lowers_2550_);
lean_inc(v_varMap_2549_);
lean_inc(v_vars_2548_);
lean_inc(v_negFn_2547_);
lean_inc(v_subFn_2546_);
lean_inc(v_homomulFn_x3f_2545_);
lean_inc(v_nsmulFn_x3f_2544_);
lean_inc(v_zsmulFn_x3f_2543_);
lean_inc(v_nsmulFn_2542_);
lean_inc(v_zsmulFn_2541_);
lean_inc(v_addFn_2540_);
lean_inc(v_ltFn_x3f_2539_);
lean_inc(v_leFn_x3f_2538_);
lean_inc(v_one_x3f_2537_);
lean_inc(v_ofNatZero_2536_);
lean_inc(v_zero_2535_);
lean_inc(v_charInst_x3f_2534_);
lean_inc(v_fieldInst_x3f_2533_);
lean_inc(v_orderedRingInst_x3f_2532_);
lean_inc(v_commRingInst_x3f_2531_);
lean_inc(v_ringInst_x3f_2530_);
lean_inc(v_noNatDivInst_x3f_2529_);
lean_inc(v_isLinearInst_x3f_2528_);
lean_inc(v_orderedAddInst_x3f_2527_);
lean_inc(v_isPreorderInst_x3f_2526_);
lean_inc(v_lawfulOrderLTInst_x3f_2525_);
lean_inc(v_ltInst_x3f_2524_);
lean_inc(v_leInst_x3f_2523_);
lean_inc(v_intModuleInst_2522_);
lean_inc(v_u_2521_);
lean_inc(v_type_2520_);
lean_inc(v_ringId_x3f_2519_);
lean_inc(v_id_2518_);
lean_dec(v_v_2517_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2574_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_xs_x27_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2564_ = lean_box(0);
v_xs_x27_2565_ = lean_array_fset(v_structs_2504_, v_a_2500_, v___x_2564_);
v___x_2566_ = l_Lean_PersistentArray_set___redArg(v_uppers_2551_, v_y_2501_, v_fst_2502_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 33, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_id_2518_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_ringId_x3f_2519_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_type_2520_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_u_2521_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_intModuleInst_2522_);
lean_ctor_set(v_reuseFailAlloc_2573_, 5, v_leInst_x3f_2523_);
lean_ctor_set(v_reuseFailAlloc_2573_, 6, v_ltInst_x3f_2524_);
lean_ctor_set(v_reuseFailAlloc_2573_, 7, v_lawfulOrderLTInst_x3f_2525_);
lean_ctor_set(v_reuseFailAlloc_2573_, 8, v_isPreorderInst_x3f_2526_);
lean_ctor_set(v_reuseFailAlloc_2573_, 9, v_orderedAddInst_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2573_, 10, v_isLinearInst_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2573_, 11, v_noNatDivInst_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2573_, 12, v_ringInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2573_, 13, v_commRingInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2573_, 14, v_orderedRingInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2573_, 15, v_fieldInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2573_, 16, v_charInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2573_, 17, v_zero_2535_);
lean_ctor_set(v_reuseFailAlloc_2573_, 18, v_ofNatZero_2536_);
lean_ctor_set(v_reuseFailAlloc_2573_, 19, v_one_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2573_, 20, v_leFn_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2573_, 21, v_ltFn_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2573_, 22, v_addFn_2540_);
lean_ctor_set(v_reuseFailAlloc_2573_, 23, v_zsmulFn_2541_);
lean_ctor_set(v_reuseFailAlloc_2573_, 24, v_nsmulFn_2542_);
lean_ctor_set(v_reuseFailAlloc_2573_, 25, v_zsmulFn_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2573_, 26, v_nsmulFn_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2573_, 27, v_homomulFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2573_, 28, v_subFn_2546_);
lean_ctor_set(v_reuseFailAlloc_2573_, 29, v_negFn_2547_);
lean_ctor_set(v_reuseFailAlloc_2573_, 30, v_vars_2548_);
lean_ctor_set(v_reuseFailAlloc_2573_, 31, v_varMap_2549_);
lean_ctor_set(v_reuseFailAlloc_2573_, 32, v_lowers_2550_);
lean_ctor_set(v_reuseFailAlloc_2573_, 33, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2573_, 34, v_diseqs_2552_);
lean_ctor_set(v_reuseFailAlloc_2573_, 35, v_assignment_2553_);
lean_ctor_set(v_reuseFailAlloc_2573_, 36, v_conflict_x3f_2555_);
lean_ctor_set(v_reuseFailAlloc_2573_, 37, v_diseqSplits_2556_);
lean_ctor_set(v_reuseFailAlloc_2573_, 38, v_elimEqs_2557_);
lean_ctor_set(v_reuseFailAlloc_2573_, 39, v_elimStack_2558_);
lean_ctor_set(v_reuseFailAlloc_2573_, 40, v_occurs_2559_);
lean_ctor_set(v_reuseFailAlloc_2573_, 41, v_ignored_2560_);
lean_ctor_set_uint8(v_reuseFailAlloc_2573_, sizeof(void*)*42, v_caseSplits_2554_);
v___x_2568_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_array_fset(v_xs_x27_2565_, v_a_2500_, v___x_2568_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2569_);
v___x_2571_ = v___x_2515_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_typeIdOf_2505_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_exprToStructId_2506_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_exprToStructIdEntries_2507_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_forbiddenNatModules_2508_);
lean_ctor_set(v_reuseFailAlloc_2572_, 5, v_natStructs_2509_);
lean_ctor_set(v_reuseFailAlloc_2572_, 6, v_natTypeIdOf_2510_);
lean_ctor_set(v_reuseFailAlloc_2572_, 7, v_exprToNatStructId_2511_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2584_, lean_object* v_y_2585_, lean_object* v_fst_2586_, lean_object* v_s_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2584_, v_y_2585_, v_fst_2586_, v_s_2587_);
lean_dec(v_y_2585_);
lean_dec(v_a_2584_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2589_, lean_object* v_x_2590_, lean_object* v_c_2591_, lean_object* v_y_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2640_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2640_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2640_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_del_object(v___x_2608_);
v___x_2611_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___y_2614_; lean_object* v_uppers_2622_; lean_object* v_size_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_uppers_2622_ = lean_ctor_get(v_a_2612_, 33);
lean_inc_ref(v_uppers_2622_);
lean_dec(v_a_2612_);
v_size_2623_ = lean_ctor_get(v_uppers_2622_, 2);
v___x_2624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2625_ = lean_nat_dec_lt(v_y_2592_, v_size_2623_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v_uppers_2622_);
v___x_2626_ = l_outOfBounds___redArg(v___x_2624_);
v___y_2614_ = v___x_2626_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2624_, v_uppers_2622_, v_y_2592_);
lean_dec_ref(v_uppers_2622_);
v___y_2614_ = v___x_2627_;
goto v___jp_2613_;
}
v___jp_2613_:
{
lean_object* v___x_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2590_, v___y_2614_);
lean_dec_ref(v___y_2614_);
v_fst_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v___x_2615_, 1);
lean_inc(v_snd_2617_);
lean_dec_ref(v___x_2615_);
lean_inc(v_a_2593_);
v___f_2618_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2618_, 0, v_a_2593_);
lean_closure_set(v___f_2618_, 1, v_y_2592_);
lean_closure_set(v___f_2618_, 2, v_fst_2616_);
v___x_2619_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2620_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2619_, v___f_2618_, v_a_2594_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2620_, 1);
v___x_2621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2589_, v_x_2590_, v_c_2591_, v_snd_2617_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_snd_2617_);
return v___x_2621_;
}
else
{
lean_dec(v_snd_2617_);
lean_dec_ref(v_c_2591_);
lean_dec(v_x_2590_);
lean_dec(v_a_2589_);
return v___x_2620_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v_y_2592_);
lean_dec_ref(v_c_2591_);
lean_dec(v_x_2590_);
lean_dec(v_a_2589_);
v_a_2628_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2611_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2611_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_dec(v_y_2592_);
lean_dec_ref(v_c_2591_);
lean_dec(v_x_2590_);
lean_dec(v_a_2589_);
v___x_2636_ = lean_box(0);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2636_);
v___x_2638_ = v___x_2608_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
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
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_y_2592_);
lean_dec_ref(v_c_2591_);
lean_dec(v_x_2590_);
lean_dec(v_a_2589_);
v_a_2641_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2605_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2605_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2649_, lean_object* v_x_2650_, lean_object* v_c_2651_, lean_object* v_y_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2649_, v_x_2650_, v_c_2651_, v_y_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2666_, lean_object* v_a_2667_, lean_object* v_s_2668_){
_start:
{
lean_object* v_structs_2669_; lean_object* v_typeIdOf_2670_; lean_object* v_exprToStructId_2671_; lean_object* v_exprToStructIdEntries_2672_; lean_object* v_forbiddenNatModules_2673_; lean_object* v_natStructs_2674_; lean_object* v_natTypeIdOf_2675_; lean_object* v_exprToNatStructId_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_structs_2669_ = lean_ctor_get(v_s_2668_, 0);
v_typeIdOf_2670_ = lean_ctor_get(v_s_2668_, 1);
v_exprToStructId_2671_ = lean_ctor_get(v_s_2668_, 2);
v_exprToStructIdEntries_2672_ = lean_ctor_get(v_s_2668_, 3);
v_forbiddenNatModules_2673_ = lean_ctor_get(v_s_2668_, 4);
v_natStructs_2674_ = lean_ctor_get(v_s_2668_, 5);
v_natTypeIdOf_2675_ = lean_ctor_get(v_s_2668_, 6);
v_exprToNatStructId_2676_ = lean_ctor_get(v_s_2668_, 7);
v___x_2677_ = lean_array_get_size(v_structs_2669_);
v___x_2678_ = lean_nat_dec_lt(v___y_2666_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v_a_2667_);
return v_s_2668_;
}
else
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2740_; 
lean_inc_ref(v_exprToNatStructId_2676_);
lean_inc_ref(v_natTypeIdOf_2675_);
lean_inc_ref(v_natStructs_2674_);
lean_inc_ref(v_forbiddenNatModules_2673_);
lean_inc_ref(v_exprToStructIdEntries_2672_);
lean_inc_ref(v_exprToStructId_2671_);
lean_inc_ref(v_typeIdOf_2670_);
lean_inc_ref(v_structs_2669_);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_s_2668_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; lean_object* v_unused_2742_; lean_object* v_unused_2743_; lean_object* v_unused_2744_; lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2741_ = lean_ctor_get(v_s_2668_, 7);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_s_2668_, 6);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_s_2668_, 5);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_s_2668_, 4);
lean_dec(v_unused_2744_);
v_unused_2745_ = lean_ctor_get(v_s_2668_, 3);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_s_2668_, 2);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_s_2668_, 1);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2668_, 0);
lean_dec(v_unused_2748_);
v___x_2680_ = v_s_2668_;
v_isShared_2681_ = v_isSharedCheck_2740_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v_s_2668_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2740_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_v_2682_; lean_object* v_id_2683_; lean_object* v_ringId_x3f_2684_; lean_object* v_type_2685_; lean_object* v_u_2686_; lean_object* v_intModuleInst_2687_; lean_object* v_leInst_x3f_2688_; lean_object* v_ltInst_x3f_2689_; lean_object* v_lawfulOrderLTInst_x3f_2690_; lean_object* v_isPreorderInst_x3f_2691_; lean_object* v_orderedAddInst_x3f_2692_; lean_object* v_isLinearInst_x3f_2693_; lean_object* v_noNatDivInst_x3f_2694_; lean_object* v_ringInst_x3f_2695_; lean_object* v_commRingInst_x3f_2696_; lean_object* v_orderedRingInst_x3f_2697_; lean_object* v_fieldInst_x3f_2698_; lean_object* v_charInst_x3f_2699_; lean_object* v_zero_2700_; lean_object* v_ofNatZero_2701_; lean_object* v_one_x3f_2702_; lean_object* v_leFn_x3f_2703_; lean_object* v_ltFn_x3f_2704_; lean_object* v_addFn_2705_; lean_object* v_zsmulFn_2706_; lean_object* v_nsmulFn_2707_; lean_object* v_zsmulFn_x3f_2708_; lean_object* v_nsmulFn_x3f_2709_; lean_object* v_homomulFn_x3f_2710_; lean_object* v_subFn_2711_; lean_object* v_negFn_2712_; lean_object* v_vars_2713_; lean_object* v_varMap_2714_; lean_object* v_lowers_2715_; lean_object* v_uppers_2716_; lean_object* v_diseqs_2717_; lean_object* v_assignment_2718_; uint8_t v_caseSplits_2719_; lean_object* v_conflict_x3f_2720_; lean_object* v_diseqSplits_2721_; lean_object* v_elimEqs_2722_; lean_object* v_elimStack_2723_; lean_object* v_occurs_2724_; lean_object* v_ignored_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2739_; 
v_v_2682_ = lean_array_fget(v_structs_2669_, v___y_2666_);
v_id_2683_ = lean_ctor_get(v_v_2682_, 0);
v_ringId_x3f_2684_ = lean_ctor_get(v_v_2682_, 1);
v_type_2685_ = lean_ctor_get(v_v_2682_, 2);
v_u_2686_ = lean_ctor_get(v_v_2682_, 3);
v_intModuleInst_2687_ = lean_ctor_get(v_v_2682_, 4);
v_leInst_x3f_2688_ = lean_ctor_get(v_v_2682_, 5);
v_ltInst_x3f_2689_ = lean_ctor_get(v_v_2682_, 6);
v_lawfulOrderLTInst_x3f_2690_ = lean_ctor_get(v_v_2682_, 7);
v_isPreorderInst_x3f_2691_ = lean_ctor_get(v_v_2682_, 8);
v_orderedAddInst_x3f_2692_ = lean_ctor_get(v_v_2682_, 9);
v_isLinearInst_x3f_2693_ = lean_ctor_get(v_v_2682_, 10);
v_noNatDivInst_x3f_2694_ = lean_ctor_get(v_v_2682_, 11);
v_ringInst_x3f_2695_ = lean_ctor_get(v_v_2682_, 12);
v_commRingInst_x3f_2696_ = lean_ctor_get(v_v_2682_, 13);
v_orderedRingInst_x3f_2697_ = lean_ctor_get(v_v_2682_, 14);
v_fieldInst_x3f_2698_ = lean_ctor_get(v_v_2682_, 15);
v_charInst_x3f_2699_ = lean_ctor_get(v_v_2682_, 16);
v_zero_2700_ = lean_ctor_get(v_v_2682_, 17);
v_ofNatZero_2701_ = lean_ctor_get(v_v_2682_, 18);
v_one_x3f_2702_ = lean_ctor_get(v_v_2682_, 19);
v_leFn_x3f_2703_ = lean_ctor_get(v_v_2682_, 20);
v_ltFn_x3f_2704_ = lean_ctor_get(v_v_2682_, 21);
v_addFn_2705_ = lean_ctor_get(v_v_2682_, 22);
v_zsmulFn_2706_ = lean_ctor_get(v_v_2682_, 23);
v_nsmulFn_2707_ = lean_ctor_get(v_v_2682_, 24);
v_zsmulFn_x3f_2708_ = lean_ctor_get(v_v_2682_, 25);
v_nsmulFn_x3f_2709_ = lean_ctor_get(v_v_2682_, 26);
v_homomulFn_x3f_2710_ = lean_ctor_get(v_v_2682_, 27);
v_subFn_2711_ = lean_ctor_get(v_v_2682_, 28);
v_negFn_2712_ = lean_ctor_get(v_v_2682_, 29);
v_vars_2713_ = lean_ctor_get(v_v_2682_, 30);
v_varMap_2714_ = lean_ctor_get(v_v_2682_, 31);
v_lowers_2715_ = lean_ctor_get(v_v_2682_, 32);
v_uppers_2716_ = lean_ctor_get(v_v_2682_, 33);
v_diseqs_2717_ = lean_ctor_get(v_v_2682_, 34);
v_assignment_2718_ = lean_ctor_get(v_v_2682_, 35);
v_caseSplits_2719_ = lean_ctor_get_uint8(v_v_2682_, sizeof(void*)*42);
v_conflict_x3f_2720_ = lean_ctor_get(v_v_2682_, 36);
v_diseqSplits_2721_ = lean_ctor_get(v_v_2682_, 37);
v_elimEqs_2722_ = lean_ctor_get(v_v_2682_, 38);
v_elimStack_2723_ = lean_ctor_get(v_v_2682_, 39);
v_occurs_2724_ = lean_ctor_get(v_v_2682_, 40);
v_ignored_2725_ = lean_ctor_get(v_v_2682_, 41);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_v_2682_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2727_ = v_v_2682_;
v_isShared_2728_ = v_isSharedCheck_2739_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_ignored_2725_);
lean_inc(v_occurs_2724_);
lean_inc(v_elimStack_2723_);
lean_inc(v_elimEqs_2722_);
lean_inc(v_diseqSplits_2721_);
lean_inc(v_conflict_x3f_2720_);
lean_inc(v_assignment_2718_);
lean_inc(v_diseqs_2717_);
lean_inc(v_uppers_2716_);
lean_inc(v_lowers_2715_);
lean_inc(v_varMap_2714_);
lean_inc(v_vars_2713_);
lean_inc(v_negFn_2712_);
lean_inc(v_subFn_2711_);
lean_inc(v_homomulFn_x3f_2710_);
lean_inc(v_nsmulFn_x3f_2709_);
lean_inc(v_zsmulFn_x3f_2708_);
lean_inc(v_nsmulFn_2707_);
lean_inc(v_zsmulFn_2706_);
lean_inc(v_addFn_2705_);
lean_inc(v_ltFn_x3f_2704_);
lean_inc(v_leFn_x3f_2703_);
lean_inc(v_one_x3f_2702_);
lean_inc(v_ofNatZero_2701_);
lean_inc(v_zero_2700_);
lean_inc(v_charInst_x3f_2699_);
lean_inc(v_fieldInst_x3f_2698_);
lean_inc(v_orderedRingInst_x3f_2697_);
lean_inc(v_commRingInst_x3f_2696_);
lean_inc(v_ringInst_x3f_2695_);
lean_inc(v_noNatDivInst_x3f_2694_);
lean_inc(v_isLinearInst_x3f_2693_);
lean_inc(v_orderedAddInst_x3f_2692_);
lean_inc(v_isPreorderInst_x3f_2691_);
lean_inc(v_lawfulOrderLTInst_x3f_2690_);
lean_inc(v_ltInst_x3f_2689_);
lean_inc(v_leInst_x3f_2688_);
lean_inc(v_intModuleInst_2687_);
lean_inc(v_u_2686_);
lean_inc(v_type_2685_);
lean_inc(v_ringId_x3f_2684_);
lean_inc(v_id_2683_);
lean_dec(v_v_2682_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2739_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_xs_x27_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2729_ = lean_box(0);
v_xs_x27_2730_ = lean_array_fset(v_structs_2669_, v___y_2666_, v___x_2729_);
v___x_2731_ = l_Lean_PersistentArray_push___redArg(v_ignored_2725_, v_a_2667_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 41, v___x_2731_);
v___x_2733_ = v___x_2727_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_id_2683_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_ringId_x3f_2684_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_type_2685_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_u_2686_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v_intModuleInst_2687_);
lean_ctor_set(v_reuseFailAlloc_2738_, 5, v_leInst_x3f_2688_);
lean_ctor_set(v_reuseFailAlloc_2738_, 6, v_ltInst_x3f_2689_);
lean_ctor_set(v_reuseFailAlloc_2738_, 7, v_lawfulOrderLTInst_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2738_, 8, v_isPreorderInst_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2738_, 9, v_orderedAddInst_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2738_, 10, v_isLinearInst_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2738_, 11, v_noNatDivInst_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2738_, 12, v_ringInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2738_, 13, v_commRingInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2738_, 14, v_orderedRingInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2738_, 15, v_fieldInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2738_, 16, v_charInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2738_, 17, v_zero_2700_);
lean_ctor_set(v_reuseFailAlloc_2738_, 18, v_ofNatZero_2701_);
lean_ctor_set(v_reuseFailAlloc_2738_, 19, v_one_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2738_, 20, v_leFn_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2738_, 21, v_ltFn_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2738_, 22, v_addFn_2705_);
lean_ctor_set(v_reuseFailAlloc_2738_, 23, v_zsmulFn_2706_);
lean_ctor_set(v_reuseFailAlloc_2738_, 24, v_nsmulFn_2707_);
lean_ctor_set(v_reuseFailAlloc_2738_, 25, v_zsmulFn_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2738_, 26, v_nsmulFn_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2738_, 27, v_homomulFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2738_, 28, v_subFn_2711_);
lean_ctor_set(v_reuseFailAlloc_2738_, 29, v_negFn_2712_);
lean_ctor_set(v_reuseFailAlloc_2738_, 30, v_vars_2713_);
lean_ctor_set(v_reuseFailAlloc_2738_, 31, v_varMap_2714_);
lean_ctor_set(v_reuseFailAlloc_2738_, 32, v_lowers_2715_);
lean_ctor_set(v_reuseFailAlloc_2738_, 33, v_uppers_2716_);
lean_ctor_set(v_reuseFailAlloc_2738_, 34, v_diseqs_2717_);
lean_ctor_set(v_reuseFailAlloc_2738_, 35, v_assignment_2718_);
lean_ctor_set(v_reuseFailAlloc_2738_, 36, v_conflict_x3f_2720_);
lean_ctor_set(v_reuseFailAlloc_2738_, 37, v_diseqSplits_2721_);
lean_ctor_set(v_reuseFailAlloc_2738_, 38, v_elimEqs_2722_);
lean_ctor_set(v_reuseFailAlloc_2738_, 39, v_elimStack_2723_);
lean_ctor_set(v_reuseFailAlloc_2738_, 40, v_occurs_2724_);
lean_ctor_set(v_reuseFailAlloc_2738_, 41, v___x_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, sizeof(void*)*42, v_caseSplits_2719_);
v___x_2733_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_array_fset(v_xs_x27_2730_, v___y_2666_, v___x_2733_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2734_);
v___x_2736_ = v___x_2680_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_typeIdOf_2670_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_exprToStructId_2671_);
lean_ctor_set(v_reuseFailAlloc_2737_, 3, v_exprToStructIdEntries_2672_);
lean_ctor_set(v_reuseFailAlloc_2737_, 4, v_forbiddenNatModules_2673_);
lean_ctor_set(v_reuseFailAlloc_2737_, 5, v_natStructs_2674_);
lean_ctor_set(v_reuseFailAlloc_2737_, 6, v_natTypeIdOf_2675_);
lean_ctor_set(v_reuseFailAlloc_2737_, 7, v_exprToNatStructId_2676_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2749_, lean_object* v_a_2750_, lean_object* v_s_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2749_, v_a_2750_, v_s_2751_);
lean_dec(v___y_2749_);
return v_res_2752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_cls_2760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2762_ = l_Lean_Name_append(v___x_2761_, v_cls_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_toCold_2801_; lean_object* v_options_2802_; uint8_t v_hasTrace_2803_; 
v_toCold_2801_ = lean_ctor_get(v_a_2773_, 0);
v_options_2802_ = lean_ctor_get(v_toCold_2801_, 2);
v_hasTrace_2803_ = lean_ctor_get_uint8(v_options_2802_, sizeof(void*)*1);
if (v_hasTrace_2803_ == 0)
{
v___y_2777_ = v_a_2764_;
v___y_2778_ = v_a_2765_;
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
goto v___jp_2776_;
}
else
{
lean_object* v_inheritedTraceOptions_2804_; lean_object* v_cls_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_inheritedTraceOptions_2804_ = lean_ctor_get(v_toCold_2801_, 11);
v_cls_2805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2804_, v_options_2802_, v___x_2806_);
if (v___x_2807_ == 0)
{
v___y_2777_ = v_a_2764_;
v___y_2778_ = v_a_2765_;
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_MessageData_ofExpr(v_a_2809_);
v___x_2811_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2805_, v___x_2810_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_dec_ref_known(v___x_2811_, 1);
v___y_2777_ = v_a_2764_;
v___y_2778_ = v_a_2765_;
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
goto v___jp_2776_;
}
else
{
return v___x_2811_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_a_2812_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2808_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2808_);
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
v___jp_2776_:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2763_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
lean_inc(v___y_2777_);
v___f_2790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2790_, 0, v___y_2777_);
lean_closure_set(v___f_2790_, 1, v_a_2789_);
v___x_2791_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2792_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2791_, v___f_2790_, v___y_2778_);
return v___x_2792_;
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2788_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2788_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_c_2820_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_p_2847_; lean_object* v_toCold_2848_; lean_object* v_currRecDepth_2849_; lean_object* v_ref_2850_; uint8_t v_diag_2851_; uint8_t v_suppressElabErrors_2852_; lean_object* v_maxRecDepth_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_p_2847_ = lean_ctor_get(v_c_u2082_2834_, 0);
v_toCold_2848_ = lean_ctor_get(v_a_2844_, 0);
lean_inc_ref(v_toCold_2848_);
v_currRecDepth_2849_ = lean_ctor_get(v_a_2844_, 1);
lean_inc(v_currRecDepth_2849_);
v_ref_2850_ = lean_ctor_get(v_a_2844_, 2);
lean_inc(v_ref_2850_);
v_diag_2851_ = lean_ctor_get_uint8(v_a_2844_, sizeof(void*)*3);
v_suppressElabErrors_2852_ = lean_ctor_get_uint8(v_a_2844_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_2844_);
v_maxRecDepth_2904_ = lean_ctor_get(v_toCold_2848_, 3);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_nat_dec_eq(v_maxRecDepth_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_nat_dec_eq(v_currRecDepth_2849_, v_maxRecDepth_2904_);
if (v___x_2907_ == 0)
{
goto v___jp_2853_;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v_currRecDepth_2849_);
lean_dec_ref(v_toCold_2848_);
lean_dec_ref(v_c_u2082_2834_);
v___x_2908_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2850_);
return v___x_2908_;
}
}
else
{
goto v___jp_2853_;
}
v___jp_2853_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_add(v_currRecDepth_2849_, v___x_2854_);
lean_dec(v_currRecDepth_2849_);
v___x_2856_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2856_, 0, v_toCold_2848_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
lean_ctor_set(v___x_2856_, 2, v_ref_2850_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*3, v_diag_2851_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*3 + 1, v_suppressElabErrors_2852_);
v___x_2857_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2847_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v___x_2856_, v_a_2845_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2895_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2895_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2895_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
if (lean_obj_tag(v_a_2858_) == 1)
{
lean_object* v_val_2862_; lean_object* v_snd_2863_; lean_object* v_snd_2864_; lean_object* v_fst_2865_; lean_object* v_fst_2866_; lean_object* v_p_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_del_object(v___x_2860_);
v_val_2862_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v_a_2858_, 1);
v_snd_2863_ = lean_ctor_get(v_val_2862_, 1);
lean_inc(v_snd_2863_);
v_snd_2864_ = lean_ctor_get(v_snd_2863_, 1);
lean_inc(v_snd_2864_);
v_fst_2865_ = lean_ctor_get(v_val_2862_, 0);
lean_inc(v_fst_2865_);
lean_dec(v_val_2862_);
v_fst_2866_ = lean_ctor_get(v_snd_2863_, 0);
lean_inc(v_fst_2866_);
lean_dec(v_snd_2863_);
v_p_2867_ = lean_ctor_get(v_snd_2864_, 0);
v___x_2868_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2867_, v_fst_2866_);
lean_inc_ref(v_c_u2082_2834_);
v___x_2869_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2868_, v_fst_2866_, v_snd_2864_, v_fst_2865_, v_c_u2082_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v___x_2856_, v_a_2845_);
lean_dec(v_fst_2866_);
lean_dec(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
if (lean_obj_tag(v_a_2870_) == 1)
{
lean_object* v_val_2871_; 
lean_dec_ref(v_c_u2082_2834_);
v_val_2871_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_a_2870_, 1);
v_c_u2082_2834_ = v_val_2871_;
v_a_2844_ = v___x_2856_;
goto _start;
}
else
{
lean_object* v___x_2873_; 
lean_dec(v_a_2870_);
v___x_2873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v___x_2856_, v_a_2845_);
lean_dec_ref_known(v___x_2856_, 3);
lean_dec_ref(v_c_u2082_2834_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2881_; 
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2882_);
v___x_2875_ = v___x_2873_;
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v___x_2873_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = lean_box(0);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2877_);
v___x_2879_ = v___x_2875_;
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
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2873_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2873_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2856_, 3);
lean_dec_ref(v_c_u2082_2834_);
return v___x_2869_;
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_dec(v_a_2858_);
lean_dec_ref_known(v___x_2856_, 3);
v___x_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_c_u2082_2834_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2891_);
v___x_2893_ = v___x_2860_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
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
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref_known(v___x_2856_, 3);
lean_dec_ref(v_c_u2082_2834_);
v_a_2896_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2857_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2857_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec(v_a_2910_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2923_, lean_object* v_x_2924_, size_t v_x_2925_, size_t v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
lean_object* v_cs_2927_; size_t v_j_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_cs_2927_ = lean_ctor_get(v_x_2924_, 0);
v_j_2928_ = lean_usize_shift_right(v_x_2925_, v_x_2926_);
v___x_2929_ = lean_usize_to_nat(v_j_2928_);
v___x_2930_ = lean_array_get_size(v_cs_2927_);
v___x_2931_ = lean_nat_dec_lt(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_dec(v___x_2929_);
lean_dec_ref(v_val_2923_);
return v_x_2924_;
}
else
{
lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2949_; 
lean_inc_ref(v_cs_2927_);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_x_2924_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; 
v_unused_2950_ = lean_ctor_get(v_x_2924_, 0);
lean_dec(v_unused_2950_);
v___x_2933_ = v_x_2924_;
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
else
{
lean_dec(v_x_2924_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
size_t v___x_2935_; size_t v___x_2936_; size_t v___x_2937_; size_t v_i_2938_; size_t v___x_2939_; size_t v_shift_2940_; lean_object* v_v_2941_; lean_object* v___x_2942_; lean_object* v_xs_x27_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2935_ = ((size_t)1ULL);
v___x_2936_ = lean_usize_shift_left(v___x_2935_, v_x_2926_);
v___x_2937_ = lean_usize_sub(v___x_2936_, v___x_2935_);
v_i_2938_ = lean_usize_land(v_x_2925_, v___x_2937_);
v___x_2939_ = ((size_t)5ULL);
v_shift_2940_ = lean_usize_sub(v_x_2926_, v___x_2939_);
v_v_2941_ = lean_array_fget(v_cs_2927_, v___x_2929_);
v___x_2942_ = lean_box(0);
v_xs_x27_2943_ = lean_array_fset(v_cs_2927_, v___x_2929_, v___x_2942_);
v___x_2944_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2923_, v_v_2941_, v_i_2938_, v_shift_2940_);
v___x_2945_ = lean_array_fset(v_xs_x27_2943_, v___x_2929_, v___x_2944_);
lean_dec(v___x_2929_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2945_);
v___x_2947_ = v___x_2933_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_vs_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_vs_2951_ = lean_ctor_get(v_x_2924_, 0);
v___x_2952_ = lean_usize_to_nat(v_x_2925_);
v___x_2953_ = lean_array_get_size(v_vs_2951_);
v___x_2954_ = lean_nat_dec_lt(v___x_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v___x_2952_);
lean_dec_ref(v_val_2923_);
return v_x_2924_;
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2966_; 
lean_inc_ref(v_vs_2951_);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_x_2924_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; 
v_unused_2967_ = lean_ctor_get(v_x_2924_, 0);
lean_dec(v_unused_2967_);
v___x_2956_ = v_x_2924_;
v_isShared_2957_ = v_isSharedCheck_2966_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_x_2924_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2966_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_v_2958_; lean_object* v___x_2959_; lean_object* v_xs_x27_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v_v_2958_ = lean_array_fget(v_vs_2951_, v___x_2952_);
v___x_2959_ = lean_box(0);
v_xs_x27_2960_ = lean_array_fset(v_vs_2951_, v___x_2952_, v___x_2959_);
v___x_2961_ = l_Lean_PersistentArray_push___redArg(v_v_2958_, v_val_2923_);
v___x_2962_ = lean_array_fset(v_xs_x27_2960_, v___x_2952_, v___x_2961_);
lean_dec(v___x_2952_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2962_);
v___x_2964_ = v___x_2956_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2968_, lean_object* v_x_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
size_t v_x_41196__boxed_2972_; size_t v_x_41197__boxed_2973_; lean_object* v_res_2974_; 
v_x_41196__boxed_2972_ = lean_unbox_usize(v_x_2970_);
lean_dec(v_x_2970_);
v_x_41197__boxed_2973_ = lean_unbox_usize(v_x_2971_);
lean_dec(v_x_2971_);
v_res_2974_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2968_, v_x_2969_, v_x_41196__boxed_2972_, v_x_41197__boxed_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2975_, lean_object* v_t_2976_, lean_object* v_i_2977_){
_start:
{
lean_object* v_root_2978_; lean_object* v_tail_2979_; lean_object* v_size_2980_; size_t v_shift_2981_; lean_object* v_tailOff_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3006_; 
v_root_2978_ = lean_ctor_get(v_t_2976_, 0);
v_tail_2979_ = lean_ctor_get(v_t_2976_, 1);
v_size_2980_ = lean_ctor_get(v_t_2976_, 2);
v_shift_2981_ = lean_ctor_get_usize(v_t_2976_, 4);
v_tailOff_2982_ = lean_ctor_get(v_t_2976_, 3);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_t_2976_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2984_ = v_t_2976_;
v_isShared_2985_ = v_isSharedCheck_3006_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_tailOff_2982_);
lean_inc(v_size_2980_);
lean_inc(v_tail_2979_);
lean_inc(v_root_2978_);
lean_dec(v_t_2976_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3006_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_nat_dec_le(v_tailOff_2982_, v_i_2977_);
if (v___x_2986_ == 0)
{
size_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2987_ = lean_usize_of_nat(v_i_2977_);
v___x_2988_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2975_, v_root_2978_, v___x_2987_, v_shift_2981_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2988_);
v___x_2990_ = v___x_2984_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_tail_2979_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_size_2980_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_tailOff_2982_);
lean_ctor_set_usize(v_reuseFailAlloc_2991_, 4, v_shift_2981_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2992_ = lean_nat_sub(v_i_2977_, v_tailOff_2982_);
v___x_2993_ = lean_array_get_size(v_tail_2979_);
v___x_2994_ = lean_nat_dec_lt(v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v___x_2992_);
lean_dec_ref(v_val_2975_);
if (v_isShared_2985_ == 0)
{
v___x_2996_ = v___x_2984_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_root_2978_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_tail_2979_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_size_2980_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v_tailOff_2982_);
lean_ctor_set_usize(v_reuseFailAlloc_2997_, 4, v_shift_2981_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
else
{
lean_object* v_v_2998_; lean_object* v___x_2999_; lean_object* v_xs_x27_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v_v_2998_ = lean_array_fget(v_tail_2979_, v___x_2992_);
v___x_2999_ = lean_box(0);
v_xs_x27_3000_ = lean_array_fset(v_tail_2979_, v___x_2992_, v___x_2999_);
v___x_3001_ = l_Lean_PersistentArray_push___redArg(v_v_2998_, v_val_2975_);
v___x_3002_ = lean_array_fset(v_xs_x27_3000_, v___x_2992_, v___x_3001_);
lean_dec(v___x_2992_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_3002_);
v___x_3004_ = v___x_2984_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_root_2978_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_size_2980_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_tailOff_2982_);
lean_ctor_set_usize(v_reuseFailAlloc_3005_, 4, v_shift_2981_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3007_, lean_object* v_t_3008_, lean_object* v_i_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3007_, v_t_3008_, v_i_3009_);
lean_dec(v_i_3009_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3011_, lean_object* v_val_3012_, lean_object* v_v_3013_, lean_object* v_s_3014_){
_start:
{
lean_object* v_structs_3015_; lean_object* v_typeIdOf_3016_; lean_object* v_exprToStructId_3017_; lean_object* v_exprToStructIdEntries_3018_; lean_object* v_forbiddenNatModules_3019_; lean_object* v_natStructs_3020_; lean_object* v_natTypeIdOf_3021_; lean_object* v_exprToNatStructId_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v_structs_3015_ = lean_ctor_get(v_s_3014_, 0);
v_typeIdOf_3016_ = lean_ctor_get(v_s_3014_, 1);
v_exprToStructId_3017_ = lean_ctor_get(v_s_3014_, 2);
v_exprToStructIdEntries_3018_ = lean_ctor_get(v_s_3014_, 3);
v_forbiddenNatModules_3019_ = lean_ctor_get(v_s_3014_, 4);
v_natStructs_3020_ = lean_ctor_get(v_s_3014_, 5);
v_natTypeIdOf_3021_ = lean_ctor_get(v_s_3014_, 6);
v_exprToNatStructId_3022_ = lean_ctor_get(v_s_3014_, 7);
v___x_3023_ = lean_array_get_size(v_structs_3015_);
v___x_3024_ = lean_nat_dec_lt(v___y_3011_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec_ref(v_val_3012_);
return v_s_3014_;
}
else
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3086_; 
lean_inc_ref(v_exprToNatStructId_3022_);
lean_inc_ref(v_natTypeIdOf_3021_);
lean_inc_ref(v_natStructs_3020_);
lean_inc_ref(v_forbiddenNatModules_3019_);
lean_inc_ref(v_exprToStructIdEntries_3018_);
lean_inc_ref(v_exprToStructId_3017_);
lean_inc_ref(v_typeIdOf_3016_);
lean_inc_ref(v_structs_3015_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_s_3014_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; lean_object* v_unused_3089_; lean_object* v_unused_3090_; lean_object* v_unused_3091_; lean_object* v_unused_3092_; lean_object* v_unused_3093_; lean_object* v_unused_3094_; 
v_unused_3087_ = lean_ctor_get(v_s_3014_, 7);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_s_3014_, 6);
lean_dec(v_unused_3088_);
v_unused_3089_ = lean_ctor_get(v_s_3014_, 5);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v_s_3014_, 4);
lean_dec(v_unused_3090_);
v_unused_3091_ = lean_ctor_get(v_s_3014_, 3);
lean_dec(v_unused_3091_);
v_unused_3092_ = lean_ctor_get(v_s_3014_, 2);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_s_3014_, 1);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_s_3014_, 0);
lean_dec(v_unused_3094_);
v___x_3026_ = v_s_3014_;
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_s_3014_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_v_3028_; lean_object* v_id_3029_; lean_object* v_ringId_x3f_3030_; lean_object* v_type_3031_; lean_object* v_u_3032_; lean_object* v_intModuleInst_3033_; lean_object* v_leInst_x3f_3034_; lean_object* v_ltInst_x3f_3035_; lean_object* v_lawfulOrderLTInst_x3f_3036_; lean_object* v_isPreorderInst_x3f_3037_; lean_object* v_orderedAddInst_x3f_3038_; lean_object* v_isLinearInst_x3f_3039_; lean_object* v_noNatDivInst_x3f_3040_; lean_object* v_ringInst_x3f_3041_; lean_object* v_commRingInst_x3f_3042_; lean_object* v_orderedRingInst_x3f_3043_; lean_object* v_fieldInst_x3f_3044_; lean_object* v_charInst_x3f_3045_; lean_object* v_zero_3046_; lean_object* v_ofNatZero_3047_; lean_object* v_one_x3f_3048_; lean_object* v_leFn_x3f_3049_; lean_object* v_ltFn_x3f_3050_; lean_object* v_addFn_3051_; lean_object* v_zsmulFn_3052_; lean_object* v_nsmulFn_3053_; lean_object* v_zsmulFn_x3f_3054_; lean_object* v_nsmulFn_x3f_3055_; lean_object* v_homomulFn_x3f_3056_; lean_object* v_subFn_3057_; lean_object* v_negFn_3058_; lean_object* v_vars_3059_; lean_object* v_varMap_3060_; lean_object* v_lowers_3061_; lean_object* v_uppers_3062_; lean_object* v_diseqs_3063_; lean_object* v_assignment_3064_; uint8_t v_caseSplits_3065_; lean_object* v_conflict_x3f_3066_; lean_object* v_diseqSplits_3067_; lean_object* v_elimEqs_3068_; lean_object* v_elimStack_3069_; lean_object* v_occurs_3070_; lean_object* v_ignored_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3085_; 
v_v_3028_ = lean_array_fget(v_structs_3015_, v___y_3011_);
v_id_3029_ = lean_ctor_get(v_v_3028_, 0);
v_ringId_x3f_3030_ = lean_ctor_get(v_v_3028_, 1);
v_type_3031_ = lean_ctor_get(v_v_3028_, 2);
v_u_3032_ = lean_ctor_get(v_v_3028_, 3);
v_intModuleInst_3033_ = lean_ctor_get(v_v_3028_, 4);
v_leInst_x3f_3034_ = lean_ctor_get(v_v_3028_, 5);
v_ltInst_x3f_3035_ = lean_ctor_get(v_v_3028_, 6);
v_lawfulOrderLTInst_x3f_3036_ = lean_ctor_get(v_v_3028_, 7);
v_isPreorderInst_x3f_3037_ = lean_ctor_get(v_v_3028_, 8);
v_orderedAddInst_x3f_3038_ = lean_ctor_get(v_v_3028_, 9);
v_isLinearInst_x3f_3039_ = lean_ctor_get(v_v_3028_, 10);
v_noNatDivInst_x3f_3040_ = lean_ctor_get(v_v_3028_, 11);
v_ringInst_x3f_3041_ = lean_ctor_get(v_v_3028_, 12);
v_commRingInst_x3f_3042_ = lean_ctor_get(v_v_3028_, 13);
v_orderedRingInst_x3f_3043_ = lean_ctor_get(v_v_3028_, 14);
v_fieldInst_x3f_3044_ = lean_ctor_get(v_v_3028_, 15);
v_charInst_x3f_3045_ = lean_ctor_get(v_v_3028_, 16);
v_zero_3046_ = lean_ctor_get(v_v_3028_, 17);
v_ofNatZero_3047_ = lean_ctor_get(v_v_3028_, 18);
v_one_x3f_3048_ = lean_ctor_get(v_v_3028_, 19);
v_leFn_x3f_3049_ = lean_ctor_get(v_v_3028_, 20);
v_ltFn_x3f_3050_ = lean_ctor_get(v_v_3028_, 21);
v_addFn_3051_ = lean_ctor_get(v_v_3028_, 22);
v_zsmulFn_3052_ = lean_ctor_get(v_v_3028_, 23);
v_nsmulFn_3053_ = lean_ctor_get(v_v_3028_, 24);
v_zsmulFn_x3f_3054_ = lean_ctor_get(v_v_3028_, 25);
v_nsmulFn_x3f_3055_ = lean_ctor_get(v_v_3028_, 26);
v_homomulFn_x3f_3056_ = lean_ctor_get(v_v_3028_, 27);
v_subFn_3057_ = lean_ctor_get(v_v_3028_, 28);
v_negFn_3058_ = lean_ctor_get(v_v_3028_, 29);
v_vars_3059_ = lean_ctor_get(v_v_3028_, 30);
v_varMap_3060_ = lean_ctor_get(v_v_3028_, 31);
v_lowers_3061_ = lean_ctor_get(v_v_3028_, 32);
v_uppers_3062_ = lean_ctor_get(v_v_3028_, 33);
v_diseqs_3063_ = lean_ctor_get(v_v_3028_, 34);
v_assignment_3064_ = lean_ctor_get(v_v_3028_, 35);
v_caseSplits_3065_ = lean_ctor_get_uint8(v_v_3028_, sizeof(void*)*42);
v_conflict_x3f_3066_ = lean_ctor_get(v_v_3028_, 36);
v_diseqSplits_3067_ = lean_ctor_get(v_v_3028_, 37);
v_elimEqs_3068_ = lean_ctor_get(v_v_3028_, 38);
v_elimStack_3069_ = lean_ctor_get(v_v_3028_, 39);
v_occurs_3070_ = lean_ctor_get(v_v_3028_, 40);
v_ignored_3071_ = lean_ctor_get(v_v_3028_, 41);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_v_3028_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3073_ = v_v_3028_;
v_isShared_3074_ = v_isSharedCheck_3085_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_ignored_3071_);
lean_inc(v_occurs_3070_);
lean_inc(v_elimStack_3069_);
lean_inc(v_elimEqs_3068_);
lean_inc(v_diseqSplits_3067_);
lean_inc(v_conflict_x3f_3066_);
lean_inc(v_assignment_3064_);
lean_inc(v_diseqs_3063_);
lean_inc(v_uppers_3062_);
lean_inc(v_lowers_3061_);
lean_inc(v_varMap_3060_);
lean_inc(v_vars_3059_);
lean_inc(v_negFn_3058_);
lean_inc(v_subFn_3057_);
lean_inc(v_homomulFn_x3f_3056_);
lean_inc(v_nsmulFn_x3f_3055_);
lean_inc(v_zsmulFn_x3f_3054_);
lean_inc(v_nsmulFn_3053_);
lean_inc(v_zsmulFn_3052_);
lean_inc(v_addFn_3051_);
lean_inc(v_ltFn_x3f_3050_);
lean_inc(v_leFn_x3f_3049_);
lean_inc(v_one_x3f_3048_);
lean_inc(v_ofNatZero_3047_);
lean_inc(v_zero_3046_);
lean_inc(v_charInst_x3f_3045_);
lean_inc(v_fieldInst_x3f_3044_);
lean_inc(v_orderedRingInst_x3f_3043_);
lean_inc(v_commRingInst_x3f_3042_);
lean_inc(v_ringInst_x3f_3041_);
lean_inc(v_noNatDivInst_x3f_3040_);
lean_inc(v_isLinearInst_x3f_3039_);
lean_inc(v_orderedAddInst_x3f_3038_);
lean_inc(v_isPreorderInst_x3f_3037_);
lean_inc(v_lawfulOrderLTInst_x3f_3036_);
lean_inc(v_ltInst_x3f_3035_);
lean_inc(v_leInst_x3f_3034_);
lean_inc(v_intModuleInst_3033_);
lean_inc(v_u_3032_);
lean_inc(v_type_3031_);
lean_inc(v_ringId_x3f_3030_);
lean_inc(v_id_3029_);
lean_dec(v_v_3028_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3085_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v_xs_x27_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3075_ = lean_box(0);
v_xs_x27_3076_ = lean_array_fset(v_structs_3015_, v___y_3011_, v___x_3075_);
v___x_3077_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3012_, v_diseqs_3063_, v_v_3013_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 34, v___x_3077_);
v___x_3079_ = v___x_3073_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_id_3029_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_ringId_x3f_3030_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_type_3031_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_u_3032_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_intModuleInst_3033_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_leInst_x3f_3034_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_ltInst_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_lawfulOrderLTInst_x3f_3036_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_isPreorderInst_x3f_3037_);
lean_ctor_set(v_reuseFailAlloc_3084_, 9, v_orderedAddInst_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3084_, 10, v_isLinearInst_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3084_, 11, v_noNatDivInst_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3084_, 12, v_ringInst_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3084_, 13, v_commRingInst_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3084_, 14, v_orderedRingInst_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3084_, 15, v_fieldInst_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3084_, 16, v_charInst_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3084_, 17, v_zero_3046_);
lean_ctor_set(v_reuseFailAlloc_3084_, 18, v_ofNatZero_3047_);
lean_ctor_set(v_reuseFailAlloc_3084_, 19, v_one_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3084_, 20, v_leFn_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3084_, 21, v_ltFn_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3084_, 22, v_addFn_3051_);
lean_ctor_set(v_reuseFailAlloc_3084_, 23, v_zsmulFn_3052_);
lean_ctor_set(v_reuseFailAlloc_3084_, 24, v_nsmulFn_3053_);
lean_ctor_set(v_reuseFailAlloc_3084_, 25, v_zsmulFn_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3084_, 26, v_nsmulFn_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3084_, 27, v_homomulFn_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3084_, 28, v_subFn_3057_);
lean_ctor_set(v_reuseFailAlloc_3084_, 29, v_negFn_3058_);
lean_ctor_set(v_reuseFailAlloc_3084_, 30, v_vars_3059_);
lean_ctor_set(v_reuseFailAlloc_3084_, 31, v_varMap_3060_);
lean_ctor_set(v_reuseFailAlloc_3084_, 32, v_lowers_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 33, v_uppers_3062_);
lean_ctor_set(v_reuseFailAlloc_3084_, 34, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3084_, 35, v_assignment_3064_);
lean_ctor_set(v_reuseFailAlloc_3084_, 36, v_conflict_x3f_3066_);
lean_ctor_set(v_reuseFailAlloc_3084_, 37, v_diseqSplits_3067_);
lean_ctor_set(v_reuseFailAlloc_3084_, 38, v_elimEqs_3068_);
lean_ctor_set(v_reuseFailAlloc_3084_, 39, v_elimStack_3069_);
lean_ctor_set(v_reuseFailAlloc_3084_, 40, v_occurs_3070_);
lean_ctor_set(v_reuseFailAlloc_3084_, 41, v_ignored_3071_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*42, v_caseSplits_3065_);
v___x_3079_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_array_fset(v_xs_x27_3076_, v___y_3011_, v___x_3079_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3080_);
v___x_3082_ = v___x_3026_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_typeIdOf_3016_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_exprToStructId_3017_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_exprToStructIdEntries_3018_);
lean_ctor_set(v_reuseFailAlloc_3083_, 4, v_forbiddenNatModules_3019_);
lean_ctor_set(v_reuseFailAlloc_3083_, 5, v_natStructs_3020_);
lean_ctor_set(v_reuseFailAlloc_3083_, 6, v_natTypeIdOf_3021_);
lean_ctor_set(v_reuseFailAlloc_3083_, 7, v_exprToNatStructId_3022_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3095_, lean_object* v_val_3096_, lean_object* v_v_3097_, lean_object* v_s_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3095_, v_val_3096_, v_v_3097_, v_s_3098_);
lean_dec(v_v_3097_);
lean_dec(v___y_3095_);
return v_res_3099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3107_ = l_Lean_Name_append(v___x_3106_, v___x_3105_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3116_ = l_Lean_Name_append(v___x_3115_, v___x_3114_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_cls_3121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3123_ = l_Lean_Name_append(v___x_3122_, v_cls_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v_toCold_3195_; lean_object* v_options_3196_; lean_object* v_inheritedTraceOptions_3197_; uint8_t v_hasTrace_3198_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; 
v_toCold_3195_ = lean_ctor_get(v_a_3134_, 0);
v_options_3196_ = lean_ctor_get(v_toCold_3195_, 2);
v_inheritedTraceOptions_3197_ = lean_ctor_get(v_toCold_3195_, 11);
v_hasTrace_3198_ = lean_ctor_get_uint8(v_options_3196_, sizeof(void*)*1);
if (v_hasTrace_3198_ == 0)
{
v___y_3200_ = v_a_3125_;
v___y_3201_ = v_a_3126_;
v___y_3202_ = v_a_3127_;
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
goto v___jp_3199_;
}
else
{
lean_object* v_cls_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_cls_3271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3197_, v_options_3196_, v___x_3272_);
if (v___x_3273_ == 0)
{
v___y_3200_ = v_a_3125_;
v___y_3201_ = v_a_3126_;
v___y_3202_ = v_a_3127_;
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_MessageData_ofExpr(v_a_3275_);
v___x_3277_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3271_, v___x_3276_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref_known(v___x_3277_, 1);
v___y_3200_ = v_a_3125_;
v___y_3201_ = v_a_3126_;
v___y_3202_ = v_a_3127_;
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
goto v___jp_3199_;
}
else
{
lean_dec_ref(v_c_3124_);
return v___x_3277_;
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_c_3124_);
v_a_3278_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3274_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3274_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
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
}
v___jp_3137_:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref_known(v___x_3154_, 1);
lean_inc(v___y_3143_);
v___f_3155_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3155_, 0, v___y_3143_);
lean_closure_set(v___f_3155_, 1, v___y_3138_);
lean_closure_set(v___f_3155_, 2, v___y_3139_);
v___x_3156_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3157_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3156_, v___f_3155_, v___y_3144_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; 
lean_dec_ref_known(v___x_3157_, 1);
v___x_3158_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3171_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3171_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3171_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
uint8_t v___x_3163_; uint8_t v___x_3164_; uint8_t v___x_3165_; 
v___x_3163_ = 0;
v___x_3164_ = lean_unbox(v_a_3159_);
lean_dec(v_a_3159_);
v___x_3165_ = l_Lean_instBEqLBool_beq(v___x_3164_, v___x_3163_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec(v___y_3141_);
v___x_3166_ = lean_box(0);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3166_);
v___x_3168_ = v___x_3161_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_object* v___x_3170_; 
lean_del_object(v___x_3161_);
v___x_3170_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3141_, v___y_3143_, v___y_3144_);
return v___x_3170_;
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v___y_3141_);
v_a_3172_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3158_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3158_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v___x_3157_;
}
}
else
{
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
return v___x_3154_;
}
}
v___jp_3180_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___y_3181_);
v___x_3194_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3193_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3194_;
}
v___jp_3199_:
{
lean_object* v___x_3211_; 
lean_inc_ref(v___y_3209_);
v___x_3211_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3124_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3262_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3262_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3262_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
if (lean_obj_tag(v_a_3212_) == 1)
{
lean_object* v_val_3216_; lean_object* v_p_3217_; 
lean_del_object(v___x_3214_);
v_val_3216_ = lean_ctor_get(v_a_3212_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v_a_3212_, 1);
v_p_3217_ = lean_ctor_get(v_val_3216_, 0);
if (lean_obj_tag(v_p_3217_) == 0)
{
lean_object* v_toCold_3218_; lean_object* v_options_3219_; uint8_t v_hasTrace_3220_; 
v_toCold_3218_ = lean_ctor_get(v___y_3209_, 0);
v_options_3219_ = lean_ctor_get(v_toCold_3218_, 2);
v_hasTrace_3220_ = lean_ctor_get_uint8(v_options_3219_, sizeof(void*)*1);
if (v_hasTrace_3220_ == 0)
{
v___y_3181_ = v_val_3216_;
v___y_3182_ = v___y_3200_;
v___y_3183_ = v___y_3201_;
v___y_3184_ = v___y_3202_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
goto v___jp_3180_;
}
else
{
lean_object* v_inheritedTraceOptions_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_inheritedTraceOptions_3221_ = lean_ctor_get(v_toCold_3218_, 11);
v___x_3222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3221_, v_options_3219_, v___x_3223_);
if (v___x_3224_ == 0)
{
v___y_3181_ = v_val_3216_;
v___y_3182_ = v___y_3200_;
v___y_3183_ = v___y_3201_;
v___y_3184_ = v___y_3202_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3216_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = l_Lean_MessageData_ofExpr(v_a_3226_);
v___x_3228_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3222_, v___x_3227_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_dec_ref_known(v___x_3228_, 1);
v___y_3181_ = v_val_3216_;
v___y_3182_ = v___y_3200_;
v___y_3183_ = v___y_3201_;
v___y_3184_ = v___y_3202_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
goto v___jp_3180_;
}
else
{
lean_dec(v_val_3216_);
return v___x_3228_;
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_val_3216_);
v_a_3229_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3225_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3225_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3237_; lean_object* v_options_3238_; uint8_t v_hasTrace_3239_; 
lean_inc_ref(v_p_3217_);
v_toCold_3237_ = lean_ctor_get(v___y_3209_, 0);
v_options_3238_ = lean_ctor_get(v_toCold_3237_, 2);
v_hasTrace_3239_ = lean_ctor_get_uint8(v_options_3238_, sizeof(void*)*1);
if (v_hasTrace_3239_ == 0)
{
lean_object* v_v_3240_; 
v_v_3240_ = lean_ctor_get(v_p_3217_, 1);
lean_inc_n(v_v_3240_, 2);
lean_inc(v_val_3216_);
v___y_3138_ = v_val_3216_;
v___y_3139_ = v_v_3240_;
v___y_3140_ = v_val_3216_;
v___y_3141_ = v_v_3240_;
v___y_3142_ = v_p_3217_;
v___y_3143_ = v___y_3200_;
v___y_3144_ = v___y_3201_;
v___y_3145_ = v___y_3202_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
goto v___jp_3137_;
}
else
{
lean_object* v_v_3241_; lean_object* v_inheritedTraceOptions_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_v_3241_ = lean_ctor_get(v_p_3217_, 1);
lean_inc(v_v_3241_);
v_inheritedTraceOptions_3242_ = lean_ctor_get(v_toCold_3237_, 11);
v___x_3243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3245_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3242_, v_options_3238_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_inc(v_v_3241_);
lean_inc(v_val_3216_);
v___y_3138_ = v_val_3216_;
v___y_3139_ = v_v_3241_;
v___y_3140_ = v_val_3216_;
v___y_3141_ = v_v_3241_;
v___y_3142_ = v_p_3217_;
v___y_3143_ = v___y_3200_;
v___y_3144_ = v___y_3201_;
v___y_3145_ = v___y_3202_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3216_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = l_Lean_MessageData_ofExpr(v_a_3247_);
v___x_3249_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3243_, v___x_3248_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_dec_ref_known(v___x_3249_, 1);
lean_inc(v_v_3241_);
lean_inc(v_val_3216_);
v___y_3138_ = v_val_3216_;
v___y_3139_ = v_v_3241_;
v___y_3140_ = v_val_3216_;
v___y_3141_ = v_v_3241_;
v___y_3142_ = v_p_3217_;
v___y_3143_ = v___y_3200_;
v___y_3144_ = v___y_3201_;
v___y_3145_ = v___y_3202_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
goto v___jp_3137_;
}
else
{
lean_dec(v_v_3241_);
lean_dec_ref_known(v_p_3217_, 3);
lean_dec(v_val_3216_);
return v___x_3249_;
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_v_3241_);
lean_dec_ref_known(v_p_3217_, 3);
lean_dec(v_val_3216_);
v_a_3250_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3246_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3246_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_dec(v_a_3212_);
v___x_3258_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3258_);
v___x_3260_ = v___x_3214_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
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
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
v_a_3263_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3211_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3211_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec(v_a_3287_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3300_, lean_object* v_as_3301_, size_t v_sz_3302_, size_t v_i_3303_, lean_object* v_b_3304_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_lt(v_i_3303_, v_sz_3302_);
if (v___x_3305_ == 0)
{
return v_b_3304_;
}
else
{
lean_object* v_snd_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3347_; 
v_snd_3306_ = lean_ctor_get(v_b_3304_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_b_3304_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v_b_3304_, 0);
lean_dec(v_unused_3348_);
v___x_3308_ = v_b_3304_;
v_isShared_3309_ = v_isSharedCheck_3347_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_snd_3306_);
lean_dec(v_b_3304_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3347_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_fst_3310_; lean_object* v_snd_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3346_; 
v_fst_3310_ = lean_ctor_get(v_snd_3306_, 0);
v_snd_3311_ = lean_ctor_get(v_snd_3306_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_snd_3306_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3313_ = v_snd_3306_;
v_isShared_3314_ = v_isSharedCheck_3346_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_snd_3311_);
lean_inc(v_fst_3310_);
lean_dec(v_snd_3306_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3346_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_a_3315_; lean_object* v_p_3316_; lean_object* v___x_3317_; lean_object* v_a_3319_; lean_object* v_b_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_a_3315_ = lean_array_uget(v_as_3301_, v_i_3303_);
v_p_3316_ = lean_ctor_get(v_a_3315_, 0);
v___x_3317_ = lean_box(0);
v_b_3326_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3316_, v_x_3300_);
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3328_ = lean_int_dec_eq(v_b_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3330_; 
lean_inc(v_a_3315_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_a_3315_);
lean_ctor_set(v___x_3308_, 0, v_b_3326_);
v___x_3330_ = v___x_3308_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_b_3326_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_a_3315_);
v___x_3330_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3338_; 
v_isSharedCheck_3338_ = !lean_is_exclusive(v_a_3315_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; lean_object* v_unused_3340_; 
v_unused_3339_ = lean_ctor_get(v_a_3315_, 1);
lean_dec(v_unused_3339_);
v_unused_3340_ = lean_ctor_get(v_a_3315_, 0);
lean_dec(v_unused_3340_);
v___x_3332_ = v_a_3315_;
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
else
{
lean_dec(v_a_3315_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_todo_3334_; lean_object* v___x_3336_; 
v_todo_3334_ = lean_array_push(v_snd_3311_, v___x_3330_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v_todo_3334_);
lean_ctor_set(v___x_3332_, 0, v_fst_3310_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_fst_3310_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_todo_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
v_a_3319_ = v___x_3336_;
goto v___jp_3318_;
}
}
}
}
else
{
lean_object* v_cs_x27_3342_; lean_object* v___x_3344_; 
lean_dec(v_b_3326_);
v_cs_x27_3342_ = l_Lean_PersistentArray_push___redArg(v_fst_3310_, v_a_3315_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_snd_3311_);
lean_ctor_set(v___x_3308_, 0, v_cs_x27_3342_);
v___x_3344_ = v___x_3308_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_cs_x27_3342_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_snd_3311_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
v_a_3319_ = v___x_3344_;
goto v___jp_3318_;
}
}
v___jp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v_a_3319_);
lean_ctor_set(v___x_3313_, 0, v___x_3317_);
v___x_3321_ = v___x_3313_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3319_);
v___x_3321_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
size_t v___x_3322_; size_t v___x_3323_; 
v___x_3322_ = ((size_t)1ULL);
v___x_3323_ = lean_usize_add(v_i_3303_, v___x_3322_);
v_i_3303_ = v___x_3323_;
v_b_3304_ = v___x_3321_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3349_, lean_object* v_as_3350_, lean_object* v_sz_3351_, lean_object* v_i_3352_, lean_object* v_b_3353_){
_start:
{
size_t v_sz_boxed_3354_; size_t v_i_boxed_3355_; lean_object* v_res_3356_; 
v_sz_boxed_3354_ = lean_unbox_usize(v_sz_3351_);
lean_dec(v_sz_3351_);
v_i_boxed_3355_ = lean_unbox_usize(v_i_3352_);
lean_dec(v_i_3352_);
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3349_, v_as_3350_, v_sz_boxed_3354_, v_i_boxed_3355_, v_b_3353_);
lean_dec_ref(v_as_3350_);
lean_dec(v_x_3349_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3357_, lean_object* v_as_3358_, size_t v_sz_3359_, size_t v_i_3360_, lean_object* v_b_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_usize_dec_lt(v_i_3360_, v_sz_3359_);
if (v___x_3362_ == 0)
{
return v_b_3361_;
}
else
{
lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3404_; 
v_snd_3363_ = lean_ctor_get(v_b_3361_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_b_3361_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v_b_3361_, 0);
lean_dec(v_unused_3405_);
v___x_3365_ = v_b_3361_;
v_isShared_3366_ = v_isSharedCheck_3404_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_dec(v_b_3361_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3404_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3403_; 
v_fst_3367_ = lean_ctor_get(v_snd_3363_, 0);
v_snd_3368_ = lean_ctor_get(v_snd_3363_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_snd_3363_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3370_ = v_snd_3363_;
v_isShared_3371_ = v_isSharedCheck_3403_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_inc(v_fst_3367_);
lean_dec(v_snd_3363_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3403_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_a_3372_; lean_object* v_p_3373_; lean_object* v___x_3374_; lean_object* v_a_3376_; lean_object* v_b_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v_a_3372_ = lean_array_uget(v_as_3358_, v_i_3360_);
v_p_3373_ = lean_ctor_get(v_a_3372_, 0);
v___x_3374_ = lean_box(0);
v_b_3383_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3373_, v_x_3357_);
v___x_3384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3385_ = lean_int_dec_eq(v_b_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3387_; 
lean_inc(v_a_3372_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v_a_3372_);
lean_ctor_set(v___x_3365_, 0, v_b_3383_);
v___x_3387_ = v___x_3365_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_b_3383_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_a_3372_);
v___x_3387_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3395_; 
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; 
v_unused_3396_ = lean_ctor_get(v_a_3372_, 1);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_a_3372_, 0);
lean_dec(v_unused_3397_);
v___x_3389_ = v_a_3372_;
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v_a_3372_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_todo_3391_; lean_object* v___x_3393_; 
v_todo_3391_ = lean_array_push(v_snd_3368_, v___x_3387_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 1, v_todo_3391_);
lean_ctor_set(v___x_3389_, 0, v_fst_3367_);
v___x_3393_ = v___x_3389_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_fst_3367_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_todo_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
v_a_3376_ = v___x_3393_;
goto v___jp_3375_;
}
}
}
}
else
{
lean_object* v_cs_x27_3399_; lean_object* v___x_3401_; 
lean_dec(v_b_3383_);
v_cs_x27_3399_ = l_Lean_PersistentArray_push___redArg(v_fst_3367_, v_a_3372_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v_snd_3368_);
lean_ctor_set(v___x_3365_, 0, v_cs_x27_3399_);
v___x_3401_ = v___x_3365_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_cs_x27_3399_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_snd_3368_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
v_a_3376_ = v___x_3401_;
goto v___jp_3375_;
}
}
v___jp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v_a_3376_);
lean_ctor_set(v___x_3370_, 0, v___x_3374_);
v___x_3378_ = v___x_3370_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3376_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((size_t)1ULL);
v___x_3380_ = lean_usize_add(v_i_3360_, v___x_3379_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3357_, v_as_3358_, v_sz_3359_, v___x_3380_, v___x_3378_);
return v___x_3381_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3406_, lean_object* v_as_3407_, lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_b_3410_){
_start:
{
size_t v_sz_boxed_3411_; size_t v_i_boxed_3412_; lean_object* v_res_3413_; 
v_sz_boxed_3411_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3406_, v_as_3407_, v_sz_boxed_3411_, v_i_boxed_3412_, v_b_3410_);
lean_dec_ref(v_as_3407_);
lean_dec(v_x_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3414_, lean_object* v_as_3415_, size_t v_sz_3416_, size_t v_i_3417_, lean_object* v_b_3418_){
_start:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_usize_dec_lt(v_i_3417_, v_sz_3416_);
if (v___x_3419_ == 0)
{
return v_b_3418_;
}
else
{
lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3461_; 
v_snd_3420_ = lean_ctor_get(v_b_3418_, 1);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_b_3418_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v_b_3418_, 0);
lean_dec(v_unused_3462_);
v___x_3422_ = v_b_3418_;
v_isShared_3423_ = v_isSharedCheck_3461_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_dec(v_b_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3461_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_fst_3424_; lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3460_; 
v_fst_3424_ = lean_ctor_get(v_snd_3420_, 0);
v_snd_3425_ = lean_ctor_get(v_snd_3420_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_snd_3420_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3427_ = v_snd_3420_;
v_isShared_3428_ = v_isSharedCheck_3460_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_inc(v_fst_3424_);
lean_dec(v_snd_3420_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3460_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_a_3429_; lean_object* v_p_3430_; lean_object* v___x_3431_; lean_object* v_a_3433_; lean_object* v_b_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_a_3429_ = lean_array_uget(v_as_3415_, v_i_3417_);
v_p_3430_ = lean_ctor_get(v_a_3429_, 0);
v___x_3431_ = lean_box(0);
v_b_3440_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3430_, v_x_3414_);
v___x_3441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3442_ = lean_int_dec_eq(v_b_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3444_; 
lean_inc(v_a_3429_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v_a_3429_);
lean_ctor_set(v___x_3422_, 0, v_b_3440_);
v___x_3444_ = v___x_3422_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_b_3440_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_a_3429_);
v___x_3444_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3452_; 
v_isSharedCheck_3452_ = !lean_is_exclusive(v_a_3429_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; lean_object* v_unused_3454_; 
v_unused_3453_ = lean_ctor_get(v_a_3429_, 1);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_a_3429_, 0);
lean_dec(v_unused_3454_);
v___x_3446_ = v_a_3429_;
v_isShared_3447_ = v_isSharedCheck_3452_;
goto v_resetjp_3445_;
}
else
{
lean_dec(v_a_3429_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3452_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_todo_3448_; lean_object* v___x_3450_; 
v_todo_3448_ = lean_array_push(v_snd_3425_, v___x_3444_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v_todo_3448_);
lean_ctor_set(v___x_3446_, 0, v_fst_3424_);
v___x_3450_ = v___x_3446_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_todo_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
v_a_3433_ = v___x_3450_;
goto v___jp_3432_;
}
}
}
}
else
{
lean_object* v_cs_x27_3456_; lean_object* v___x_3458_; 
lean_dec(v_b_3440_);
v_cs_x27_3456_ = l_Lean_PersistentArray_push___redArg(v_fst_3424_, v_a_3429_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v_snd_3425_);
lean_ctor_set(v___x_3422_, 0, v_cs_x27_3456_);
v___x_3458_ = v___x_3422_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_cs_x27_3456_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_snd_3425_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
v_a_3433_ = v___x_3458_;
goto v___jp_3432_;
}
}
v___jp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v_a_3433_);
lean_ctor_set(v___x_3427_, 0, v___x_3431_);
v___x_3435_ = v___x_3427_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_a_3433_);
v___x_3435_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
size_t v___x_3436_; size_t v___x_3437_; 
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3417_, v___x_3436_);
v_i_3417_ = v___x_3437_;
v_b_3418_ = v___x_3435_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3463_, lean_object* v_as_3464_, lean_object* v_sz_3465_, lean_object* v_i_3466_, lean_object* v_b_3467_){
_start:
{
size_t v_sz_boxed_3468_; size_t v_i_boxed_3469_; lean_object* v_res_3470_; 
v_sz_boxed_3468_ = lean_unbox_usize(v_sz_3465_);
lean_dec(v_sz_3465_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3463_, v_as_3464_, v_sz_boxed_3468_, v_i_boxed_3469_, v_b_3467_);
lean_dec_ref(v_as_3464_);
lean_dec(v_x_3463_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3471_, lean_object* v_as_3472_, size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_b_3475_){
_start:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
if (v___x_3476_ == 0)
{
return v_b_3475_;
}
else
{
lean_object* v_snd_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3518_; 
v_snd_3477_ = lean_ctor_get(v_b_3475_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_b_3475_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v_b_3475_, 0);
lean_dec(v_unused_3519_);
v___x_3479_ = v_b_3475_;
v_isShared_3480_ = v_isSharedCheck_3518_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_snd_3477_);
lean_dec(v_b_3475_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3518_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v_fst_3481_; lean_object* v_snd_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3517_; 
v_fst_3481_ = lean_ctor_get(v_snd_3477_, 0);
v_snd_3482_ = lean_ctor_get(v_snd_3477_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_snd_3477_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3484_ = v_snd_3477_;
v_isShared_3485_ = v_isSharedCheck_3517_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snd_3482_);
lean_inc(v_fst_3481_);
lean_dec(v_snd_3477_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3517_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_a_3486_; lean_object* v_p_3487_; lean_object* v___x_3488_; lean_object* v_a_3490_; lean_object* v_b_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v_a_3486_ = lean_array_uget(v_as_3472_, v_i_3474_);
v_p_3487_ = lean_ctor_get(v_a_3486_, 0);
v___x_3488_ = lean_box(0);
v_b_3497_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3487_, v_x_3471_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3499_ = lean_int_dec_eq(v_b_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3501_; 
lean_inc(v_a_3486_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 1, v_a_3486_);
lean_ctor_set(v___x_3479_, 0, v_b_3497_);
v___x_3501_ = v___x_3479_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_b_3497_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3486_);
v___x_3501_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3509_; 
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3486_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; lean_object* v_unused_3511_; 
v_unused_3510_ = lean_ctor_get(v_a_3486_, 1);
lean_dec(v_unused_3510_);
v_unused_3511_ = lean_ctor_get(v_a_3486_, 0);
lean_dec(v_unused_3511_);
v___x_3503_ = v_a_3486_;
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_a_3486_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_todo_3505_; lean_object* v___x_3507_; 
v_todo_3505_ = lean_array_push(v_snd_3482_, v___x_3501_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v_todo_3505_);
lean_ctor_set(v___x_3503_, 0, v_fst_3481_);
v___x_3507_ = v___x_3503_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_fst_3481_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_todo_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v_a_3490_ = v___x_3507_;
goto v___jp_3489_;
}
}
}
}
else
{
lean_object* v_cs_x27_3513_; lean_object* v___x_3515_; 
lean_dec(v_b_3497_);
v_cs_x27_3513_ = l_Lean_PersistentArray_push___redArg(v_fst_3481_, v_a_3486_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 1, v_snd_3482_);
lean_ctor_set(v___x_3479_, 0, v_cs_x27_3513_);
v___x_3515_ = v___x_3479_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_cs_x27_3513_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_snd_3482_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
v_a_3490_ = v___x_3515_;
goto v___jp_3489_;
}
}
v___jp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v_a_3490_);
lean_ctor_set(v___x_3484_, 0, v___x_3488_);
v___x_3492_ = v___x_3484_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_a_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3474_, v___x_3493_);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3471_, v_as_3472_, v_sz_3473_, v___x_3494_, v___x_3492_);
return v___x_3495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3520_, lean_object* v_as_3521_, lean_object* v_sz_3522_, lean_object* v_i_3523_, lean_object* v_b_3524_){
_start:
{
size_t v_sz_boxed_3525_; size_t v_i_boxed_3526_; lean_object* v_res_3527_; 
v_sz_boxed_3525_ = lean_unbox_usize(v_sz_3522_);
lean_dec(v_sz_3522_);
v_i_boxed_3526_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3520_, v_as_3521_, v_sz_boxed_3525_, v_i_boxed_3526_, v_b_3524_);
lean_dec_ref(v_as_3521_);
lean_dec(v_x_3520_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3528_, lean_object* v_x_3529_, lean_object* v_n_3530_, lean_object* v_b_3531_){
_start:
{
if (lean_obj_tag(v_n_3530_) == 0)
{
lean_object* v_cs_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; size_t v_sz_3535_; size_t v___x_3536_; lean_object* v___x_3537_; lean_object* v_fst_3538_; 
v_cs_3532_ = lean_ctor_get(v_n_3530_, 0);
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v_b_3531_);
v_sz_3535_ = lean_array_size(v_cs_3532_);
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3528_, v_x_3529_, v_cs_3532_, v_sz_3535_, v___x_3536_, v___x_3534_);
v_fst_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_fst_3538_);
if (lean_obj_tag(v_fst_3538_) == 0)
{
lean_object* v_snd_3539_; lean_object* v___x_3540_; 
v_snd_3539_ = lean_ctor_get(v___x_3537_, 1);
lean_inc(v_snd_3539_);
lean_dec_ref(v___x_3537_);
v___x_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_snd_3539_);
return v___x_3540_;
}
else
{
lean_object* v_val_3541_; 
lean_dec_ref(v___x_3537_);
v_val_3541_ = lean_ctor_get(v_fst_3538_, 0);
lean_inc(v_val_3541_);
lean_dec_ref_known(v_fst_3538_, 1);
return v_val_3541_;
}
}
else
{
lean_object* v_vs_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; size_t v_sz_3545_; size_t v___x_3546_; lean_object* v___x_3547_; lean_object* v_fst_3548_; 
v_vs_3542_ = lean_ctor_get(v_n_3530_, 0);
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v_b_3531_);
v_sz_3545_ = lean_array_size(v_vs_3542_);
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3529_, v_vs_3542_, v_sz_3545_, v___x_3546_, v___x_3544_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3552_, lean_object* v_x_3553_, lean_object* v_as_3554_, size_t v_sz_3555_, size_t v_i_3556_, lean_object* v_b_3557_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = lean_usize_dec_lt(v_i_3556_, v_sz_3555_);
if (v___x_3558_ == 0)
{
return v_b_3557_;
}
else
{
lean_object* v_snd_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3577_; 
v_snd_3559_ = lean_ctor_get(v_b_3557_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_b_3557_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_b_3557_, 0);
lean_dec(v_unused_3578_);
v___x_3561_ = v_b_3557_;
v_isShared_3562_ = v_isSharedCheck_3577_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_snd_3559_);
lean_dec(v_b_3557_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3577_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_a_3563_; lean_object* v___x_3564_; 
v_a_3563_ = lean_array_uget_borrowed(v_as_3554_, v_i_3556_);
lean_inc(v_snd_3559_);
v___x_3564_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3552_, v_x_3553_, v_a_3563_, v_snd_3559_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3565_);
v___x_3567_ = v___x_3561_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_snd_3559_);
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
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
lean_dec(v_snd_3559_);
v_a_3569_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3570_ = lean_box(0);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 1, v_a_3569_);
lean_ctor_set(v___x_3561_, 0, v___x_3570_);
v___x_3572_ = v___x_3561_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_a_3569_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
size_t v___x_3573_; size_t v___x_3574_; 
v___x_3573_ = ((size_t)1ULL);
v___x_3574_ = lean_usize_add(v_i_3556_, v___x_3573_);
v_i_3556_ = v___x_3574_;
v_b_3557_ = v___x_3572_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3579_, lean_object* v_x_3580_, lean_object* v_as_3581_, lean_object* v_sz_3582_, lean_object* v_i_3583_, lean_object* v_b_3584_){
_start:
{
size_t v_sz_boxed_3585_; size_t v_i_boxed_3586_; lean_object* v_res_3587_; 
v_sz_boxed_3585_ = lean_unbox_usize(v_sz_3582_);
lean_dec(v_sz_3582_);
v_i_boxed_3586_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_res_3587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3579_, v_x_3580_, v_as_3581_, v_sz_boxed_3585_, v_i_boxed_3586_, v_b_3584_);
lean_dec_ref(v_as_3581_);
lean_dec(v_x_3580_);
lean_dec_ref(v_init_3579_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3588_, lean_object* v_x_3589_, lean_object* v_n_3590_, lean_object* v_b_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3588_, v_x_3589_, v_n_3590_, v_b_3591_);
lean_dec_ref(v_n_3590_);
lean_dec(v_x_3589_);
lean_dec_ref(v_init_3588_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3593_, lean_object* v_t_3594_, lean_object* v_init_3595_){
_start:
{
lean_object* v_root_3596_; lean_object* v_tail_3597_; lean_object* v___x_3598_; 
v_root_3596_ = lean_ctor_get(v_t_3594_, 0);
v_tail_3597_ = lean_ctor_get(v_t_3594_, 1);
lean_inc_ref(v_init_3595_);
v___x_3598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3595_, v_x_3593_, v_root_3596_, v_init_3595_);
lean_dec_ref(v_init_3595_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
return v_a_3599_;
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; size_t v_sz_3603_; size_t v___x_3604_; lean_object* v___x_3605_; lean_object* v_fst_3606_; 
v_a_3600_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3601_ = lean_box(0);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v_a_3600_);
v_sz_3603_ = lean_array_size(v_tail_3597_);
v___x_3604_ = ((size_t)0ULL);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3593_, v_tail_3597_, v_sz_3603_, v___x_3604_, v___x_3602_);
v_fst_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_fst_3606_);
if (lean_obj_tag(v_fst_3606_) == 0)
{
lean_object* v_snd_3607_; 
v_snd_3607_ = lean_ctor_get(v___x_3605_, 1);
lean_inc(v_snd_3607_);
lean_dec_ref(v___x_3605_);
return v_snd_3607_;
}
else
{
lean_object* v_val_3608_; 
lean_dec_ref(v___x_3605_);
v_val_3608_ = lean_ctor_get(v_fst_3606_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v_fst_3606_, 1);
return v_val_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3609_, lean_object* v_t_3610_, lean_object* v_init_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3609_, v_t_3610_, v_init_3611_);
lean_dec_ref(v_t_3610_);
lean_dec(v_x_3609_);
return v_res_3612_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = lean_unsigned_to_nat(32u);
v___x_3614_ = lean_mk_empty_array_with_capacity(v___x_3613_);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v_cs_x27_3621_; 
v___x_3616_ = ((size_t)5ULL);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = lean_unsigned_to_nat(32u);
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_3618_);
v___x_3620_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3621_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3621_, 0, v___x_3620_);
lean_ctor_set(v_cs_x27_3621_, 1, v___x_3619_);
lean_ctor_set(v_cs_x27_3621_, 2, v___x_3617_);
lean_ctor_set(v_cs_x27_3621_, 3, v___x_3617_);
lean_ctor_set_usize(v_cs_x27_3621_, 4, v___x_3616_);
return v_cs_x27_3621_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3624_; lean_object* v_cs_x27_3625_; lean_object* v___x_3626_; 
v_todo_3624_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3625_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_cs_x27_3625_);
lean_ctor_set(v___x_3626_, 1, v_todo_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3627_, lean_object* v_cs_3628_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_fst_3631_; lean_object* v_snd_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
v___x_3629_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3630_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3627_, v_cs_3628_, v___x_3629_);
v_fst_3631_ = lean_ctor_get(v___x_3630_, 0);
v_snd_3632_ = lean_ctor_get(v___x_3630_, 1);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3630_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_snd_3632_);
lean_inc(v_fst_3631_);
lean_dec(v___x_3630_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_fst_3631_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_snd_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3640_, lean_object* v_cs_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3640_, v_cs_3641_);
lean_dec_ref(v_cs_3641_);
lean_dec(v_x_3640_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3643_, lean_object* v_cs_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3643_, v_cs_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3646_, lean_object* v_cs_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3646_, v_cs_3647_);
lean_dec_ref(v_cs_3647_);
lean_dec(v_x_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3649_, lean_object* v_y_3650_, lean_object* v_fst_3651_, lean_object* v_s_3652_){
_start:
{
lean_object* v_structs_3653_; lean_object* v_typeIdOf_3654_; lean_object* v_exprToStructId_3655_; lean_object* v_exprToStructIdEntries_3656_; lean_object* v_forbiddenNatModules_3657_; lean_object* v_natStructs_3658_; lean_object* v_natTypeIdOf_3659_; lean_object* v_exprToNatStructId_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_structs_3653_ = lean_ctor_get(v_s_3652_, 0);
v_typeIdOf_3654_ = lean_ctor_get(v_s_3652_, 1);
v_exprToStructId_3655_ = lean_ctor_get(v_s_3652_, 2);
v_exprToStructIdEntries_3656_ = lean_ctor_get(v_s_3652_, 3);
v_forbiddenNatModules_3657_ = lean_ctor_get(v_s_3652_, 4);
v_natStructs_3658_ = lean_ctor_get(v_s_3652_, 5);
v_natTypeIdOf_3659_ = lean_ctor_get(v_s_3652_, 6);
v_exprToNatStructId_3660_ = lean_ctor_get(v_s_3652_, 7);
v___x_3661_ = lean_array_get_size(v_structs_3653_);
v___x_3662_ = lean_nat_dec_lt(v_a_3649_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec_ref(v_fst_3651_);
return v_s_3652_;
}
else
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3724_; 
lean_inc_ref(v_exprToNatStructId_3660_);
lean_inc_ref(v_natTypeIdOf_3659_);
lean_inc_ref(v_natStructs_3658_);
lean_inc_ref(v_forbiddenNatModules_3657_);
lean_inc_ref(v_exprToStructIdEntries_3656_);
lean_inc_ref(v_exprToStructId_3655_);
lean_inc_ref(v_typeIdOf_3654_);
lean_inc_ref(v_structs_3653_);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_s_3652_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; 
v_unused_3725_ = lean_ctor_get(v_s_3652_, 7);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_s_3652_, 6);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_s_3652_, 5);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_s_3652_, 4);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_s_3652_, 3);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_s_3652_, 2);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_s_3652_, 1);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_s_3652_, 0);
lean_dec(v_unused_3732_);
v___x_3664_ = v_s_3652_;
v_isShared_3665_ = v_isSharedCheck_3724_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_s_3652_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3724_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_v_3666_; lean_object* v_id_3667_; lean_object* v_ringId_x3f_3668_; lean_object* v_type_3669_; lean_object* v_u_3670_; lean_object* v_intModuleInst_3671_; lean_object* v_leInst_x3f_3672_; lean_object* v_ltInst_x3f_3673_; lean_object* v_lawfulOrderLTInst_x3f_3674_; lean_object* v_isPreorderInst_x3f_3675_; lean_object* v_orderedAddInst_x3f_3676_; lean_object* v_isLinearInst_x3f_3677_; lean_object* v_noNatDivInst_x3f_3678_; lean_object* v_ringInst_x3f_3679_; lean_object* v_commRingInst_x3f_3680_; lean_object* v_orderedRingInst_x3f_3681_; lean_object* v_fieldInst_x3f_3682_; lean_object* v_charInst_x3f_3683_; lean_object* v_zero_3684_; lean_object* v_ofNatZero_3685_; lean_object* v_one_x3f_3686_; lean_object* v_leFn_x3f_3687_; lean_object* v_ltFn_x3f_3688_; lean_object* v_addFn_3689_; lean_object* v_zsmulFn_3690_; lean_object* v_nsmulFn_3691_; lean_object* v_zsmulFn_x3f_3692_; lean_object* v_nsmulFn_x3f_3693_; lean_object* v_homomulFn_x3f_3694_; lean_object* v_subFn_3695_; lean_object* v_negFn_3696_; lean_object* v_vars_3697_; lean_object* v_varMap_3698_; lean_object* v_lowers_3699_; lean_object* v_uppers_3700_; lean_object* v_diseqs_3701_; lean_object* v_assignment_3702_; uint8_t v_caseSplits_3703_; lean_object* v_conflict_x3f_3704_; lean_object* v_diseqSplits_3705_; lean_object* v_elimEqs_3706_; lean_object* v_elimStack_3707_; lean_object* v_occurs_3708_; lean_object* v_ignored_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3723_; 
v_v_3666_ = lean_array_fget(v_structs_3653_, v_a_3649_);
v_id_3667_ = lean_ctor_get(v_v_3666_, 0);
v_ringId_x3f_3668_ = lean_ctor_get(v_v_3666_, 1);
v_type_3669_ = lean_ctor_get(v_v_3666_, 2);
v_u_3670_ = lean_ctor_get(v_v_3666_, 3);
v_intModuleInst_3671_ = lean_ctor_get(v_v_3666_, 4);
v_leInst_x3f_3672_ = lean_ctor_get(v_v_3666_, 5);
v_ltInst_x3f_3673_ = lean_ctor_get(v_v_3666_, 6);
v_lawfulOrderLTInst_x3f_3674_ = lean_ctor_get(v_v_3666_, 7);
v_isPreorderInst_x3f_3675_ = lean_ctor_get(v_v_3666_, 8);
v_orderedAddInst_x3f_3676_ = lean_ctor_get(v_v_3666_, 9);
v_isLinearInst_x3f_3677_ = lean_ctor_get(v_v_3666_, 10);
v_noNatDivInst_x3f_3678_ = lean_ctor_get(v_v_3666_, 11);
v_ringInst_x3f_3679_ = lean_ctor_get(v_v_3666_, 12);
v_commRingInst_x3f_3680_ = lean_ctor_get(v_v_3666_, 13);
v_orderedRingInst_x3f_3681_ = lean_ctor_get(v_v_3666_, 14);
v_fieldInst_x3f_3682_ = lean_ctor_get(v_v_3666_, 15);
v_charInst_x3f_3683_ = lean_ctor_get(v_v_3666_, 16);
v_zero_3684_ = lean_ctor_get(v_v_3666_, 17);
v_ofNatZero_3685_ = lean_ctor_get(v_v_3666_, 18);
v_one_x3f_3686_ = lean_ctor_get(v_v_3666_, 19);
v_leFn_x3f_3687_ = lean_ctor_get(v_v_3666_, 20);
v_ltFn_x3f_3688_ = lean_ctor_get(v_v_3666_, 21);
v_addFn_3689_ = lean_ctor_get(v_v_3666_, 22);
v_zsmulFn_3690_ = lean_ctor_get(v_v_3666_, 23);
v_nsmulFn_3691_ = lean_ctor_get(v_v_3666_, 24);
v_zsmulFn_x3f_3692_ = lean_ctor_get(v_v_3666_, 25);
v_nsmulFn_x3f_3693_ = lean_ctor_get(v_v_3666_, 26);
v_homomulFn_x3f_3694_ = lean_ctor_get(v_v_3666_, 27);
v_subFn_3695_ = lean_ctor_get(v_v_3666_, 28);
v_negFn_3696_ = lean_ctor_get(v_v_3666_, 29);
v_vars_3697_ = lean_ctor_get(v_v_3666_, 30);
v_varMap_3698_ = lean_ctor_get(v_v_3666_, 31);
v_lowers_3699_ = lean_ctor_get(v_v_3666_, 32);
v_uppers_3700_ = lean_ctor_get(v_v_3666_, 33);
v_diseqs_3701_ = lean_ctor_get(v_v_3666_, 34);
v_assignment_3702_ = lean_ctor_get(v_v_3666_, 35);
v_caseSplits_3703_ = lean_ctor_get_uint8(v_v_3666_, sizeof(void*)*42);
v_conflict_x3f_3704_ = lean_ctor_get(v_v_3666_, 36);
v_diseqSplits_3705_ = lean_ctor_get(v_v_3666_, 37);
v_elimEqs_3706_ = lean_ctor_get(v_v_3666_, 38);
v_elimStack_3707_ = lean_ctor_get(v_v_3666_, 39);
v_occurs_3708_ = lean_ctor_get(v_v_3666_, 40);
v_ignored_3709_ = lean_ctor_get(v_v_3666_, 41);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_v_3666_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3711_ = v_v_3666_;
v_isShared_3712_ = v_isSharedCheck_3723_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_ignored_3709_);
lean_inc(v_occurs_3708_);
lean_inc(v_elimStack_3707_);
lean_inc(v_elimEqs_3706_);
lean_inc(v_diseqSplits_3705_);
lean_inc(v_conflict_x3f_3704_);
lean_inc(v_assignment_3702_);
lean_inc(v_diseqs_3701_);
lean_inc(v_uppers_3700_);
lean_inc(v_lowers_3699_);
lean_inc(v_varMap_3698_);
lean_inc(v_vars_3697_);
lean_inc(v_negFn_3696_);
lean_inc(v_subFn_3695_);
lean_inc(v_homomulFn_x3f_3694_);
lean_inc(v_nsmulFn_x3f_3693_);
lean_inc(v_zsmulFn_x3f_3692_);
lean_inc(v_nsmulFn_3691_);
lean_inc(v_zsmulFn_3690_);
lean_inc(v_addFn_3689_);
lean_inc(v_ltFn_x3f_3688_);
lean_inc(v_leFn_x3f_3687_);
lean_inc(v_one_x3f_3686_);
lean_inc(v_ofNatZero_3685_);
lean_inc(v_zero_3684_);
lean_inc(v_charInst_x3f_3683_);
lean_inc(v_fieldInst_x3f_3682_);
lean_inc(v_orderedRingInst_x3f_3681_);
lean_inc(v_commRingInst_x3f_3680_);
lean_inc(v_ringInst_x3f_3679_);
lean_inc(v_noNatDivInst_x3f_3678_);
lean_inc(v_isLinearInst_x3f_3677_);
lean_inc(v_orderedAddInst_x3f_3676_);
lean_inc(v_isPreorderInst_x3f_3675_);
lean_inc(v_lawfulOrderLTInst_x3f_3674_);
lean_inc(v_ltInst_x3f_3673_);
lean_inc(v_leInst_x3f_3672_);
lean_inc(v_intModuleInst_3671_);
lean_inc(v_u_3670_);
lean_inc(v_type_3669_);
lean_inc(v_ringId_x3f_3668_);
lean_inc(v_id_3667_);
lean_dec(v_v_3666_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3723_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v_xs_x27_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3713_ = lean_box(0);
v_xs_x27_3714_ = lean_array_fset(v_structs_3653_, v_a_3649_, v___x_3713_);
v___x_3715_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3701_, v_y_3650_, v_fst_3651_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 34, v___x_3715_);
v___x_3717_ = v___x_3711_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_id_3667_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_ringId_x3f_3668_);
lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_type_3669_);
lean_ctor_set(v_reuseFailAlloc_3722_, 3, v_u_3670_);
lean_ctor_set(v_reuseFailAlloc_3722_, 4, v_intModuleInst_3671_);
lean_ctor_set(v_reuseFailAlloc_3722_, 5, v_leInst_x3f_3672_);
lean_ctor_set(v_reuseFailAlloc_3722_, 6, v_ltInst_x3f_3673_);
lean_ctor_set(v_reuseFailAlloc_3722_, 7, v_lawfulOrderLTInst_x3f_3674_);
lean_ctor_set(v_reuseFailAlloc_3722_, 8, v_isPreorderInst_x3f_3675_);
lean_ctor_set(v_reuseFailAlloc_3722_, 9, v_orderedAddInst_x3f_3676_);
lean_ctor_set(v_reuseFailAlloc_3722_, 10, v_isLinearInst_x3f_3677_);
lean_ctor_set(v_reuseFailAlloc_3722_, 11, v_noNatDivInst_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3722_, 12, v_ringInst_x3f_3679_);
lean_ctor_set(v_reuseFailAlloc_3722_, 13, v_commRingInst_x3f_3680_);
lean_ctor_set(v_reuseFailAlloc_3722_, 14, v_orderedRingInst_x3f_3681_);
lean_ctor_set(v_reuseFailAlloc_3722_, 15, v_fieldInst_x3f_3682_);
lean_ctor_set(v_reuseFailAlloc_3722_, 16, v_charInst_x3f_3683_);
lean_ctor_set(v_reuseFailAlloc_3722_, 17, v_zero_3684_);
lean_ctor_set(v_reuseFailAlloc_3722_, 18, v_ofNatZero_3685_);
lean_ctor_set(v_reuseFailAlloc_3722_, 19, v_one_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3722_, 20, v_leFn_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3722_, 21, v_ltFn_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3722_, 22, v_addFn_3689_);
lean_ctor_set(v_reuseFailAlloc_3722_, 23, v_zsmulFn_3690_);
lean_ctor_set(v_reuseFailAlloc_3722_, 24, v_nsmulFn_3691_);
lean_ctor_set(v_reuseFailAlloc_3722_, 25, v_zsmulFn_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3722_, 26, v_nsmulFn_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3722_, 27, v_homomulFn_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3722_, 28, v_subFn_3695_);
lean_ctor_set(v_reuseFailAlloc_3722_, 29, v_negFn_3696_);
lean_ctor_set(v_reuseFailAlloc_3722_, 30, v_vars_3697_);
lean_ctor_set(v_reuseFailAlloc_3722_, 31, v_varMap_3698_);
lean_ctor_set(v_reuseFailAlloc_3722_, 32, v_lowers_3699_);
lean_ctor_set(v_reuseFailAlloc_3722_, 33, v_uppers_3700_);
lean_ctor_set(v_reuseFailAlloc_3722_, 34, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3722_, 35, v_assignment_3702_);
lean_ctor_set(v_reuseFailAlloc_3722_, 36, v_conflict_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3722_, 37, v_diseqSplits_3705_);
lean_ctor_set(v_reuseFailAlloc_3722_, 38, v_elimEqs_3706_);
lean_ctor_set(v_reuseFailAlloc_3722_, 39, v_elimStack_3707_);
lean_ctor_set(v_reuseFailAlloc_3722_, 40, v_occurs_3708_);
lean_ctor_set(v_reuseFailAlloc_3722_, 41, v_ignored_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3722_, sizeof(void*)*42, v_caseSplits_3703_);
v___x_3717_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3718_ = lean_array_fset(v_xs_x27_3714_, v_a_3649_, v___x_3717_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3718_);
v___x_3720_ = v___x_3664_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_typeIdOf_3654_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_exprToStructId_3655_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_exprToStructIdEntries_3656_);
lean_ctor_set(v_reuseFailAlloc_3721_, 4, v_forbiddenNatModules_3657_);
lean_ctor_set(v_reuseFailAlloc_3721_, 5, v_natStructs_3658_);
lean_ctor_set(v_reuseFailAlloc_3721_, 6, v_natTypeIdOf_3659_);
lean_ctor_set(v_reuseFailAlloc_3721_, 7, v_exprToNatStructId_3660_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3733_, lean_object* v_y_3734_, lean_object* v_fst_3735_, lean_object* v_s_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3733_, v_y_3734_, v_fst_3735_, v_s_3736_);
lean_dec(v_y_3734_);
lean_dec(v_a_3733_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3738_, lean_object* v_x_3739_, lean_object* v_c_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_a_3758_; uint8_t v___x_3762_; 
v___x_3762_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_dec_ref(v_c_3740_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_b_3744_);
return v___x_3763_;
}
else
{
lean_object* v_a_3764_; lean_object* v_fst_3765_; lean_object* v_snd_3766_; lean_object* v___x_3767_; 
lean_dec_ref(v_b_3744_);
v_a_3764_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
v_fst_3765_ = lean_ctor_get(v_a_3764_, 0);
v_snd_3766_ = lean_ctor_get(v_a_3764_, 1);
lean_inc(v_snd_3766_);
lean_inc(v_fst_3765_);
lean_inc_ref(v_c_3740_);
v___x_3767_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3738_, v_x_3739_, v_c_3740_, v_fst_3765_, v_snd_3766_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3768_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3771_; 
v_val_3770_ = lean_ctor_get(v_a_3768_, 0);
lean_inc(v_val_3770_);
lean_dec_ref_known(v_a_3768_, 1);
v___x_3771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3770_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3772_; 
lean_dec_ref_known(v___x_3771_, 1);
v___x_3772_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3782_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_unbox(v_a_3773_);
lean_dec(v_a_3773_);
if (v___x_3777_ == 0)
{
lean_del_object(v___x_3775_);
v_a_3758_ = v___x_3769_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_dec_ref(v_c_3740_);
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v___x_3778_);
v___x_3780_ = v___x_3775_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
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
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_c_3740_);
v_a_3783_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3772_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3772_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v_c_3740_);
v_a_3791_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3771_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3771_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
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
lean_object* v___x_3799_; 
lean_dec(v_a_3768_);
v___x_3799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3766_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref_known(v___x_3799_, 1);
v_a_3758_ = v___x_3769_;
goto v___jp_3757_;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v_c_3740_);
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_c_3740_);
v_a_3808_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3767_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3767_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
v___jp_3757_:
{
size_t v___x_3759_; size_t v___x_3760_; 
v___x_3759_ = ((size_t)1ULL);
v___x_3760_ = lean_usize_add(v_i_3743_, v___x_3759_);
lean_inc_ref(v_a_3758_);
v_i_3743_ = v___x_3760_;
v_b_3744_ = v_a_3758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3816_ = _args[0];
lean_object* v_x_3817_ = _args[1];
lean_object* v_c_3818_ = _args[2];
lean_object* v_as_3819_ = _args[3];
lean_object* v_sz_3820_ = _args[4];
lean_object* v_i_3821_ = _args[5];
lean_object* v_b_3822_ = _args[6];
lean_object* v___y_3823_ = _args[7];
lean_object* v___y_3824_ = _args[8];
lean_object* v___y_3825_ = _args[9];
lean_object* v___y_3826_ = _args[10];
lean_object* v___y_3827_ = _args[11];
lean_object* v___y_3828_ = _args[12];
lean_object* v___y_3829_ = _args[13];
lean_object* v___y_3830_ = _args[14];
lean_object* v___y_3831_ = _args[15];
lean_object* v___y_3832_ = _args[16];
lean_object* v___y_3833_ = _args[17];
lean_object* v___y_3834_ = _args[18];
_start:
{
size_t v_sz_boxed_3835_; size_t v_i_boxed_3836_; lean_object* v_res_3837_; 
v_sz_boxed_3835_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3836_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3816_, v_x_3817_, v_c_3818_, v_as_3819_, v_sz_boxed_3835_, v_i_boxed_3836_, v_b_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v_as_3819_);
lean_dec(v_x_3817_);
lean_dec(v_a_3816_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3838_, lean_object* v_x_3839_, lean_object* v_c_3840_, lean_object* v_y_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3914_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3914_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3914_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
uint8_t v___x_3859_; 
v___x_3859_ = lean_unbox(v_a_3855_);
lean_dec(v_a_3855_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_del_object(v___x_3857_);
v___x_3860_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___y_3863_; lean_object* v_diseqs_3896_; lean_object* v_size_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v_diseqs_3896_ = lean_ctor_get(v_a_3861_, 34);
lean_inc_ref(v_diseqs_3896_);
lean_dec(v_a_3861_);
v_size_3897_ = lean_ctor_get(v_diseqs_3896_, 2);
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3899_ = lean_nat_dec_lt(v_y_3841_, v_size_3897_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec_ref(v_diseqs_3896_);
v___x_3900_ = l_outOfBounds___redArg(v___x_3898_);
v___y_3863_ = v___x_3900_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3898_, v_diseqs_3896_, v_y_3841_);
lean_dec_ref(v_diseqs_3896_);
v___y_3863_ = v___x_3901_;
goto v___jp_3862_;
}
v___jp_3862_:
{
lean_object* v___x_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v___f_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3864_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3839_, v___y_3863_);
lean_dec_ref(v___y_3863_);
v_fst_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fst_3865_);
v_snd_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_snd_3866_);
lean_dec_ref(v___x_3864_);
lean_inc(v_a_3842_);
v___f_3867_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3867_, 0, v_a_3842_);
lean_closure_set(v___f_3867_, 1, v_y_3841_);
lean_closure_set(v___f_3867_, 2, v_fst_3865_);
v___x_3868_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3869_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3868_, v___f_3867_, v_a_3843_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
lean_dec_ref_known(v___x_3869_, 1);
v___x_3870_ = lean_box(0);
v___x_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3872_ = lean_array_size(v_snd_3866_);
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3838_, v_x_3839_, v_c_3840_, v_snd_3866_, v_sz_3872_, v___x_3873_, v___x_3871_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_snd_3866_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3887_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3887_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3887_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_fst_3879_; 
v_fst_3879_ = lean_ctor_get(v_a_3875_, 0);
lean_inc(v_fst_3879_);
lean_dec(v_a_3875_);
if (lean_obj_tag(v_fst_3879_) == 0)
{
lean_object* v___x_3881_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3870_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3870_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
else
{
lean_object* v_val_3883_; lean_object* v___x_3885_; 
v_val_3883_ = lean_ctor_get(v_fst_3879_, 0);
lean_inc(v_val_3883_);
lean_dec_ref_known(v_fst_3879_, 1);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_val_3883_);
v___x_3885_ = v___x_3877_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_a_3888_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3874_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3874_);
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
lean_dec(v_snd_3866_);
lean_dec_ref(v_c_3840_);
return v___x_3869_;
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_y_3841_);
lean_dec_ref(v_c_3840_);
v_a_3902_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3860_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3860_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
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
lean_object* v___x_3910_; lean_object* v___x_3912_; 
lean_dec(v_y_3841_);
lean_dec_ref(v_c_3840_);
v___x_3910_ = lean_box(0);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3910_);
v___x_3912_ = v___x_3857_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
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
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_y_3841_);
lean_dec_ref(v_c_3840_);
v_a_3915_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3854_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3854_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3923_, lean_object* v_x_3924_, lean_object* v_c_3925_, lean_object* v_y_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3923_, v_x_3924_, v_c_3925_, v_y_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_x_3924_);
lean_dec(v_a_3923_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3940_, lean_object* v_x_3941_, lean_object* v_c_3942_, lean_object* v_y_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v___x_3956_; 
lean_inc(v_y_3943_);
lean_inc_ref(v_c_3942_);
lean_inc(v_x_3941_);
lean_inc(v_a_3940_);
v___x_3956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3940_, v_x_3941_, v_c_3942_, v_y_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref_known(v___x_3956_, 1);
lean_inc(v_y_3943_);
lean_inc_ref(v_c_3942_);
lean_inc(v_x_3941_);
lean_inc(v_a_3940_);
v___x_3957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3940_, v_x_3941_, v_c_3942_, v_y_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec_ref_known(v___x_3957_, 1);
v___x_3958_ = lean_nat_to_int(v_a_3940_);
v___x_3959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3958_, v_x_3941_, v_c_3942_, v_y_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
lean_dec(v_x_3941_);
lean_dec(v___x_3958_);
return v___x_3959_;
}
else
{
lean_dec(v_y_3943_);
lean_dec_ref(v_c_3942_);
lean_dec(v_x_3941_);
lean_dec(v_a_3940_);
return v___x_3957_;
}
}
else
{
lean_dec(v_y_3943_);
lean_dec_ref(v_c_3942_);
lean_dec(v_x_3941_);
lean_dec(v_a_3940_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3960_, lean_object* v_x_3961_, lean_object* v_c_3962_, lean_object* v_y_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3960_, v_x_3961_, v_c_3962_, v_y_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec(v_a_3964_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3977_, lean_object* v_x_3978_, lean_object* v_s_3979_){
_start:
{
lean_object* v_structs_3980_; lean_object* v_typeIdOf_3981_; lean_object* v_exprToStructId_3982_; lean_object* v_exprToStructIdEntries_3983_; lean_object* v_forbiddenNatModules_3984_; lean_object* v_natStructs_3985_; lean_object* v_natTypeIdOf_3986_; lean_object* v_exprToNatStructId_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; 
v_structs_3980_ = lean_ctor_get(v_s_3979_, 0);
v_typeIdOf_3981_ = lean_ctor_get(v_s_3979_, 1);
v_exprToStructId_3982_ = lean_ctor_get(v_s_3979_, 2);
v_exprToStructIdEntries_3983_ = lean_ctor_get(v_s_3979_, 3);
v_forbiddenNatModules_3984_ = lean_ctor_get(v_s_3979_, 4);
v_natStructs_3985_ = lean_ctor_get(v_s_3979_, 5);
v_natTypeIdOf_3986_ = lean_ctor_get(v_s_3979_, 6);
v_exprToNatStructId_3987_ = lean_ctor_get(v_s_3979_, 7);
v___x_3988_ = lean_array_get_size(v_structs_3980_);
v___x_3989_ = lean_nat_dec_lt(v_a_3977_, v___x_3988_);
if (v___x_3989_ == 0)
{
return v_s_3979_;
}
else
{
lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4052_; 
lean_inc_ref(v_exprToNatStructId_3987_);
lean_inc_ref(v_natTypeIdOf_3986_);
lean_inc_ref(v_natStructs_3985_);
lean_inc_ref(v_forbiddenNatModules_3984_);
lean_inc_ref(v_exprToStructIdEntries_3983_);
lean_inc_ref(v_exprToStructId_3982_);
lean_inc_ref(v_typeIdOf_3981_);
lean_inc_ref(v_structs_3980_);
v_isSharedCheck_4052_ = !lean_is_exclusive(v_s_3979_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; lean_object* v_unused_4054_; lean_object* v_unused_4055_; lean_object* v_unused_4056_; lean_object* v_unused_4057_; lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; 
v_unused_4053_ = lean_ctor_get(v_s_3979_, 7);
lean_dec(v_unused_4053_);
v_unused_4054_ = lean_ctor_get(v_s_3979_, 6);
lean_dec(v_unused_4054_);
v_unused_4055_ = lean_ctor_get(v_s_3979_, 5);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_s_3979_, 4);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_s_3979_, 3);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_s_3979_, 2);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_s_3979_, 1);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_s_3979_, 0);
lean_dec(v_unused_4060_);
v___x_3991_ = v_s_3979_;
v_isShared_3992_ = v_isSharedCheck_4052_;
goto v_resetjp_3990_;
}
else
{
lean_dec(v_s_3979_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4052_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v_v_3993_; lean_object* v_id_3994_; lean_object* v_ringId_x3f_3995_; lean_object* v_type_3996_; lean_object* v_u_3997_; lean_object* v_intModuleInst_3998_; lean_object* v_leInst_x3f_3999_; lean_object* v_ltInst_x3f_4000_; lean_object* v_lawfulOrderLTInst_x3f_4001_; lean_object* v_isPreorderInst_x3f_4002_; lean_object* v_orderedAddInst_x3f_4003_; lean_object* v_isLinearInst_x3f_4004_; lean_object* v_noNatDivInst_x3f_4005_; lean_object* v_ringInst_x3f_4006_; lean_object* v_commRingInst_x3f_4007_; lean_object* v_orderedRingInst_x3f_4008_; lean_object* v_fieldInst_x3f_4009_; lean_object* v_charInst_x3f_4010_; lean_object* v_zero_4011_; lean_object* v_ofNatZero_4012_; lean_object* v_one_x3f_4013_; lean_object* v_leFn_x3f_4014_; lean_object* v_ltFn_x3f_4015_; lean_object* v_addFn_4016_; lean_object* v_zsmulFn_4017_; lean_object* v_nsmulFn_4018_; lean_object* v_zsmulFn_x3f_4019_; lean_object* v_nsmulFn_x3f_4020_; lean_object* v_homomulFn_x3f_4021_; lean_object* v_subFn_4022_; lean_object* v_negFn_4023_; lean_object* v_vars_4024_; lean_object* v_varMap_4025_; lean_object* v_lowers_4026_; lean_object* v_uppers_4027_; lean_object* v_diseqs_4028_; lean_object* v_assignment_4029_; uint8_t v_caseSplits_4030_; lean_object* v_conflict_x3f_4031_; lean_object* v_diseqSplits_4032_; lean_object* v_elimEqs_4033_; lean_object* v_elimStack_4034_; lean_object* v_occurs_4035_; lean_object* v_ignored_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4051_; 
v_v_3993_ = lean_array_fget(v_structs_3980_, v_a_3977_);
v_id_3994_ = lean_ctor_get(v_v_3993_, 0);
v_ringId_x3f_3995_ = lean_ctor_get(v_v_3993_, 1);
v_type_3996_ = lean_ctor_get(v_v_3993_, 2);
v_u_3997_ = lean_ctor_get(v_v_3993_, 3);
v_intModuleInst_3998_ = lean_ctor_get(v_v_3993_, 4);
v_leInst_x3f_3999_ = lean_ctor_get(v_v_3993_, 5);
v_ltInst_x3f_4000_ = lean_ctor_get(v_v_3993_, 6);
v_lawfulOrderLTInst_x3f_4001_ = lean_ctor_get(v_v_3993_, 7);
v_isPreorderInst_x3f_4002_ = lean_ctor_get(v_v_3993_, 8);
v_orderedAddInst_x3f_4003_ = lean_ctor_get(v_v_3993_, 9);
v_isLinearInst_x3f_4004_ = lean_ctor_get(v_v_3993_, 10);
v_noNatDivInst_x3f_4005_ = lean_ctor_get(v_v_3993_, 11);
v_ringInst_x3f_4006_ = lean_ctor_get(v_v_3993_, 12);
v_commRingInst_x3f_4007_ = lean_ctor_get(v_v_3993_, 13);
v_orderedRingInst_x3f_4008_ = lean_ctor_get(v_v_3993_, 14);
v_fieldInst_x3f_4009_ = lean_ctor_get(v_v_3993_, 15);
v_charInst_x3f_4010_ = lean_ctor_get(v_v_3993_, 16);
v_zero_4011_ = lean_ctor_get(v_v_3993_, 17);
v_ofNatZero_4012_ = lean_ctor_get(v_v_3993_, 18);
v_one_x3f_4013_ = lean_ctor_get(v_v_3993_, 19);
v_leFn_x3f_4014_ = lean_ctor_get(v_v_3993_, 20);
v_ltFn_x3f_4015_ = lean_ctor_get(v_v_3993_, 21);
v_addFn_4016_ = lean_ctor_get(v_v_3993_, 22);
v_zsmulFn_4017_ = lean_ctor_get(v_v_3993_, 23);
v_nsmulFn_4018_ = lean_ctor_get(v_v_3993_, 24);
v_zsmulFn_x3f_4019_ = lean_ctor_get(v_v_3993_, 25);
v_nsmulFn_x3f_4020_ = lean_ctor_get(v_v_3993_, 26);
v_homomulFn_x3f_4021_ = lean_ctor_get(v_v_3993_, 27);
v_subFn_4022_ = lean_ctor_get(v_v_3993_, 28);
v_negFn_4023_ = lean_ctor_get(v_v_3993_, 29);
v_vars_4024_ = lean_ctor_get(v_v_3993_, 30);
v_varMap_4025_ = lean_ctor_get(v_v_3993_, 31);
v_lowers_4026_ = lean_ctor_get(v_v_3993_, 32);
v_uppers_4027_ = lean_ctor_get(v_v_3993_, 33);
v_diseqs_4028_ = lean_ctor_get(v_v_3993_, 34);
v_assignment_4029_ = lean_ctor_get(v_v_3993_, 35);
v_caseSplits_4030_ = lean_ctor_get_uint8(v_v_3993_, sizeof(void*)*42);
v_conflict_x3f_4031_ = lean_ctor_get(v_v_3993_, 36);
v_diseqSplits_4032_ = lean_ctor_get(v_v_3993_, 37);
v_elimEqs_4033_ = lean_ctor_get(v_v_3993_, 38);
v_elimStack_4034_ = lean_ctor_get(v_v_3993_, 39);
v_occurs_4035_ = lean_ctor_get(v_v_3993_, 40);
v_ignored_4036_ = lean_ctor_get(v_v_3993_, 41);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_v_3993_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4038_ = v_v_3993_;
v_isShared_4039_ = v_isSharedCheck_4051_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_ignored_4036_);
lean_inc(v_occurs_4035_);
lean_inc(v_elimStack_4034_);
lean_inc(v_elimEqs_4033_);
lean_inc(v_diseqSplits_4032_);
lean_inc(v_conflict_x3f_4031_);
lean_inc(v_assignment_4029_);
lean_inc(v_diseqs_4028_);
lean_inc(v_uppers_4027_);
lean_inc(v_lowers_4026_);
lean_inc(v_varMap_4025_);
lean_inc(v_vars_4024_);
lean_inc(v_negFn_4023_);
lean_inc(v_subFn_4022_);
lean_inc(v_homomulFn_x3f_4021_);
lean_inc(v_nsmulFn_x3f_4020_);
lean_inc(v_zsmulFn_x3f_4019_);
lean_inc(v_nsmulFn_4018_);
lean_inc(v_zsmulFn_4017_);
lean_inc(v_addFn_4016_);
lean_inc(v_ltFn_x3f_4015_);
lean_inc(v_leFn_x3f_4014_);
lean_inc(v_one_x3f_4013_);
lean_inc(v_ofNatZero_4012_);
lean_inc(v_zero_4011_);
lean_inc(v_charInst_x3f_4010_);
lean_inc(v_fieldInst_x3f_4009_);
lean_inc(v_orderedRingInst_x3f_4008_);
lean_inc(v_commRingInst_x3f_4007_);
lean_inc(v_ringInst_x3f_4006_);
lean_inc(v_noNatDivInst_x3f_4005_);
lean_inc(v_isLinearInst_x3f_4004_);
lean_inc(v_orderedAddInst_x3f_4003_);
lean_inc(v_isPreorderInst_x3f_4002_);
lean_inc(v_lawfulOrderLTInst_x3f_4001_);
lean_inc(v_ltInst_x3f_4000_);
lean_inc(v_leInst_x3f_3999_);
lean_inc(v_intModuleInst_3998_);
lean_inc(v_u_3997_);
lean_inc(v_type_3996_);
lean_inc(v_ringId_x3f_3995_);
lean_inc(v_id_3994_);
lean_dec(v_v_3993_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4051_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v_xs_x27_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4040_ = lean_box(0);
v_xs_x27_4041_ = lean_array_fset(v_structs_3980_, v_a_3977_, v___x_4040_);
v___x_4042_ = lean_box(1);
v___x_4043_ = l_Lean_PersistentArray_set___redArg(v_occurs_4035_, v_x_3978_, v___x_4042_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 40, v___x_4043_);
v___x_4045_ = v___x_4038_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_id_3994_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_ringId_x3f_3995_);
lean_ctor_set(v_reuseFailAlloc_4050_, 2, v_type_3996_);
lean_ctor_set(v_reuseFailAlloc_4050_, 3, v_u_3997_);
lean_ctor_set(v_reuseFailAlloc_4050_, 4, v_intModuleInst_3998_);
lean_ctor_set(v_reuseFailAlloc_4050_, 5, v_leInst_x3f_3999_);
lean_ctor_set(v_reuseFailAlloc_4050_, 6, v_ltInst_x3f_4000_);
lean_ctor_set(v_reuseFailAlloc_4050_, 7, v_lawfulOrderLTInst_x3f_4001_);
lean_ctor_set(v_reuseFailAlloc_4050_, 8, v_isPreorderInst_x3f_4002_);
lean_ctor_set(v_reuseFailAlloc_4050_, 9, v_orderedAddInst_x3f_4003_);
lean_ctor_set(v_reuseFailAlloc_4050_, 10, v_isLinearInst_x3f_4004_);
lean_ctor_set(v_reuseFailAlloc_4050_, 11, v_noNatDivInst_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4050_, 12, v_ringInst_x3f_4006_);
lean_ctor_set(v_reuseFailAlloc_4050_, 13, v_commRingInst_x3f_4007_);
lean_ctor_set(v_reuseFailAlloc_4050_, 14, v_orderedRingInst_x3f_4008_);
lean_ctor_set(v_reuseFailAlloc_4050_, 15, v_fieldInst_x3f_4009_);
lean_ctor_set(v_reuseFailAlloc_4050_, 16, v_charInst_x3f_4010_);
lean_ctor_set(v_reuseFailAlloc_4050_, 17, v_zero_4011_);
lean_ctor_set(v_reuseFailAlloc_4050_, 18, v_ofNatZero_4012_);
lean_ctor_set(v_reuseFailAlloc_4050_, 19, v_one_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4050_, 20, v_leFn_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4050_, 21, v_ltFn_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4050_, 22, v_addFn_4016_);
lean_ctor_set(v_reuseFailAlloc_4050_, 23, v_zsmulFn_4017_);
lean_ctor_set(v_reuseFailAlloc_4050_, 24, v_nsmulFn_4018_);
lean_ctor_set(v_reuseFailAlloc_4050_, 25, v_zsmulFn_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4050_, 26, v_nsmulFn_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4050_, 27, v_homomulFn_x3f_4021_);
lean_ctor_set(v_reuseFailAlloc_4050_, 28, v_subFn_4022_);
lean_ctor_set(v_reuseFailAlloc_4050_, 29, v_negFn_4023_);
lean_ctor_set(v_reuseFailAlloc_4050_, 30, v_vars_4024_);
lean_ctor_set(v_reuseFailAlloc_4050_, 31, v_varMap_4025_);
lean_ctor_set(v_reuseFailAlloc_4050_, 32, v_lowers_4026_);
lean_ctor_set(v_reuseFailAlloc_4050_, 33, v_uppers_4027_);
lean_ctor_set(v_reuseFailAlloc_4050_, 34, v_diseqs_4028_);
lean_ctor_set(v_reuseFailAlloc_4050_, 35, v_assignment_4029_);
lean_ctor_set(v_reuseFailAlloc_4050_, 36, v_conflict_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4050_, 37, v_diseqSplits_4032_);
lean_ctor_set(v_reuseFailAlloc_4050_, 38, v_elimEqs_4033_);
lean_ctor_set(v_reuseFailAlloc_4050_, 39, v_elimStack_4034_);
lean_ctor_set(v_reuseFailAlloc_4050_, 40, v___x_4043_);
lean_ctor_set(v_reuseFailAlloc_4050_, 41, v_ignored_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, sizeof(void*)*42, v_caseSplits_4030_);
v___x_4045_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4046_ = lean_array_fset(v_xs_x27_4041_, v_a_3977_, v___x_4045_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v___x_4046_);
v___x_4048_ = v___x_3991_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_typeIdOf_3981_);
lean_ctor_set(v_reuseFailAlloc_4049_, 2, v_exprToStructId_3982_);
lean_ctor_set(v_reuseFailAlloc_4049_, 3, v_exprToStructIdEntries_3983_);
lean_ctor_set(v_reuseFailAlloc_4049_, 4, v_forbiddenNatModules_3984_);
lean_ctor_set(v_reuseFailAlloc_4049_, 5, v_natStructs_3985_);
lean_ctor_set(v_reuseFailAlloc_4049_, 6, v_natTypeIdOf_3986_);
lean_ctor_set(v_reuseFailAlloc_4049_, 7, v_exprToNatStructId_3987_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4061_, lean_object* v_x_4062_, lean_object* v_s_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4061_, v_x_4062_, v_s_4063_);
lean_dec(v_x_4062_);
lean_dec(v_a_4061_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4065_, lean_object* v_x_4066_, lean_object* v_c_4067_, lean_object* v_init_4068_, lean_object* v_x_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
if (lean_obj_tag(v_x_4069_) == 0)
{
lean_object* v_k_4082_; lean_object* v_l_4083_; lean_object* v_r_4084_; lean_object* v___x_4085_; 
v_k_4082_ = lean_ctor_get(v_x_4069_, 1);
lean_inc(v_k_4082_);
v_l_4083_ = lean_ctor_get(v_x_4069_, 3);
lean_inc(v_l_4083_);
v_r_4084_ = lean_ctor_get(v_x_4069_, 4);
lean_inc(v_r_4084_);
lean_dec_ref_known(v_x_4069_, 5);
lean_inc_ref(v_c_4067_);
lean_inc(v_x_4066_);
lean_inc(v_a_4065_);
v___x_4085_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4065_, v_x_4066_, v_c_4067_, v_init_4068_, v_l_4083_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v___x_4086_; 
lean_dec_ref_known(v___x_4085_, 1);
lean_inc_ref(v_c_4067_);
lean_inc(v_x_4066_);
lean_inc(v_a_4065_);
v___x_4086_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4065_, v_x_4066_, v_c_4067_, v_k_4082_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v___x_4087_; 
lean_dec_ref_known(v___x_4086_, 1);
v___x_4087_ = lean_box(0);
v_init_4068_ = v___x_4087_;
v_x_4069_ = v_r_4084_;
goto _start;
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_r_4084_);
lean_dec_ref(v_c_4067_);
lean_dec(v_x_4066_);
lean_dec(v_a_4065_);
v_a_4089_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4086_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4086_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_dec(v_r_4084_);
lean_dec(v_k_4082_);
lean_dec_ref(v_c_4067_);
lean_dec(v_x_4066_);
lean_dec(v_a_4065_);
return v___x_4085_;
}
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec_ref(v_c_4067_);
lean_dec(v_x_4066_);
lean_dec(v_a_4065_);
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_init_4068_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4099_ = _args[0];
lean_object* v_x_4100_ = _args[1];
lean_object* v_c_4101_ = _args[2];
lean_object* v_init_4102_ = _args[3];
lean_object* v_x_4103_ = _args[4];
lean_object* v___y_4104_ = _args[5];
lean_object* v___y_4105_ = _args[6];
lean_object* v___y_4106_ = _args[7];
lean_object* v___y_4107_ = _args[8];
lean_object* v___y_4108_ = _args[9];
lean_object* v___y_4109_ = _args[10];
lean_object* v___y_4110_ = _args[11];
lean_object* v___y_4111_ = _args[12];
lean_object* v___y_4112_ = _args[13];
lean_object* v___y_4113_ = _args[14];
lean_object* v___y_4114_ = _args[15];
lean_object* v___y_4115_ = _args[16];
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4099_, v_x_4100_, v_c_4101_, v_init_4102_, v_x_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec(v___y_4104_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4117_, lean_object* v_x_4118_, lean_object* v_c_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v_occurs_4134_; lean_object* v_size_4135_; lean_object* v___f_4136_; lean_object* v___y_4138_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v_occurs_4134_ = lean_ctor_get(v_a_4133_, 40);
lean_inc_ref(v_occurs_4134_);
lean_dec(v_a_4133_);
v_size_4135_ = lean_ctor_get(v_occurs_4134_, 2);
lean_inc(v_x_4118_);
lean_inc(v_a_4120_);
v___f_4136_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4136_, 0, v_a_4120_);
lean_closure_set(v___f_4136_, 1, v_x_4118_);
v___x_4160_ = lean_box(1);
v___x_4161_ = lean_nat_dec_lt(v_x_4118_, v_size_4135_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; 
lean_dec_ref(v_occurs_4134_);
v___x_4162_ = l_outOfBounds___redArg(v___x_4160_);
v___y_4138_ = v___x_4162_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4160_, v_occurs_4134_, v_x_4118_);
lean_dec_ref(v_occurs_4134_);
v___y_4138_ = v___x_4163_;
goto v___jp_4137_;
}
v___jp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4140_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4139_, v___f_4136_, v_a_4121_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v___x_4141_; 
lean_dec_ref_known(v___x_4140_, 1);
lean_inc_ref(v_c_4119_);
lean_inc_n(v_x_4118_, 2);
lean_inc(v_a_4117_);
v___x_4141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4117_, v_x_4118_, v_c_4119_, v_x_4118_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec_ref_known(v___x_4141_, 1);
v___x_4142_ = lean_box(0);
v___x_4143_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4117_, v_x_4118_, v_c_4119_, v___x_4142_, v___y_4138_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v___x_4143_, 0);
lean_dec(v_unused_4151_);
v___x_4145_ = v___x_4143_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_dec(v___x_4143_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4142_);
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4142_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_a_4152_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4143_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4143_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_dec(v___y_4138_);
lean_dec_ref(v_c_4119_);
lean_dec(v_x_4118_);
lean_dec(v_a_4117_);
return v___x_4141_;
}
}
else
{
lean_dec(v___y_4138_);
lean_dec_ref(v_c_4119_);
lean_dec(v_x_4118_);
lean_dec(v_a_4117_);
return v___x_4140_;
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_c_4119_);
lean_dec(v_x_4118_);
lean_dec(v_a_4117_);
v_a_4164_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4132_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4132_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4172_, lean_object* v_x_4173_, lean_object* v_c_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4172_, v_x_4173_, v_c_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec(v_a_4175_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_p_4205_; 
v_p_4205_ = lean_ctor_get(v_c_4188_, 0);
if (lean_obj_tag(v_p_4205_) == 1)
{
lean_object* v_k_4206_; lean_object* v_v_4207_; lean_object* v_p_4208_; lean_object* v_y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_k_4206_ = lean_ctor_get(v_p_4205_, 0);
v_v_4207_ = lean_ctor_get(v_p_4205_, 1);
v_p_4208_ = lean_ctor_get(v_p_4205_, 2);
v___x_4259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4261_ = lean_int_dec_eq(v_k_4206_, v___x_4260_);
if (v___x_4261_ == 0)
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_int_dec_eq(v_k_4206_, v___x_4259_);
if (v___x_4262_ == 0)
{
goto v___jp_4201_;
}
else
{
if (lean_obj_tag(v_p_4208_) == 1)
{
lean_object* v_k_4263_; lean_object* v_v_4264_; lean_object* v_p_4265_; uint8_t v___x_4266_; 
v_k_4263_ = lean_ctor_get(v_p_4208_, 0);
v_v_4264_ = lean_ctor_get(v_p_4208_, 1);
v_p_4265_ = lean_ctor_get(v_p_4208_, 2);
v___x_4266_ = lean_int_dec_eq(v_k_4263_, v___x_4260_);
if (v___x_4266_ == 0)
{
goto v___jp_4201_;
}
else
{
if (lean_obj_tag(v_p_4265_) == 0)
{
v_y_4210_ = v_v_4264_;
v___y_4211_ = v_a_4189_;
v___y_4212_ = v_a_4190_;
v___y_4213_ = v_a_4191_;
v___y_4214_ = v_a_4192_;
v___y_4215_ = v_a_4193_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
goto v___jp_4209_;
}
else
{
goto v___jp_4201_;
}
}
}
else
{
goto v___jp_4201_;
}
}
}
else
{
if (lean_obj_tag(v_p_4208_) == 1)
{
lean_object* v_k_4267_; lean_object* v_v_4268_; lean_object* v_p_4269_; uint8_t v___x_4270_; 
v_k_4267_ = lean_ctor_get(v_p_4208_, 0);
v_v_4268_ = lean_ctor_get(v_p_4208_, 1);
v_p_4269_ = lean_ctor_get(v_p_4208_, 2);
v___x_4270_ = lean_int_dec_eq(v_k_4267_, v___x_4259_);
if (v___x_4270_ == 0)
{
goto v___jp_4201_;
}
else
{
if (lean_obj_tag(v_p_4269_) == 0)
{
v_y_4210_ = v_v_4268_;
v___y_4211_ = v_a_4189_;
v___y_4212_ = v_a_4190_;
v___y_4213_ = v_a_4191_;
v___y_4214_ = v_a_4192_;
v___y_4215_ = v_a_4193_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
goto v___jp_4209_;
}
else
{
goto v___jp_4201_;
}
}
}
else
{
goto v___jp_4201_;
}
}
v___jp_4209_:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4207_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v___x_4226_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4223_, v_a_4225_, v___y_4212_);
lean_dec(v_a_4225_);
lean_dec(v_a_4223_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4242_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4242_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4242_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_unbox(v_a_4227_);
lean_dec(v_a_4227_);
if (v___x_4231_ == 0)
{
uint8_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4232_ = 1;
v___x_4233_ = lean_box(v___x_4232_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4233_);
v___x_4235_ = v___x_4229_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
else
{
uint8_t v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4237_ = 0;
v___x_4238_ = lean_box(v___x_4237_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4238_);
v___x_4240_ = v___x_4229_;
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
}
}
else
{
return v___x_4226_;
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_a_4223_);
v_a_4243_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4224_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4224_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4222_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4222_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
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
}
else
{
goto v___jp_4201_;
}
v___jp_4201_:
{
uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = 0;
v___x_4203_ = lean_box(v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec_ref(v_c_4271_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4285_){
_start:
{
lean_object* v_p_4287_; 
v_p_4287_ = lean_ctor_get(v_c_4285_, 0);
if (lean_obj_tag(v_p_4287_) == 1)
{
lean_object* v_k_4288_; lean_object* v___x_4289_; uint8_t v___x_4290_; 
v_k_4288_ = lean_ctor_get(v_p_4287_, 0);
v___x_4289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4290_ = lean_int_dec_lt(v_k_4288_, v___x_4289_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; 
v___x_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4291_, 0, v_c_4285_);
return v___x_4291_;
}
else
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4287_);
v___x_4293_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4287_, v___x_4292_);
v___x_4294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4294_, 0, v_c_4285_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
else
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v_c_4285_);
return v___x_4297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4298_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4301_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec(v_a_4316_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4329_, lean_object* v_snd_4330_, lean_object* v_fst_4331_, lean_object* v_s_4332_){
_start:
{
lean_object* v_structs_4333_; lean_object* v_typeIdOf_4334_; lean_object* v_exprToStructId_4335_; lean_object* v_exprToStructIdEntries_4336_; lean_object* v_forbiddenNatModules_4337_; lean_object* v_natStructs_4338_; lean_object* v_natTypeIdOf_4339_; lean_object* v_exprToNatStructId_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_structs_4333_ = lean_ctor_get(v_s_4332_, 0);
v_typeIdOf_4334_ = lean_ctor_get(v_s_4332_, 1);
v_exprToStructId_4335_ = lean_ctor_get(v_s_4332_, 2);
v_exprToStructIdEntries_4336_ = lean_ctor_get(v_s_4332_, 3);
v_forbiddenNatModules_4337_ = lean_ctor_get(v_s_4332_, 4);
v_natStructs_4338_ = lean_ctor_get(v_s_4332_, 5);
v_natTypeIdOf_4339_ = lean_ctor_get(v_s_4332_, 6);
v_exprToNatStructId_4340_ = lean_ctor_get(v_s_4332_, 7);
v___x_4341_ = lean_array_get_size(v_structs_4333_);
v___x_4342_ = lean_nat_dec_lt(v___y_4329_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec(v_fst_4331_);
lean_dec_ref(v_snd_4330_);
return v_s_4332_;
}
else
{
lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4406_; 
lean_inc_ref(v_exprToNatStructId_4340_);
lean_inc_ref(v_natTypeIdOf_4339_);
lean_inc_ref(v_natStructs_4338_);
lean_inc_ref(v_forbiddenNatModules_4337_);
lean_inc_ref(v_exprToStructIdEntries_4336_);
lean_inc_ref(v_exprToStructId_4335_);
lean_inc_ref(v_typeIdOf_4334_);
lean_inc_ref(v_structs_4333_);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_s_4332_);
if (v_isSharedCheck_4406_ == 0)
{
lean_object* v_unused_4407_; lean_object* v_unused_4408_; lean_object* v_unused_4409_; lean_object* v_unused_4410_; lean_object* v_unused_4411_; lean_object* v_unused_4412_; lean_object* v_unused_4413_; lean_object* v_unused_4414_; 
v_unused_4407_ = lean_ctor_get(v_s_4332_, 7);
lean_dec(v_unused_4407_);
v_unused_4408_ = lean_ctor_get(v_s_4332_, 6);
lean_dec(v_unused_4408_);
v_unused_4409_ = lean_ctor_get(v_s_4332_, 5);
lean_dec(v_unused_4409_);
v_unused_4410_ = lean_ctor_get(v_s_4332_, 4);
lean_dec(v_unused_4410_);
v_unused_4411_ = lean_ctor_get(v_s_4332_, 3);
lean_dec(v_unused_4411_);
v_unused_4412_ = lean_ctor_get(v_s_4332_, 2);
lean_dec(v_unused_4412_);
v_unused_4413_ = lean_ctor_get(v_s_4332_, 1);
lean_dec(v_unused_4413_);
v_unused_4414_ = lean_ctor_get(v_s_4332_, 0);
lean_dec(v_unused_4414_);
v___x_4344_ = v_s_4332_;
v_isShared_4345_ = v_isSharedCheck_4406_;
goto v_resetjp_4343_;
}
else
{
lean_dec(v_s_4332_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4406_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_v_4346_; lean_object* v_id_4347_; lean_object* v_ringId_x3f_4348_; lean_object* v_type_4349_; lean_object* v_u_4350_; lean_object* v_intModuleInst_4351_; lean_object* v_leInst_x3f_4352_; lean_object* v_ltInst_x3f_4353_; lean_object* v_lawfulOrderLTInst_x3f_4354_; lean_object* v_isPreorderInst_x3f_4355_; lean_object* v_orderedAddInst_x3f_4356_; lean_object* v_isLinearInst_x3f_4357_; lean_object* v_noNatDivInst_x3f_4358_; lean_object* v_ringInst_x3f_4359_; lean_object* v_commRingInst_x3f_4360_; lean_object* v_orderedRingInst_x3f_4361_; lean_object* v_fieldInst_x3f_4362_; lean_object* v_charInst_x3f_4363_; lean_object* v_zero_4364_; lean_object* v_ofNatZero_4365_; lean_object* v_one_x3f_4366_; lean_object* v_leFn_x3f_4367_; lean_object* v_ltFn_x3f_4368_; lean_object* v_addFn_4369_; lean_object* v_zsmulFn_4370_; lean_object* v_nsmulFn_4371_; lean_object* v_zsmulFn_x3f_4372_; lean_object* v_nsmulFn_x3f_4373_; lean_object* v_homomulFn_x3f_4374_; lean_object* v_subFn_4375_; lean_object* v_negFn_4376_; lean_object* v_vars_4377_; lean_object* v_varMap_4378_; lean_object* v_lowers_4379_; lean_object* v_uppers_4380_; lean_object* v_diseqs_4381_; lean_object* v_assignment_4382_; uint8_t v_caseSplits_4383_; lean_object* v_conflict_x3f_4384_; lean_object* v_diseqSplits_4385_; lean_object* v_elimEqs_4386_; lean_object* v_elimStack_4387_; lean_object* v_occurs_4388_; lean_object* v_ignored_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4405_; 
v_v_4346_ = lean_array_fget(v_structs_4333_, v___y_4329_);
v_id_4347_ = lean_ctor_get(v_v_4346_, 0);
v_ringId_x3f_4348_ = lean_ctor_get(v_v_4346_, 1);
v_type_4349_ = lean_ctor_get(v_v_4346_, 2);
v_u_4350_ = lean_ctor_get(v_v_4346_, 3);
v_intModuleInst_4351_ = lean_ctor_get(v_v_4346_, 4);
v_leInst_x3f_4352_ = lean_ctor_get(v_v_4346_, 5);
v_ltInst_x3f_4353_ = lean_ctor_get(v_v_4346_, 6);
v_lawfulOrderLTInst_x3f_4354_ = lean_ctor_get(v_v_4346_, 7);
v_isPreorderInst_x3f_4355_ = lean_ctor_get(v_v_4346_, 8);
v_orderedAddInst_x3f_4356_ = lean_ctor_get(v_v_4346_, 9);
v_isLinearInst_x3f_4357_ = lean_ctor_get(v_v_4346_, 10);
v_noNatDivInst_x3f_4358_ = lean_ctor_get(v_v_4346_, 11);
v_ringInst_x3f_4359_ = lean_ctor_get(v_v_4346_, 12);
v_commRingInst_x3f_4360_ = lean_ctor_get(v_v_4346_, 13);
v_orderedRingInst_x3f_4361_ = lean_ctor_get(v_v_4346_, 14);
v_fieldInst_x3f_4362_ = lean_ctor_get(v_v_4346_, 15);
v_charInst_x3f_4363_ = lean_ctor_get(v_v_4346_, 16);
v_zero_4364_ = lean_ctor_get(v_v_4346_, 17);
v_ofNatZero_4365_ = lean_ctor_get(v_v_4346_, 18);
v_one_x3f_4366_ = lean_ctor_get(v_v_4346_, 19);
v_leFn_x3f_4367_ = lean_ctor_get(v_v_4346_, 20);
v_ltFn_x3f_4368_ = lean_ctor_get(v_v_4346_, 21);
v_addFn_4369_ = lean_ctor_get(v_v_4346_, 22);
v_zsmulFn_4370_ = lean_ctor_get(v_v_4346_, 23);
v_nsmulFn_4371_ = lean_ctor_get(v_v_4346_, 24);
v_zsmulFn_x3f_4372_ = lean_ctor_get(v_v_4346_, 25);
v_nsmulFn_x3f_4373_ = lean_ctor_get(v_v_4346_, 26);
v_homomulFn_x3f_4374_ = lean_ctor_get(v_v_4346_, 27);
v_subFn_4375_ = lean_ctor_get(v_v_4346_, 28);
v_negFn_4376_ = lean_ctor_get(v_v_4346_, 29);
v_vars_4377_ = lean_ctor_get(v_v_4346_, 30);
v_varMap_4378_ = lean_ctor_get(v_v_4346_, 31);
v_lowers_4379_ = lean_ctor_get(v_v_4346_, 32);
v_uppers_4380_ = lean_ctor_get(v_v_4346_, 33);
v_diseqs_4381_ = lean_ctor_get(v_v_4346_, 34);
v_assignment_4382_ = lean_ctor_get(v_v_4346_, 35);
v_caseSplits_4383_ = lean_ctor_get_uint8(v_v_4346_, sizeof(void*)*42);
v_conflict_x3f_4384_ = lean_ctor_get(v_v_4346_, 36);
v_diseqSplits_4385_ = lean_ctor_get(v_v_4346_, 37);
v_elimEqs_4386_ = lean_ctor_get(v_v_4346_, 38);
v_elimStack_4387_ = lean_ctor_get(v_v_4346_, 39);
v_occurs_4388_ = lean_ctor_get(v_v_4346_, 40);
v_ignored_4389_ = lean_ctor_get(v_v_4346_, 41);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_v_4346_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4391_ = v_v_4346_;
v_isShared_4392_ = v_isSharedCheck_4405_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_ignored_4389_);
lean_inc(v_occurs_4388_);
lean_inc(v_elimStack_4387_);
lean_inc(v_elimEqs_4386_);
lean_inc(v_diseqSplits_4385_);
lean_inc(v_conflict_x3f_4384_);
lean_inc(v_assignment_4382_);
lean_inc(v_diseqs_4381_);
lean_inc(v_uppers_4380_);
lean_inc(v_lowers_4379_);
lean_inc(v_varMap_4378_);
lean_inc(v_vars_4377_);
lean_inc(v_negFn_4376_);
lean_inc(v_subFn_4375_);
lean_inc(v_homomulFn_x3f_4374_);
lean_inc(v_nsmulFn_x3f_4373_);
lean_inc(v_zsmulFn_x3f_4372_);
lean_inc(v_nsmulFn_4371_);
lean_inc(v_zsmulFn_4370_);
lean_inc(v_addFn_4369_);
lean_inc(v_ltFn_x3f_4368_);
lean_inc(v_leFn_x3f_4367_);
lean_inc(v_one_x3f_4366_);
lean_inc(v_ofNatZero_4365_);
lean_inc(v_zero_4364_);
lean_inc(v_charInst_x3f_4363_);
lean_inc(v_fieldInst_x3f_4362_);
lean_inc(v_orderedRingInst_x3f_4361_);
lean_inc(v_commRingInst_x3f_4360_);
lean_inc(v_ringInst_x3f_4359_);
lean_inc(v_noNatDivInst_x3f_4358_);
lean_inc(v_isLinearInst_x3f_4357_);
lean_inc(v_orderedAddInst_x3f_4356_);
lean_inc(v_isPreorderInst_x3f_4355_);
lean_inc(v_lawfulOrderLTInst_x3f_4354_);
lean_inc(v_ltInst_x3f_4353_);
lean_inc(v_leInst_x3f_4352_);
lean_inc(v_intModuleInst_4351_);
lean_inc(v_u_4350_);
lean_inc(v_type_4349_);
lean_inc(v_ringId_x3f_4348_);
lean_inc(v_id_4347_);
lean_dec(v_v_4346_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4405_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; lean_object* v_xs_x27_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4393_ = lean_box(0);
v_xs_x27_4394_ = lean_array_fset(v_structs_4333_, v___y_4329_, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4395_, 0, v_snd_4330_);
v___x_4396_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4386_, v_fst_4331_, v___x_4395_);
v___x_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4397_, 0, v_fst_4331_);
lean_ctor_set(v___x_4397_, 1, v_elimStack_4387_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 39, v___x_4397_);
lean_ctor_set(v___x_4391_, 38, v___x_4396_);
v___x_4399_ = v___x_4391_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_id_4347_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_ringId_x3f_4348_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_type_4349_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_u_4350_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_intModuleInst_4351_);
lean_ctor_set(v_reuseFailAlloc_4404_, 5, v_leInst_x3f_4352_);
lean_ctor_set(v_reuseFailAlloc_4404_, 6, v_ltInst_x3f_4353_);
lean_ctor_set(v_reuseFailAlloc_4404_, 7, v_lawfulOrderLTInst_x3f_4354_);
lean_ctor_set(v_reuseFailAlloc_4404_, 8, v_isPreorderInst_x3f_4355_);
lean_ctor_set(v_reuseFailAlloc_4404_, 9, v_orderedAddInst_x3f_4356_);
lean_ctor_set(v_reuseFailAlloc_4404_, 10, v_isLinearInst_x3f_4357_);
lean_ctor_set(v_reuseFailAlloc_4404_, 11, v_noNatDivInst_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4404_, 12, v_ringInst_x3f_4359_);
lean_ctor_set(v_reuseFailAlloc_4404_, 13, v_commRingInst_x3f_4360_);
lean_ctor_set(v_reuseFailAlloc_4404_, 14, v_orderedRingInst_x3f_4361_);
lean_ctor_set(v_reuseFailAlloc_4404_, 15, v_fieldInst_x3f_4362_);
lean_ctor_set(v_reuseFailAlloc_4404_, 16, v_charInst_x3f_4363_);
lean_ctor_set(v_reuseFailAlloc_4404_, 17, v_zero_4364_);
lean_ctor_set(v_reuseFailAlloc_4404_, 18, v_ofNatZero_4365_);
lean_ctor_set(v_reuseFailAlloc_4404_, 19, v_one_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4404_, 20, v_leFn_x3f_4367_);
lean_ctor_set(v_reuseFailAlloc_4404_, 21, v_ltFn_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4404_, 22, v_addFn_4369_);
lean_ctor_set(v_reuseFailAlloc_4404_, 23, v_zsmulFn_4370_);
lean_ctor_set(v_reuseFailAlloc_4404_, 24, v_nsmulFn_4371_);
lean_ctor_set(v_reuseFailAlloc_4404_, 25, v_zsmulFn_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4404_, 26, v_nsmulFn_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4404_, 27, v_homomulFn_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4404_, 28, v_subFn_4375_);
lean_ctor_set(v_reuseFailAlloc_4404_, 29, v_negFn_4376_);
lean_ctor_set(v_reuseFailAlloc_4404_, 30, v_vars_4377_);
lean_ctor_set(v_reuseFailAlloc_4404_, 31, v_varMap_4378_);
lean_ctor_set(v_reuseFailAlloc_4404_, 32, v_lowers_4379_);
lean_ctor_set(v_reuseFailAlloc_4404_, 33, v_uppers_4380_);
lean_ctor_set(v_reuseFailAlloc_4404_, 34, v_diseqs_4381_);
lean_ctor_set(v_reuseFailAlloc_4404_, 35, v_assignment_4382_);
lean_ctor_set(v_reuseFailAlloc_4404_, 36, v_conflict_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4404_, 37, v_diseqSplits_4385_);
lean_ctor_set(v_reuseFailAlloc_4404_, 38, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4404_, 39, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4404_, 40, v_occurs_4388_);
lean_ctor_set(v_reuseFailAlloc_4404_, 41, v_ignored_4389_);
lean_ctor_set_uint8(v_reuseFailAlloc_4404_, sizeof(void*)*42, v_caseSplits_4383_);
v___x_4399_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4400_ = lean_array_fset(v_xs_x27_4394_, v___y_4329_, v___x_4399_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4400_);
v___x_4402_ = v___x_4344_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_typeIdOf_4334_);
lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_exprToStructId_4335_);
lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_exprToStructIdEntries_4336_);
lean_ctor_set(v_reuseFailAlloc_4403_, 4, v_forbiddenNatModules_4337_);
lean_ctor_set(v_reuseFailAlloc_4403_, 5, v_natStructs_4338_);
lean_ctor_set(v_reuseFailAlloc_4403_, 6, v_natTypeIdOf_4339_);
lean_ctor_set(v_reuseFailAlloc_4403_, 7, v_exprToNatStructId_4340_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4415_, lean_object* v_snd_4416_, lean_object* v_fst_4417_, lean_object* v_s_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4415_, v_snd_4416_, v_fst_4417_, v_s_4418_);
lean_dec(v___y_4415_);
return v_res_4419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4422_ = l_Lean_stringToMessageData(v___x_4421_);
return v___x_4422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4430_ = l_Lean_Name_append(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v_toCold_4510_; lean_object* v_options_4511_; lean_object* v_inheritedTraceOptions_4512_; uint8_t v_hasTrace_4513_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v_options_4530_; lean_object* v_inheritedTraceOptions_4531_; lean_object* v___y_4532_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; 
v_toCold_4510_ = lean_ctor_get(v_a_4441_, 0);
v_options_4511_ = lean_ctor_get(v_toCold_4510_, 2);
v_inheritedTraceOptions_4512_ = lean_ctor_get(v_toCold_4510_, 11);
v_hasTrace_4513_ = lean_ctor_get_uint8(v_options_4511_, sizeof(void*)*1);
if (v_hasTrace_4513_ == 0)
{
v___y_4549_ = v_a_4432_;
v___y_4550_ = v_a_4433_;
v___y_4551_ = v_a_4434_;
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
goto v___jp_4548_;
}
else
{
lean_object* v_cls_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v_cls_4657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4659_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4512_, v_options_4511_, v___x_4658_);
if (v___x_4659_ == 0)
{
v___y_4549_ = v_a_4432_;
v___y_4550_ = v_a_4433_;
v___y_4551_ = v_a_4434_;
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
goto v___jp_4548_;
}
else
{
lean_object* v___x_4660_; 
v___x_4660_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v___x_4662_ = l_Lean_MessageData_ofExpr(v_a_4661_);
v___x_4663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4657_, v___x_4662_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_dec_ref_known(v___x_4663_, 1);
v___y_4549_ = v_a_4432_;
v___y_4550_ = v_a_4433_;
v___y_4551_ = v_a_4434_;
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
goto v___jp_4548_;
}
else
{
lean_dec_ref(v_c_4431_);
return v___x_4663_;
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec_ref(v_c_4431_);
v_a_4664_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4660_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4660_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
v___jp_4444_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_box(0);
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
return v___x_4446_;
}
v___jp_4447_:
{
lean_object* v___f_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_inc(v___y_4453_);
v___f_4464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4464_, 0, v___y_4453_);
lean_closure_set(v___f_4464_, 1, v___y_4448_);
lean_closure_set(v___f_4464_, 2, v___y_4449_);
v___x_4465_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4466_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4465_, v___f_4464_, v___y_4454_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4467_; 
lean_dec_ref_known(v___x_4466_, 1);
v___x_4467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4452_, v___y_4451_, v___y_4450_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4467_;
}
else
{
lean_dec(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v___x_4466_;
}
}
v___jp_4468_:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; uint8_t v_caseSplits_4487_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v_caseSplits_4487_ = lean_ctor_get_uint8(v_a_4486_, sizeof(void*)*42);
lean_dec(v_a_4486_);
if (v_caseSplits_4487_ == 0)
{
lean_object* v___x_4488_; 
v___x_4488_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4471_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; uint8_t v___x_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = lean_unbox(v_a_4489_);
lean_dec(v_a_4489_);
if (v___x_4490_ == 0)
{
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
v___y_4450_ = v___y_4471_;
v___y_4451_ = v___y_4472_;
v___y_4452_ = v___y_4473_;
v___y_4453_ = v___y_4474_;
v___y_4454_ = v___y_4475_;
v___y_4455_ = v___y_4476_;
v___y_4456_ = v___y_4477_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
goto v___jp_4447_;
}
else
{
lean_object* v___x_4491_; lean_object* v_a_4492_; lean_object* v___x_4493_; 
lean_inc_ref(v___y_4471_);
v___x_4491_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4471_);
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref(v___x_4491_);
v___x_4493_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4492_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_dec_ref_known(v___x_4493_, 1);
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
v___y_4450_ = v___y_4471_;
v___y_4451_ = v___y_4472_;
v___y_4452_ = v___y_4473_;
v___y_4453_ = v___y_4474_;
v___y_4454_ = v___y_4475_;
v___y_4455_ = v___y_4476_;
v___y_4456_ = v___y_4477_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
goto v___jp_4447_;
}
else
{
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
return v___x_4493_;
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
v_a_4494_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4488_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4488_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
v___y_4450_ = v___y_4471_;
v___y_4451_ = v___y_4472_;
v___y_4452_ = v___y_4473_;
v___y_4453_ = v___y_4474_;
v___y_4454_ = v___y_4475_;
v___y_4455_ = v___y_4476_;
v___y_4456_ = v___y_4477_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
goto v___jp_4447_;
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
v_a_4502_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4485_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4485_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
v___jp_4514_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4531_, v_options_4530_, v___x_4534_);
if (v___x_4535_ == 0)
{
v___y_4469_ = v___y_4515_;
v___y_4470_ = v___y_4516_;
v___y_4471_ = v___y_4517_;
v___y_4472_ = v___y_4518_;
v___y_4473_ = v___y_4519_;
v___y_4474_ = v___y_4520_;
v___y_4475_ = v___y_4521_;
v___y_4476_ = v___y_4522_;
v___y_4477_ = v___y_4523_;
v___y_4478_ = v___y_4524_;
v___y_4479_ = v___y_4525_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v___y_4527_;
v___y_4482_ = v___y_4528_;
v___y_4483_ = v___y_4529_;
v___y_4484_ = v___y_4532_;
goto v___jp_4468_;
}
else
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4517_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4532_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = l_Lean_MessageData_ofExpr(v_a_4537_);
v___x_4539_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4533_, v___x_4538_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4532_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_dec_ref_known(v___x_4539_, 1);
v___y_4469_ = v___y_4515_;
v___y_4470_ = v___y_4516_;
v___y_4471_ = v___y_4517_;
v___y_4472_ = v___y_4518_;
v___y_4473_ = v___y_4519_;
v___y_4474_ = v___y_4520_;
v___y_4475_ = v___y_4521_;
v___y_4476_ = v___y_4522_;
v___y_4477_ = v___y_4523_;
v___y_4478_ = v___y_4524_;
v___y_4479_ = v___y_4525_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v___y_4527_;
v___y_4482_ = v___y_4528_;
v___y_4483_ = v___y_4529_;
v___y_4484_ = v___y_4532_;
goto v___jp_4468_;
}
else
{
lean_dec(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v___x_4539_;
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
v_a_4540_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4536_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4536_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
}
v___jp_4548_:
{
lean_object* v___x_4560_; 
lean_inc_ref(v___y_4558_);
v___x_4560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4431_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v_p_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
v_p_4562_ = lean_ctor_get(v_a_4561_, 0);
v___x_4563_ = lean_box(0);
v___x_4564_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4562_, v___x_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4561_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v_snd_4567_; lean_object* v_toCold_4568_; lean_object* v_options_4569_; uint8_t v_hasTrace_4570_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v_snd_4567_ = lean_ctor_get(v_a_4566_, 1);
lean_inc(v_snd_4567_);
v_toCold_4568_ = lean_ctor_get(v___y_4558_, 0);
v_options_4569_ = lean_ctor_get(v_toCold_4568_, 2);
v_hasTrace_4570_ = lean_ctor_get_uint8(v_options_4569_, sizeof(void*)*1);
if (v_hasTrace_4570_ == 0)
{
lean_object* v_fst_4571_; lean_object* v_fst_4572_; lean_object* v_snd_4573_; 
v_fst_4571_ = lean_ctor_get(v_a_4566_, 0);
lean_inc(v_fst_4571_);
lean_dec(v_a_4566_);
v_fst_4572_ = lean_ctor_get(v_snd_4567_, 0);
lean_inc_n(v_fst_4572_, 2);
v_snd_4573_ = lean_ctor_get(v_snd_4567_, 1);
lean_inc_n(v_snd_4573_, 2);
lean_dec(v_snd_4567_);
v___y_4469_ = v_snd_4573_;
v___y_4470_ = v_fst_4572_;
v___y_4471_ = v_snd_4573_;
v___y_4472_ = v_fst_4572_;
v___y_4473_ = v_fst_4571_;
v___y_4474_ = v___y_4549_;
v___y_4475_ = v___y_4550_;
v___y_4476_ = v___y_4551_;
v___y_4477_ = v___y_4552_;
v___y_4478_ = v___y_4553_;
v___y_4479_ = v___y_4554_;
v___y_4480_ = v___y_4555_;
v___y_4481_ = v___y_4556_;
v___y_4482_ = v___y_4557_;
v___y_4483_ = v___y_4558_;
v___y_4484_ = v___y_4559_;
goto v___jp_4468_;
}
else
{
lean_object* v_fst_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4620_; 
v_fst_4574_ = lean_ctor_get(v_a_4566_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_a_4566_);
if (v_isSharedCheck_4620_ == 0)
{
lean_object* v_unused_4621_; 
v_unused_4621_ = lean_ctor_get(v_a_4566_, 1);
lean_dec(v_unused_4621_);
v___x_4576_ = v_a_4566_;
v_isShared_4577_ = v_isSharedCheck_4620_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_fst_4574_);
lean_dec(v_a_4566_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4620_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_fst_4578_; lean_object* v_snd_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4619_; 
v_fst_4578_ = lean_ctor_get(v_snd_4567_, 0);
v_snd_4579_ = lean_ctor_get(v_snd_4567_, 1);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_snd_4567_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4581_ = v_snd_4567_;
v_isShared_4582_ = v_isSharedCheck_4619_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_snd_4579_);
lean_inc(v_fst_4578_);
lean_dec(v_snd_4567_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4619_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v_inheritedTraceOptions_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; 
v_inheritedTraceOptions_4583_ = lean_ctor_get(v_toCold_4568_, 11);
v___x_4584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4583_, v_options_4569_, v___x_4585_);
if (v___x_4586_ == 0)
{
lean_del_object(v___x_4581_);
lean_del_object(v___x_4576_);
lean_inc(v_fst_4578_);
lean_inc(v_snd_4579_);
v___y_4515_ = v_snd_4579_;
v___y_4516_ = v_fst_4578_;
v___y_4517_ = v_snd_4579_;
v___y_4518_ = v_fst_4578_;
v___y_4519_ = v_fst_4574_;
v___y_4520_ = v___y_4549_;
v___y_4521_ = v___y_4550_;
v___y_4522_ = v___y_4551_;
v___y_4523_ = v___y_4552_;
v___y_4524_ = v___y_4553_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v_options_4530_ = v_options_4569_;
v_inheritedTraceOptions_4531_ = v_inheritedTraceOptions_4583_;
v___y_4532_ = v___y_4559_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4578_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4589_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v___x_4589_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4579_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref_known(v___x_4589_, 1);
v___x_4591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4592_ = l_Lean_MessageData_ofExpr(v_a_4588_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 7);
lean_ctor_set(v___x_4581_, 1, v___x_4592_);
lean_ctor_set(v___x_4581_, 0, v___x_4591_);
v___x_4594_ = v___x_4581_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4577_ == 0)
{
lean_ctor_set_tag(v___x_4576_, 7);
lean_ctor_set(v___x_4576_, 1, v___x_4595_);
lean_ctor_set(v___x_4576_, 0, v___x_4594_);
v___x_4597_ = v___x_4576_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4598_ = l_Lean_MessageData_ofExpr(v_a_4590_);
v___x_4599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4584_, v___x_4599_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_dec_ref_known(v___x_4600_, 1);
lean_inc(v_fst_4578_);
lean_inc(v_snd_4579_);
v___y_4515_ = v_snd_4579_;
v___y_4516_ = v_fst_4578_;
v___y_4517_ = v_snd_4579_;
v___y_4518_ = v_fst_4578_;
v___y_4519_ = v_fst_4574_;
v___y_4520_ = v___y_4549_;
v___y_4521_ = v___y_4550_;
v___y_4522_ = v___y_4551_;
v___y_4523_ = v___y_4552_;
v___y_4524_ = v___y_4553_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v_options_4530_ = v_options_4569_;
v_inheritedTraceOptions_4531_ = v_inheritedTraceOptions_4583_;
v___y_4532_ = v___y_4559_;
goto v___jp_4514_;
}
else
{
lean_dec(v_snd_4579_);
lean_dec(v_fst_4578_);
lean_dec(v_fst_4574_);
return v___x_4600_;
}
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec(v_a_4588_);
lean_del_object(v___x_4581_);
lean_dec(v_snd_4579_);
lean_dec(v_fst_4578_);
lean_del_object(v___x_4576_);
lean_dec(v_fst_4574_);
v_a_4603_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4589_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4589_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_del_object(v___x_4581_);
lean_dec(v_snd_4579_);
lean_dec(v_fst_4578_);
lean_del_object(v___x_4576_);
lean_dec(v_fst_4574_);
v_a_4611_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4587_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4587_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
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
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
v_a_4622_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4565_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4565_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
else
{
lean_object* v_toCold_4630_; lean_object* v_options_4631_; uint8_t v_hasTrace_4632_; 
v_toCold_4630_ = lean_ctor_get(v___y_4558_, 0);
v_options_4631_ = lean_ctor_get(v_toCold_4630_, 2);
v_hasTrace_4632_ = lean_ctor_get_uint8(v_options_4631_, sizeof(void*)*1);
if (v_hasTrace_4632_ == 0)
{
lean_dec(v_a_4561_);
goto v___jp_4444_;
}
else
{
lean_object* v_inheritedTraceOptions_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v_inheritedTraceOptions_4633_ = lean_ctor_get(v_toCold_4630_, 11);
v___x_4634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4633_, v_options_4631_, v___x_4635_);
if (v___x_4636_ == 0)
{
lean_dec(v_a_4561_);
goto v___jp_4444_;
}
else
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4561_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v_a_4561_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
v___x_4639_ = l_Lean_MessageData_ofExpr(v_a_4638_);
v___x_4640_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4634_, v___x_4639_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_dec_ref_known(v___x_4640_, 1);
goto v___jp_4444_;
}
else
{
return v___x_4640_;
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
v_a_4641_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4637_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4637_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
v_a_4649_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4560_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4560_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec(v_a_4674_);
lean_dec(v_a_4673_);
return v_res_4685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_cls_4690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4692_ = l_Lean_Name_append(v___x_4691_, v_cls_4690_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4693_, lean_object* v_b_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v_toCold_4703_; lean_object* v_options_4704_; uint8_t v_hasTrace_4705_; 
v_toCold_4703_ = lean_ctor_get(v_a_4697_, 0);
v_options_4704_ = lean_ctor_get(v_toCold_4703_, 2);
v_hasTrace_4705_ = lean_ctor_get_uint8(v_options_4704_, sizeof(void*)*1);
if (v_hasTrace_4705_ == 0)
{
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
goto v___jp_4700_;
}
else
{
lean_object* v_inheritedTraceOptions_4706_; lean_object* v_cls_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4706_ = lean_ctor_get(v_toCold_4703_, 11);
v_cls_4707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4706_, v_options_4704_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
goto v___jp_4700_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4710_ = l_Lean_MessageData_ofExpr(v_a_4693_);
v___x_4711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = l_Lean_MessageData_ofExpr(v_b_4694_);
v___x_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4707_, v___x_4714_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
return v___x_4715_;
}
}
v___jp_4700_:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
return v___x_4702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4716_, lean_object* v_b_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4716_, v_b_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
lean_dec(v_a_4719_);
lean_dec_ref(v_a_4718_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4724_, lean_object* v_b_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v___x_4738_; 
v___x_4738_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4724_, v_b_4725_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4739_, lean_object* v_b_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4739_, v_b_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec(v_a_4741_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4754_, lean_object* v_b_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4754_, v_a_4757_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; uint8_t v___x_4770_; lean_object* v___x_4771_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4768_, 1);
v___x_4770_ = 0;
lean_inc_ref(v_a_4754_);
v___x_4771_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4754_, v___x_4770_, v_a_4769_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4821_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4821_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4821_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
if (lean_obj_tag(v_a_4772_) == 1)
{
lean_object* v_val_4776_; lean_object* v___x_4777_; 
lean_del_object(v___x_4774_);
v_val_4776_ = lean_ctor_get(v_a_4772_, 0);
lean_inc(v_val_4776_);
lean_dec_ref_known(v_a_4772_, 1);
v___x_4777_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4755_, v_a_4757_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4779_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v___x_4777_, 1);
lean_inc_ref(v_b_4755_);
v___x_4779_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4755_, v___x_4770_, v_a_4778_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4800_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4800_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4800_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
if (lean_obj_tag(v_a_4780_) == 1)
{
lean_object* v_val_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_val_4784_ = lean_ctor_get(v_a_4780_, 0);
lean_inc_n(v_val_4784_, 2);
lean_dec_ref_known(v_a_4780_, 1);
lean_inc(v_val_4776_);
v___x_4785_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4785_, 0, v_val_4776_);
lean_ctor_set(v___x_4785_, 1, v_val_4784_);
v___x_4786_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4785_);
v___x_4787_ = lean_box(0);
v___x_4788_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4786_, v___x_4787_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_del_object(v___x_4782_);
v___x_4789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4789_, 0, v_a_4754_);
lean_ctor_set(v___x_4789_, 1, v_b_4755_);
lean_ctor_set(v___x_4789_, 2, v_val_4776_);
lean_ctor_set(v___x_4789_, 3, v_val_4784_);
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4786_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4790_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
return v___x_4791_;
}
else
{
lean_object* v___x_4792_; lean_object* v___x_4794_; 
lean_dec(v___x_4786_);
lean_dec(v_val_4784_);
lean_dec(v_val_4776_);
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v___x_4792_ = lean_box(0);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4792_);
v___x_4794_ = v___x_4782_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4792_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
else
{
lean_object* v___x_4796_; lean_object* v___x_4798_; 
lean_dec(v_a_4780_);
lean_dec(v_val_4776_);
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v___x_4796_ = lean_box(0);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4796_);
v___x_4798_ = v___x_4782_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_val_4776_);
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v_a_4801_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4779_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4779_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
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
lean_dec(v_val_4776_);
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v_a_4809_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4777_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4777_);
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
lean_object* v___x_4817_; lean_object* v___x_4819_; 
lean_dec(v_a_4772_);
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v___x_4817_ = lean_box(0);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4817_);
v___x_4819_ = v___x_4774_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
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
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v_a_4822_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4771_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4771_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
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
lean_dec_ref(v_b_4755_);
lean_dec_ref(v_a_4754_);
v_a_4830_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4768_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4768_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4838_, lean_object* v_b_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4838_, v_b_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec(v_a_4840_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4853_, lean_object* v_b_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4869_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref_known(v___x_4867_, 1);
lean_inc_ref(v_a_4853_);
v___x_4869_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4853_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v_fst_4871_; lean_object* v___x_4872_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v_fst_4871_ = lean_ctor_get(v_a_4870_, 0);
lean_inc(v_fst_4871_);
lean_dec(v_a_4870_);
lean_inc_ref(v_b_4854_);
v___x_4872_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v_fst_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4957_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
v_fst_4874_ = lean_ctor_get(v_a_4873_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v_a_4873_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v_a_4873_, 1);
lean_dec(v_unused_4958_);
v___x_4876_ = v_a_4873_;
v_isShared_4877_ = v_isSharedCheck_4957_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_fst_4874_);
lean_dec(v_a_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4957_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4853_, v_a_4856_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v_id_4880_; lean_object* v_structId_4881_; uint8_t v___x_4882_; lean_object* v___x_4883_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4878_, 1);
v_id_4880_ = lean_ctor_get(v_a_4868_, 0);
lean_inc(v_id_4880_);
v_structId_4881_ = lean_ctor_get(v_a_4868_, 1);
lean_inc(v_structId_4881_);
lean_dec(v_a_4868_);
v___x_4882_ = 0;
v___x_4883_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4871_, v___x_4882_, v_a_4879_, v_structId_4881_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4940_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4940_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4940_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
if (lean_obj_tag(v_a_4884_) == 1)
{
lean_object* v_val_4888_; lean_object* v___x_4889_; 
lean_del_object(v___x_4886_);
v_val_4888_ = lean_ctor_get(v_a_4884_, 0);
lean_inc(v_val_4888_);
lean_dec_ref_known(v_a_4884_, 1);
v___x_4889_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4854_, v_a_4856_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4874_, v___x_4882_, v_a_4890_, v_structId_4881_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4919_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4919_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4919_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
if (lean_obj_tag(v_a_4892_) == 1)
{
lean_object* v_val_4896_; lean_object* v___x_4898_; 
v_val_4896_ = lean_ctor_get(v_a_4892_, 0);
lean_inc_n(v_val_4896_, 2);
lean_dec_ref_known(v_a_4892_, 1);
lean_inc(v_val_4888_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 3);
lean_ctor_set(v___x_4876_, 1, v_val_4896_);
lean_ctor_set(v___x_4876_, 0, v_val_4888_);
v___x_4898_ = v___x_4876_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_val_4888_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v_val_4896_);
v___x_4898_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4899_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4898_);
v___x_4900_ = lean_box(0);
v___x_4901_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4899_, v___x_4900_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
lean_del_object(v___x_4894_);
lean_inc(v_val_4896_);
lean_inc(v_val_4888_);
lean_inc(v_id_4880_);
lean_inc_ref(v_b_4854_);
lean_inc_ref(v_a_4853_);
v___x_4902_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4902_, 0, v_a_4853_);
lean_ctor_set(v___x_4902_, 1, v_b_4854_);
lean_ctor_set(v___x_4902_, 2, v_id_4880_);
lean_ctor_set(v___x_4902_, 3, v_val_4888_);
lean_ctor_set(v___x_4902_, 4, v_val_4896_);
lean_inc(v___x_4899_);
v___x_4903_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4903_, 0, v___x_4899_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
lean_ctor_set_uint8(v___x_4903_, sizeof(void*)*2, v___x_4882_);
v___x_4904_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4903_, v_structId_4881_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec_ref_known(v___x_4904_, 1);
v___x_4905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4906_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4899_, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4907_, 0, v_b_4854_);
lean_ctor_set(v___x_4907_, 1, v_a_4853_);
lean_ctor_set(v___x_4907_, 2, v_id_4880_);
lean_ctor_set(v___x_4907_, 3, v_val_4896_);
lean_ctor_set(v___x_4907_, 4, v_val_4888_);
v___x_4908_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4908_, 0, v___x_4906_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*2, v___x_4882_);
v___x_4909_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4908_, v_structId_4881_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
lean_dec(v_structId_4881_);
return v___x_4909_;
}
else
{
lean_dec(v___x_4899_);
lean_dec(v_val_4896_);
lean_dec(v_val_4888_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
return v___x_4904_;
}
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
lean_dec(v___x_4899_);
lean_dec(v_val_4896_);
lean_dec(v_val_4888_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v___x_4910_ = lean_box(0);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4910_);
v___x_4912_ = v___x_4894_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4917_; 
lean_dec(v_a_4892_);
lean_dec(v_val_4888_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_del_object(v___x_4876_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v___x_4915_ = lean_box(0);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4915_);
v___x_4917_ = v___x_4894_;
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
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
lean_dec(v_val_4888_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_del_object(v___x_4876_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4920_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4891_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4891_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
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
lean_dec(v_val_4888_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_del_object(v___x_4876_);
lean_dec(v_fst_4874_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4928_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4889_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4889_);
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
lean_object* v___x_4936_; lean_object* v___x_4938_; 
lean_dec(v_a_4884_);
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_del_object(v___x_4876_);
lean_dec(v_fst_4874_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v___x_4936_ = lean_box(0);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v___x_4936_);
v___x_4938_ = v___x_4886_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
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
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_structId_4881_);
lean_dec(v_id_4880_);
lean_del_object(v___x_4876_);
lean_dec(v_fst_4874_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4941_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4883_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4883_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
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
lean_del_object(v___x_4876_);
lean_dec(v_fst_4874_);
lean_dec(v_fst_4871_);
lean_dec(v_a_4868_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4949_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4878_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4878_);
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
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v_fst_4871_);
lean_dec(v_a_4868_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4959_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4872_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4872_);
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
lean_dec(v_a_4868_);
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4967_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4869_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4869_);
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
lean_dec_ref(v_b_4854_);
lean_dec_ref(v_a_4853_);
v_a_4975_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4867_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4867_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4983_, lean_object* v_b_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4983_, v_b_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec(v_a_4986_);
lean_dec(v_a_4985_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_4998_, lean_object* v_b_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5014_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5012_, 1);
lean_inc_ref(v_a_4998_);
v___x_5014_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4998_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v_fst_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5112_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
v_fst_5016_ = lean_ctor_get(v_a_5015_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_a_5015_);
if (v_isSharedCheck_5112_ == 0)
{
lean_object* v_unused_5113_; 
v_unused_5113_ = lean_ctor_get(v_a_5015_, 1);
lean_dec(v_unused_5113_);
v___x_5018_ = v_a_5015_;
v_isShared_5019_ = v_isSharedCheck_5112_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_fst_5016_);
lean_dec(v_a_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5112_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5020_; 
lean_inc_ref(v_b_4999_);
v___x_5020_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v_fst_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5102_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5020_, 1);
v_fst_5022_ = lean_ctor_get(v_a_5021_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v_a_5021_);
if (v_isSharedCheck_5102_ == 0)
{
lean_object* v_unused_5103_; 
v_unused_5103_ = lean_ctor_get(v_a_5021_, 1);
lean_dec(v_unused_5103_);
v___x_5024_ = v_a_5021_;
v_isShared_5025_ = v_isSharedCheck_5102_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_fst_5022_);
lean_dec(v_a_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5102_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4998_, v_a_5001_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v_id_5028_; lean_object* v_structId_5029_; uint8_t v___x_5030_; lean_object* v___x_5031_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5026_, 1);
v_id_5028_ = lean_ctor_get(v_a_5013_, 0);
lean_inc(v_id_5028_);
v_structId_5029_ = lean_ctor_get(v_a_5013_, 1);
lean_inc(v_structId_5029_);
lean_dec(v_a_5013_);
v___x_5030_ = 0;
v___x_5031_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5016_, v___x_5030_, v_a_5027_, v_structId_5029_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5085_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5085_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5085_;
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
v___x_5037_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4999_, v_a_5001_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5039_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_a_5038_);
lean_dec_ref_known(v___x_5037_, 1);
v___x_5039_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5022_, v___x_5030_, v_a_5038_, v_structId_5029_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5064_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5064_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5064_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
if (lean_obj_tag(v_a_5040_) == 1)
{
lean_object* v_val_5044_; lean_object* v___x_5046_; 
v_val_5044_ = lean_ctor_get(v_a_5040_, 0);
lean_inc_n(v_val_5044_, 2);
lean_dec_ref_known(v_a_5040_, 1);
lean_inc(v_val_5036_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 3);
lean_ctor_set(v___x_5024_, 1, v_val_5044_);
lean_ctor_set(v___x_5024_, 0, v_val_5036_);
v___x_5046_ = v___x_5024_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_val_5036_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_val_5044_);
v___x_5046_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5047_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5046_);
v___x_5048_ = lean_box(0);
v___x_5049_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5047_, v___x_5048_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; lean_object* v___x_5052_; 
lean_del_object(v___x_5042_);
v___x_5050_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5050_, 0, v_a_4998_);
lean_ctor_set(v___x_5050_, 1, v_b_4999_);
lean_ctor_set(v___x_5050_, 2, v_id_5028_);
lean_ctor_set(v___x_5050_, 3, v_val_5036_);
lean_ctor_set(v___x_5050_, 4, v_val_5044_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 1, v___x_5050_);
lean_ctor_set(v___x_5018_, 0, v___x_5047_);
v___x_5052_ = v___x_5018_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5047_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; 
v___x_5053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5052_, v_structId_5029_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_structId_5029_);
return v___x_5053_;
}
}
else
{
lean_object* v___x_5055_; lean_object* v___x_5057_; 
lean_dec(v___x_5047_);
lean_dec(v_val_5044_);
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v___x_5055_ = lean_box(0);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5055_);
v___x_5057_ = v___x_5042_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
lean_dec(v_a_5040_);
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v___x_5060_ = lean_box(0);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5060_);
v___x_5062_ = v___x_5042_;
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
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5065_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5039_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5039_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
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
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5073_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5037_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5037_);
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
lean_object* v___x_5081_; lean_object* v___x_5083_; 
lean_dec(v_a_5032_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v___x_5081_ = lean_box(0);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5081_);
v___x_5083_ = v___x_5034_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5081_);
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
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_del_object(v___x_5018_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5086_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5031_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5031_);
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
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_del_object(v___x_5018_);
lean_dec(v_fst_5016_);
lean_dec(v_a_5013_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5094_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5026_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5026_);
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
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_del_object(v___x_5018_);
lean_dec(v_fst_5016_);
lean_dec(v_a_5013_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5104_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5020_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5020_);
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
lean_dec(v_a_5013_);
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5114_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5014_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5014_);
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
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec_ref(v_b_4999_);
lean_dec_ref(v_a_4998_);
v_a_5122_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5012_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5012_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5130_, lean_object* v_b_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5130_, v_b_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec_ref(v_a_5139_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
lean_dec(v_a_5134_);
lean_dec(v_a_5133_);
lean_dec(v_a_5132_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5145_, lean_object* v_b_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
size_t v___x_5158_; size_t v___x_5159_; uint8_t v___x_5160_; 
v___x_5158_ = lean_ptr_addr(v_a_5145_);
v___x_5159_ = lean_ptr_addr(v_b_5146_);
v___x_5160_ = lean_usize_dec_eq(v___x_5158_, v___x_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; 
v___x_5161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5145_, v_b_5146_, v_a_5147_, v_a_5155_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
if (lean_obj_tag(v_a_5162_) == 1)
{
lean_object* v_val_5163_; lean_object* v___x_5164_; 
v_val_5163_ = lean_ctor_get(v_a_5162_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v_a_5162_, 1);
v___x_5164_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; uint8_t v___x_5166_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5165_);
lean_dec_ref_known(v___x_5164_, 1);
v___x_5166_ = lean_unbox(v_a_5165_);
lean_dec(v_a_5165_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; uint8_t v___x_5169_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
v___x_5169_ = lean_unbox(v_a_5168_);
lean_dec(v_a_5168_);
if (v___x_5169_ == 0)
{
lean_object* v___x_5170_; 
v___x_5170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5145_, v_b_5146_, v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_val_5163_);
return v___x_5170_;
}
else
{
lean_object* v___x_5171_; 
lean_dec(v_val_5163_);
v___x_5171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5145_, v_b_5146_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
return v___x_5171_;
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec(v_val_5163_);
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5172_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5167_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5167_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
else
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; uint8_t v___x_5182_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc(v_a_5181_);
lean_dec_ref_known(v___x_5180_, 1);
v___x_5182_ = lean_unbox(v_a_5181_);
lean_dec(v_a_5181_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; 
v___x_5183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5145_, v_b_5146_, v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_val_5163_);
return v___x_5183_;
}
else
{
lean_object* v___x_5184_; 
v___x_5184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5145_, v_b_5146_, v_val_5163_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_val_5163_);
return v___x_5184_;
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
lean_dec(v_val_5163_);
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5185_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5180_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5180_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec(v_val_5163_);
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5193_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5164_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5164_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v___x_5201_; 
lean_dec(v_a_5162_);
v___x_5201_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5145_, v_b_5146_, v_a_5147_, v_a_5155_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5224_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5204_ = v___x_5201_;
v_isShared_5205_ = v_isSharedCheck_5224_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5224_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
if (lean_obj_tag(v_a_5202_) == 1)
{
lean_object* v_val_5206_; lean_object* v___x_5207_; 
lean_del_object(v___x_5204_);
v_val_5206_ = lean_ctor_get(v_a_5202_, 0);
lean_inc(v_val_5206_);
lean_dec_ref_known(v_a_5202_, 1);
v___x_5207_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5206_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v_orderedAddInst_x3f_5209_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v_orderedAddInst_x3f_5209_ = lean_ctor_get(v_a_5208_, 9);
lean_inc(v_orderedAddInst_x3f_5209_);
lean_dec(v_a_5208_);
if (lean_obj_tag(v_orderedAddInst_x3f_5209_) == 0)
{
lean_object* v___x_5210_; 
v___x_5210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5145_, v_b_5146_, v_val_5206_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_val_5206_);
return v___x_5210_;
}
else
{
lean_object* v___x_5211_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5209_, 1);
v___x_5211_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5145_, v_b_5146_, v_val_5206_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_val_5206_);
return v___x_5211_;
}
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
lean_dec(v_val_5206_);
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5212_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5207_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5207_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
lean_dec(v_a_5202_);
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v___x_5220_ = lean_box(0);
if (v_isShared_5205_ == 0)
{
lean_ctor_set(v___x_5204_, 0, v___x_5220_);
v___x_5222_ = v___x_5204_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5220_);
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
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5225_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5201_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5201_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v_a_5233_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5161_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5161_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
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
lean_object* v___x_5241_; lean_object* v___x_5242_; 
lean_dec_ref(v_b_5146_);
lean_dec_ref(v_a_5145_);
v___x_5241_ = lean_box(0);
v___x_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
return v___x_5242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5243_, lean_object* v_b_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5243_, v_b_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5252_);
lean_dec_ref(v_a_5251_);
lean_dec(v_a_5250_);
lean_dec_ref(v_a_5249_);
lean_dec(v_a_5248_);
lean_dec_ref(v_a_5247_);
lean_dec(v_a_5246_);
lean_dec(v_a_5245_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5257_, lean_object* v_b_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
uint8_t v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5271_ = 0;
v___x_5272_ = lean_unsigned_to_nat(0u);
v___x_5273_ = lean_box(v___x_5271_);
lean_inc_ref(v_a_5257_);
v___x_5274_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5274_, 0, v_a_5257_);
lean_closure_set(v___x_5274_, 1, v___x_5273_);
lean_closure_set(v___x_5274_, 2, v___x_5272_);
v___x_5275_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5274_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5275_) == 0)
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5377_; 
v_a_5276_ = lean_ctor_get(v___x_5275_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5278_ = v___x_5275_;
v_isShared_5279_ = v_isSharedCheck_5377_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___x_5275_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5377_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
if (lean_obj_tag(v_a_5276_) == 1)
{
lean_object* v_val_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
lean_del_object(v___x_5278_);
v_val_5280_ = lean_ctor_get(v_a_5276_, 0);
lean_inc(v_val_5280_);
lean_dec_ref_known(v_a_5276_, 1);
v___x_5281_ = lean_box(v___x_5271_);
lean_inc_ref(v_b_5258_);
v___x_5282_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5282_, 0, v_b_5258_);
lean_closure_set(v___x_5282_, 1, v___x_5281_);
lean_closure_set(v___x_5282_, 2, v___x_5272_);
v___x_5283_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5282_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5364_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5286_ = v___x_5283_;
v_isShared_5287_ = v_isSharedCheck_5364_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5364_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
if (lean_obj_tag(v_a_5284_) == 1)
{
lean_object* v_val_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_del_object(v___x_5286_);
v_val_5288_ = lean_ctor_get(v_a_5284_, 0);
lean_inc_n(v_val_5288_, 2);
lean_dec_ref_known(v_a_5284_, 1);
lean_inc(v_val_5280_);
v___x_5289_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5289_, 0, v_val_5280_);
lean_ctor_set(v___x_5289_, 1, v_val_5288_);
v___x_5290_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5289_);
lean_inc_ref(v_b_5258_);
lean_inc_ref(v_a_5257_);
v___x_5291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5291_, 0, v_a_5257_);
lean_ctor_set(v___x_5291_, 1, v_b_5258_);
lean_ctor_set(v___x_5291_, 2, v_val_5280_);
lean_ctor_set(v___x_5291_, 3, v_val_5288_);
v___x_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5290_);
lean_ctor_set(v___x_5292_, 1, v___x_5291_);
v___x_5293_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5292_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v___x_5295_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
lean_inc(v_a_5294_);
lean_dec_ref_known(v___x_5293_, 1);
v___x_5295_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5257_, v_a_5260_);
lean_dec_ref(v_a_5257_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5297_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5295_, 1);
v___x_5297_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5258_, v_a_5260_);
lean_dec_ref(v_b_5258_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; lean_object* v_p_5299_; lean_object* v___y_5301_; uint8_t v___x_5335_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5298_);
lean_dec_ref_known(v___x_5297_, 1);
v_p_5299_ = lean_ctor_get(v_a_5294_, 0);
v___x_5335_ = lean_nat_dec_le(v_a_5296_, v_a_5298_);
if (v___x_5335_ == 0)
{
lean_dec(v_a_5298_);
v___y_5301_ = v_a_5296_;
goto v___jp_5300_;
}
else
{
lean_dec(v_a_5296_);
v___y_5301_ = v_a_5298_;
goto v___jp_5300_;
}
v___jp_5300_:
{
lean_object* v___x_5302_; 
lean_inc(v___y_5301_);
lean_inc_ref(v_p_5299_);
v___x_5302_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5299_, v___y_5301_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5304_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref_known(v___x_5302_, 1);
v___x_5304_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5303_, v___x_5271_, v___y_5301_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5318_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5307_ = v___x_5304_;
v_isShared_5308_ = v_isSharedCheck_5318_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5304_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5318_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
if (lean_obj_tag(v_a_5305_) == 1)
{
lean_object* v_val_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
lean_del_object(v___x_5307_);
v_val_5309_ = lean_ctor_get(v_a_5305_, 0);
lean_inc_n(v_val_5309_, 2);
lean_dec_ref_known(v_a_5305_, 1);
v___x_5310_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5309_);
v___x_5311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5311_, 0, v_a_5294_);
lean_ctor_set(v___x_5311_, 1, v_val_5309_);
v___x_5312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5310_);
lean_ctor_set(v___x_5312_, 1, v___x_5311_);
v___x_5313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5312_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
return v___x_5313_;
}
else
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
lean_dec(v_a_5305_);
lean_dec(v_a_5294_);
v___x_5314_ = lean_box(0);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5314_);
v___x_5316_ = v___x_5307_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
lean_dec(v_a_5294_);
v_a_5319_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5304_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5304_);
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
lean_dec(v___y_5301_);
lean_dec(v_a_5294_);
v_a_5327_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5302_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5302_);
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
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
lean_dec(v_a_5296_);
lean_dec(v_a_5294_);
v_a_5336_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5297_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5297_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec(v_a_5294_);
lean_dec_ref(v_b_5258_);
v_a_5344_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5295_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5295_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec_ref(v_b_5258_);
lean_dec_ref(v_a_5257_);
v_a_5352_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5293_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5293_);
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
lean_object* v___x_5360_; lean_object* v___x_5362_; 
lean_dec(v_a_5284_);
lean_dec(v_val_5280_);
lean_dec_ref(v_b_5258_);
lean_dec_ref(v_a_5257_);
v___x_5360_ = lean_box(0);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5360_);
v___x_5362_ = v___x_5286_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
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
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_val_5280_);
lean_dec_ref(v_b_5258_);
lean_dec_ref(v_a_5257_);
v_a_5365_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5283_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5283_);
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
lean_object* v___x_5373_; lean_object* v___x_5375_; 
lean_dec(v_a_5276_);
lean_dec_ref(v_b_5258_);
lean_dec_ref(v_a_5257_);
v___x_5373_ = lean_box(0);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 0, v___x_5373_);
v___x_5375_ = v___x_5278_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5373_);
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
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec_ref(v_b_5258_);
lean_dec_ref(v_a_5257_);
v_a_5378_ = lean_ctor_get(v___x_5275_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5275_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5275_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5386_, lean_object* v_b_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5386_, v_b_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_);
lean_dec(v_a_5398_);
lean_dec_ref(v_a_5397_);
lean_dec(v_a_5396_);
lean_dec_ref(v_a_5395_);
lean_dec(v_a_5394_);
lean_dec_ref(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec(v_a_5388_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5401_, lean_object* v_b_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5401_, v_a_5404_);
if (lean_obj_tag(v___x_5415_) == 0)
{
lean_object* v_a_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; 
v_a_5416_ = lean_ctor_get(v___x_5415_, 0);
lean_inc(v_a_5416_);
lean_dec_ref_known(v___x_5415_, 1);
v___x_5417_ = 0;
lean_inc_ref(v_a_5401_);
v___x_5418_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5401_, v___x_5417_, v_a_5416_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5462_; 
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5421_ = v___x_5418_;
v_isShared_5422_ = v_isSharedCheck_5462_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5418_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5462_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
if (lean_obj_tag(v_a_5419_) == 1)
{
lean_object* v_val_5423_; lean_object* v___x_5424_; 
lean_del_object(v___x_5421_);
v_val_5423_ = lean_ctor_get(v_a_5419_, 0);
lean_inc(v_val_5423_);
lean_dec_ref_known(v_a_5419_, 1);
v___x_5424_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5402_, v_a_5404_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5426_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
lean_inc(v_a_5425_);
lean_dec_ref_known(v___x_5424_, 1);
lean_inc_ref(v_b_5402_);
v___x_5426_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5402_, v___x_5417_, v_a_5425_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5441_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5429_ = v___x_5426_;
v_isShared_5430_ = v_isSharedCheck_5441_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5426_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5441_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
if (lean_obj_tag(v_a_5427_) == 1)
{
lean_object* v_val_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
lean_del_object(v___x_5429_);
v_val_5431_ = lean_ctor_get(v_a_5427_, 0);
lean_inc_n(v_val_5431_, 2);
lean_dec_ref_known(v_a_5427_, 1);
lean_inc(v_val_5423_);
v___x_5432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5432_, 0, v_val_5423_);
lean_ctor_set(v___x_5432_, 1, v_val_5431_);
v___x_5433_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5432_);
v___x_5434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5434_, 0, v_a_5401_);
lean_ctor_set(v___x_5434_, 1, v_b_5402_);
lean_ctor_set(v___x_5434_, 2, v_val_5423_);
lean_ctor_set(v___x_5434_, 3, v_val_5431_);
v___x_5435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5435_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
return v___x_5436_;
}
else
{
lean_object* v___x_5437_; lean_object* v___x_5439_; 
lean_dec(v_a_5427_);
lean_dec(v_val_5423_);
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v___x_5437_ = lean_box(0);
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 0, v___x_5437_);
v___x_5439_ = v___x_5429_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
lean_dec(v_val_5423_);
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v_a_5442_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5426_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5426_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_dec(v_val_5423_);
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v_a_5450_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5424_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5424_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
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
lean_object* v___x_5458_; lean_object* v___x_5460_; 
lean_dec(v_a_5419_);
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v___x_5458_ = lean_box(0);
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 0, v___x_5458_);
v___x_5460_ = v___x_5421_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5458_);
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
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v_a_5463_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5418_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5418_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
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
lean_dec_ref(v_b_5402_);
lean_dec_ref(v_a_5401_);
v_a_5471_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5415_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5415_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5479_, lean_object* v_b_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_){
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5479_, v_b_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_);
lean_dec(v_a_5491_);
lean_dec_ref(v_a_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v_a_5488_);
lean_dec(v_a_5487_);
lean_dec_ref(v_a_5486_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec(v_a_5482_);
lean_dec(v_a_5481_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5494_, lean_object* v_b_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_){
_start:
{
lean_object* v___x_5508_; 
v___x_5508_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
if (lean_obj_tag(v___x_5508_) == 0)
{
lean_object* v_a_5509_; lean_object* v_addRightCancelInst_x3f_5510_; 
v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
lean_inc(v_a_5509_);
lean_dec_ref_known(v___x_5508_, 1);
v_addRightCancelInst_x3f_5510_ = lean_ctor_get(v_a_5509_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5510_) == 0)
{
lean_object* v___x_5511_; 
lean_dec(v_a_5509_);
v___x_5511_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5494_, v_b_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
return v___x_5511_;
}
else
{
lean_object* v_id_5512_; lean_object* v_structId_5513_; lean_object* v___x_5514_; 
v_id_5512_ = lean_ctor_get(v_a_5509_, 0);
lean_inc(v_id_5512_);
v_structId_5513_ = lean_ctor_get(v_a_5509_, 1);
lean_inc(v_structId_5513_);
lean_dec(v_a_5509_);
lean_inc_ref(v_a_5494_);
v___x_5514_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5494_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v_fst_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5604_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref_known(v___x_5514_, 1);
v_fst_5516_ = lean_ctor_get(v_a_5515_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_a_5515_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_a_5515_, 1);
lean_dec(v_unused_5605_);
v___x_5518_ = v_a_5515_;
v_isShared_5519_ = v_isSharedCheck_5604_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_fst_5516_);
lean_dec(v_a_5515_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5604_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5520_; 
lean_inc_ref(v_b_5495_);
v___x_5520_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v_fst_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5594_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v___x_5520_, 1);
v_fst_5522_ = lean_ctor_get(v_a_5521_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_a_5521_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; 
v_unused_5595_ = lean_ctor_get(v_a_5521_, 1);
lean_dec(v_unused_5595_);
v___x_5524_ = v_a_5521_;
v_isShared_5525_ = v_isSharedCheck_5594_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_fst_5522_);
lean_dec(v_a_5521_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5594_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5526_; 
v___x_5526_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5494_, v_a_5497_);
if (lean_obj_tag(v___x_5526_) == 0)
{
lean_object* v_a_5527_; uint8_t v___x_5528_; lean_object* v___x_5529_; 
v_a_5527_ = lean_ctor_get(v___x_5526_, 0);
lean_inc(v_a_5527_);
lean_dec_ref_known(v___x_5526_, 1);
v___x_5528_ = 0;
v___x_5529_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5516_, v___x_5528_, v_a_5527_, v_structId_5513_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5577_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5577_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5577_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
if (lean_obj_tag(v_a_5530_) == 1)
{
lean_object* v_val_5534_; lean_object* v___x_5535_; 
lean_del_object(v___x_5532_);
v_val_5534_ = lean_ctor_get(v_a_5530_, 0);
lean_inc(v_val_5534_);
lean_dec_ref_known(v_a_5530_, 1);
v___x_5535_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5495_, v_a_5497_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5537_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
lean_dec_ref_known(v___x_5535_, 1);
v___x_5537_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5522_, v___x_5528_, v_a_5536_, v_structId_5513_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5556_; 
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5540_ = v___x_5537_;
v_isShared_5541_ = v_isSharedCheck_5556_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5537_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5556_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
if (lean_obj_tag(v_a_5538_) == 1)
{
lean_object* v_val_5542_; lean_object* v___x_5544_; 
lean_del_object(v___x_5540_);
v_val_5542_ = lean_ctor_get(v_a_5538_, 0);
lean_inc_n(v_val_5542_, 2);
lean_dec_ref_known(v_a_5538_, 1);
lean_inc(v_val_5534_);
if (v_isShared_5525_ == 0)
{
lean_ctor_set_tag(v___x_5524_, 3);
lean_ctor_set(v___x_5524_, 1, v_val_5542_);
lean_ctor_set(v___x_5524_, 0, v_val_5534_);
v___x_5544_ = v___x_5524_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_val_5534_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_val_5542_);
v___x_5544_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5548_; 
v___x_5545_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5544_);
v___x_5546_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5546_, 0, v_a_5494_);
lean_ctor_set(v___x_5546_, 1, v_b_5495_);
lean_ctor_set(v___x_5546_, 2, v_id_5512_);
lean_ctor_set(v___x_5546_, 3, v_val_5534_);
lean_ctor_set(v___x_5546_, 4, v_val_5542_);
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5546_);
lean_ctor_set(v___x_5518_, 0, v___x_5545_);
v___x_5548_ = v___x_5518_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5545_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; 
v___x_5549_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5548_, v_structId_5513_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
lean_dec(v_structId_5513_);
return v___x_5549_;
}
}
}
else
{
lean_object* v___x_5552_; lean_object* v___x_5554_; 
lean_dec(v_a_5538_);
lean_dec(v_val_5534_);
lean_del_object(v___x_5524_);
lean_del_object(v___x_5518_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v___x_5552_ = lean_box(0);
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 0, v___x_5552_);
v___x_5554_ = v___x_5540_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_dec(v_val_5534_);
lean_del_object(v___x_5524_);
lean_del_object(v___x_5518_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5557_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5559_ = v___x_5537_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_a_5557_);
lean_dec(v___x_5537_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
else
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5572_; 
lean_dec(v_val_5534_);
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_del_object(v___x_5518_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5565_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5567_ = v___x_5535_;
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5535_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5570_; 
if (v_isShared_5568_ == 0)
{
v___x_5570_ = v___x_5567_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5565_);
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
lean_object* v___x_5573_; lean_object* v___x_5575_; 
lean_dec(v_a_5530_);
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_del_object(v___x_5518_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v___x_5573_ = lean_box(0);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5573_);
v___x_5575_ = v___x_5532_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5573_);
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
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_del_object(v___x_5518_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5578_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5529_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5529_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
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
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_del_object(v___x_5518_);
lean_dec(v_fst_5516_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5586_ = lean_ctor_get(v___x_5526_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5526_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5526_);
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
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_del_object(v___x_5518_);
lean_dec(v_fst_5516_);
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5596_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5520_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5520_);
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
lean_dec(v_structId_5513_);
lean_dec(v_id_5512_);
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5606_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5514_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5514_);
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
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec_ref(v_b_5495_);
lean_dec_ref(v_a_5494_);
v_a_5614_ = lean_ctor_get(v___x_5508_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5508_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5508_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5622_, lean_object* v_b_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5622_, v_b_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
lean_dec(v_a_5628_);
lean_dec_ref(v_a_5627_);
lean_dec(v_a_5626_);
lean_dec(v_a_5625_);
lean_dec(v_a_5624_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5637_, lean_object* v_b_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_){
_start:
{
lean_object* v___x_5650_; 
v___x_5650_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5637_, v_b_5638_, v_a_5639_, v_a_5647_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_object* v_a_5651_; 
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
lean_inc(v_a_5651_);
lean_dec_ref_known(v___x_5650_, 1);
if (lean_obj_tag(v_a_5651_) == 1)
{
lean_object* v_val_5652_; lean_object* v___x_5653_; 
v_val_5652_ = lean_ctor_get(v_a_5651_, 0);
lean_inc(v_val_5652_);
lean_dec_ref_known(v_a_5651_, 1);
v___x_5653_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5652_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; uint8_t v___x_5655_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_a_5654_);
lean_dec_ref_known(v___x_5653_, 1);
v___x_5655_ = lean_unbox(v_a_5654_);
lean_dec(v_a_5654_);
if (v___x_5655_ == 0)
{
lean_object* v___x_5656_; 
v___x_5656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5637_, v_b_5638_, v_val_5652_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_);
lean_dec(v_val_5652_);
return v___x_5656_;
}
else
{
lean_object* v___x_5657_; 
v___x_5657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5637_, v_b_5638_, v_val_5652_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_);
lean_dec(v_val_5652_);
return v___x_5657_;
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v_val_5652_);
lean_dec_ref(v_b_5638_);
lean_dec_ref(v_a_5637_);
v_a_5658_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5653_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5653_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
else
{
lean_object* v___x_5666_; 
lean_dec(v_a_5651_);
v___x_5666_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5637_, v_b_5638_, v_a_5639_, v_a_5647_);
if (lean_obj_tag(v___x_5666_) == 0)
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5677_; 
v_a_5667_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5669_ = v___x_5666_;
v_isShared_5670_ = v_isSharedCheck_5677_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5666_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5677_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
if (lean_obj_tag(v_a_5667_) == 1)
{
lean_object* v_val_5671_; lean_object* v___x_5672_; 
lean_del_object(v___x_5669_);
v_val_5671_ = lean_ctor_get(v_a_5667_, 0);
lean_inc(v_val_5671_);
lean_dec_ref_known(v_a_5667_, 1);
v___x_5672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5637_, v_b_5638_, v_val_5671_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_);
lean_dec(v_val_5671_);
return v___x_5672_;
}
else
{
lean_object* v___x_5673_; lean_object* v___x_5675_; 
lean_dec(v_a_5667_);
lean_dec_ref(v_b_5638_);
lean_dec_ref(v_a_5637_);
v___x_5673_ = lean_box(0);
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 0, v___x_5673_);
v___x_5675_ = v___x_5669_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5673_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
}
else
{
lean_object* v_a_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5685_; 
lean_dec_ref(v_b_5638_);
lean_dec_ref(v_a_5637_);
v_a_5678_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5685_ == 0)
{
v___x_5680_ = v___x_5666_;
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_a_5678_);
lean_dec(v___x_5666_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v___x_5683_; 
if (v_isShared_5681_ == 0)
{
v___x_5683_ = v___x_5680_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5684_; 
v_reuseFailAlloc_5684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
v___x_5683_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
return v___x_5683_;
}
}
}
}
}
else
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5693_; 
lean_dec_ref(v_b_5638_);
lean_dec_ref(v_a_5637_);
v_a_5686_ = lean_ctor_get(v___x_5650_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5688_ = v___x_5650_;
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5650_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5689_ == 0)
{
v___x_5691_ = v___x_5688_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5686_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5694_, lean_object* v_b_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5694_, v_b_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_a_5701_);
lean_dec_ref(v_a_5700_);
lean_dec(v_a_5699_);
lean_dec_ref(v_a_5698_);
lean_dec(v_a_5697_);
lean_dec(v_a_5696_);
return v_res_5707_;
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
