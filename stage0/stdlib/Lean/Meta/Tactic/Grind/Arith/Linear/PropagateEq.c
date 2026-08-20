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
v_options_306_ = lean_ctor_get(v___y_298_, 2);
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
v_ref_329_ = lean_ctor_get(v___y_326_, 5);
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
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_538_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_538_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_538_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_538_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
if (lean_obj_tag(v_a_416_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_533_; 
v_val_420_ = lean_ctor_get(v_a_416_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_533_ == 0)
{
v___x_422_ = v_a_416_;
v_isShared_423_ = v_isSharedCheck_533_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v_a_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_533_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_snd_424_; lean_object* v_snd_425_; lean_object* v_options_426_; lean_object* v_fst_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_531_; 
v_snd_424_ = lean_ctor_get(v_val_420_, 1);
lean_inc(v_snd_424_);
v_snd_425_ = lean_ctor_get(v_snd_424_, 1);
lean_inc(v_snd_425_);
v_options_426_ = lean_ctor_get(v_a_412_, 2);
v_fst_427_ = lean_ctor_get(v_val_420_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_val_420_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_val_420_, 1);
lean_dec(v_unused_532_);
v___x_429_ = v_val_420_;
v_isShared_430_ = v_isSharedCheck_531_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_fst_427_);
lean_dec(v_val_420_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_531_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_529_; 
v_fst_431_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_snd_424_, 1);
lean_dec(v_unused_530_);
v___x_433_ = v_snd_424_;
v_isShared_434_ = v_isSharedCheck_529_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_fst_431_);
lean_dec(v_snd_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_529_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_p_435_; lean_object* v_inheritedTraceOptions_436_; uint8_t v_hasTrace_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_p_435_ = lean_ctor_get(v_snd_425_, 0);
v_inheritedTraceOptions_436_ = lean_ctor_get(v_a_412_, 13);
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
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_458_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_436_, v_options_426_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v___x_438_);
lean_dec(v_fst_427_);
lean_dec(v_p_402_);
goto v___jp_443_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_p_402_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_431_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_425_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_442_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = l_Lean_MessageData_ofExpr(v_a_460_);
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Int_repr(v_fst_427_);
lean_dec(v_fst_427_);
v___x_471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
v___x_472_ = l_Lean_MessageData_ofFormat(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_469_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_468_);
v___x_475_ = l_Lean_MessageData_ofExpr(v_a_462_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_468_);
v___x_478_ = l_Lean_MessageData_ofExpr(v_a_464_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_468_);
v___x_481_ = l_Int_repr(v___x_438_);
lean_dec(v___x_438_);
v___x_482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = l_Lean_MessageData_ofFormat(v___x_482_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_480_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_468_);
v___x_486_ = l_Lean_MessageData_ofExpr(v_a_466_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_456_, v___x_487_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref_known(v___x_488_, 1);
goto v___jp_443_;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v___x_442_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
lean_dec(v_a_460_);
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
v_a_497_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_465_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_465_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_462_);
lean_dec(v_a_460_);
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
v_a_505_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_463_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_463_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_a_460_);
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
v_a_513_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_461_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_461_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v___x_442_);
lean_dec(v___x_438_);
lean_del_object(v___x_433_);
lean_dec(v_fst_431_);
lean_del_object(v___x_429_);
lean_dec(v_fst_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_422_);
lean_del_object(v___x_418_);
v_a_521_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_459_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_459_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
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
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_a_416_);
lean_dec(v_p_402_);
v___x_534_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_534_);
v___x_536_ = v___x_418_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_p_402_);
v_a_539_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_415_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_415_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_561_, lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_561_, v_msg_562_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_576_, lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_576_, v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_p_604_; lean_object* v___x_605_; 
v_p_604_ = lean_ctor_get(v_c_591_, 0);
v___x_605_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_604_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_ofNatZero_609_; lean_object* v___x_610_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_ofNatZero_609_ = lean_ctor_get(v_a_608_, 18);
lean_inc_ref(v_ofNatZero_609_);
lean_dec(v_a_608_);
v___x_610_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_606_, v_ofNatZero_609_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_mkNot(v_a_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
return v___x_610_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_606_);
v_a_620_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_607_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v_c_628_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_nat_to_int(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_cls_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_650_ = l_Lean_Name_append(v___x_649_, v_cls_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_651_, lean_object* v_x_652_, lean_object* v_c_u2081_653_, lean_object* v_b_654_, lean_object* v_c_u2082_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v_options_722_; uint8_t v_hasTrace_723_; 
v_options_722_ = lean_ctor_get(v_a_665_, 2);
v_hasTrace_723_ = lean_ctor_get_uint8(v_options_722_, sizeof(void*)*1);
if (v_hasTrace_723_ == 0)
{
v___y_669_ = v_a_656_;
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
goto v___jp_668_;
}
else
{
lean_object* v_inheritedTraceOptions_724_; lean_object* v_cls_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_inheritedTraceOptions_724_ = lean_ctor_get(v_a_665_, 13);
v_cls_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_724_, v_options_722_, v___x_726_);
if (v___x_727_ == 0)
{
v___y_669_ = v_a_656_;
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
goto v___jp_668_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_652_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_653_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_MessageData_ofExpr(v_a_729_);
v___x_735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_MessageData_ofExpr(v_a_731_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_735_);
v___x_740_ = l_Lean_MessageData_ofExpr(v_a_733_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_725_, v___x_741_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_dec_ref_known(v___x_742_, 1);
v___y_669_ = v_a_656_;
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
goto v___jp_668_;
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_a_731_);
lean_dec(v_a_729_);
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v_a_751_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_732_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_732_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_729_);
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v_a_759_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_730_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_730_);
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
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v_a_767_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_728_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_728_);
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
}
v___jp_668_:
{
lean_object* v_p_680_; lean_object* v_p_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_p_680_ = lean_ctor_get(v_c_u2081_653_, 0);
v_p_681_ = lean_ctor_get(v_c_u2082_655_, 0);
v___x_682_ = lean_int_emod(v_b_654_, v_a_651_);
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_684_ = lean_int_dec_eq(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_705_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_705_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_705_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_705_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; 
v___x_690_ = lean_unbox(v_a_686_);
lean_dec(v_a_686_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v___x_691_ = lean_box(0);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_p_680_);
v___x_695_ = l_Lean_Grind_Linarith_Poly_mul(v_p_680_, v_b_654_);
v___x_696_ = lean_int_neg(v_a_651_);
lean_inc(v_p_681_);
v___x_697_ = l_Lean_Grind_Linarith_Poly_mul(v_p_681_, v___x_696_);
v___x_698_ = l_Lean_Grind_Linarith_Poly_combine(v___x_695_, v___x_697_);
v___x_699_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_699_, 0, v___x_696_);
lean_ctor_set(v___x_699_, 1, v_b_654_);
lean_ctor_set(v___x_699_, 2, v_c_u2081_653_);
lean_ctor_set(v___x_699_, 3, v_c_u2082_655_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_701_);
v___x_703_ = v___x_688_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_c_u2082_655_);
lean_dec(v_b_654_);
lean_dec_ref(v_c_u2081_653_);
v_a_706_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_685_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_685_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_714_ = lean_int_neg(v_b_654_);
lean_dec(v_b_654_);
v___x_715_ = lean_int_ediv(v___x_714_, v_a_651_);
lean_dec(v___x_714_);
lean_inc(v_p_680_);
v___x_716_ = l_Lean_Grind_Linarith_Poly_mul(v_p_680_, v___x_715_);
lean_inc(v_p_681_);
v___x_717_ = l_Lean_Grind_Linarith_Poly_combine(v___x_716_, v_p_681_);
v___x_718_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_718_, 0, v___x_715_);
lean_ctor_set(v___x_718_, 1, v_c_u2081_653_);
lean_ctor_set(v___x_718_, 2, v_c_u2082_655_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_775_ = _args[0];
lean_object* v_x_776_ = _args[1];
lean_object* v_c_u2081_777_ = _args[2];
lean_object* v_b_778_ = _args[3];
lean_object* v_c_u2082_779_ = _args[4];
lean_object* v_a_780_ = _args[5];
lean_object* v_a_781_ = _args[6];
lean_object* v_a_782_ = _args[7];
lean_object* v_a_783_ = _args[8];
lean_object* v_a_784_ = _args[9];
lean_object* v_a_785_ = _args[10];
lean_object* v_a_786_ = _args[11];
lean_object* v_a_787_ = _args[12];
lean_object* v_a_788_ = _args[13];
lean_object* v_a_789_ = _args[14];
lean_object* v_a_790_ = _args[15];
lean_object* v_a_791_ = _args[16];
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_775_, v_x_776_, v_c_u2081_777_, v_b_778_, v_c_u2082_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
lean_dec(v_x_776_);
lean_dec(v_a_775_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_793_, lean_object* v_b_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_793_, v_a_795_, v_a_796_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_827_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_827_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_827_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_827_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
if (lean_obj_tag(v_a_799_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_804_; 
lean_del_object(v___x_801_);
v_val_803_ = lean_ctor_get(v_a_799_, 0);
v___x_804_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_794_, v_a_795_, v_a_796_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_822_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_822_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_822_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_822_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
if (lean_obj_tag(v_a_805_) == 1)
{
lean_object* v_val_809_; uint8_t v___x_810_; 
v_val_809_ = lean_ctor_get(v_a_805_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_a_805_, 1);
v___x_810_ = lean_nat_dec_eq(v_val_803_, v_val_809_);
lean_dec(v_val_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec_ref_known(v_a_799_, 1);
v___x_811_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_816_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v_a_799_);
v___x_816_ = v___x_807_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_799_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_820_; 
lean_dec(v_a_805_);
lean_dec_ref_known(v_a_799_, 1);
v___x_818_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_818_);
v___x_820_ = v___x_807_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_799_, 1);
return v___x_804_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_825_; 
lean_dec(v_a_799_);
v___x_823_ = lean_box(0);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_823_);
v___x_825_ = v___x_801_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_828_, lean_object* v_b_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_828_, v_b_829_, v_a_830_, v_a_831_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_b_829_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_834_, v_b_835_, v_a_836_, v_a_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_848_, lean_object* v_b_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_848_, v_b_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_b_849_);
lean_dec_ref(v_a_848_);
return v_res_861_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_863_ = lean_int_neg(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_864_, lean_object* v_b_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_878_ = 0;
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_box(v___x_878_);
lean_inc_ref(v_a_864_);
v___x_881_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_881_, 0, v_a_864_);
lean_closure_set(v___x_881_, 1, v___x_880_);
lean_closure_set(v___x_881_, 2, v___x_879_);
v___x_882_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_881_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_1034_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_1034_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_1034_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_a_883_) == 1)
{
lean_object* v_val_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_del_object(v___x_885_);
v_val_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v_a_883_, 1);
v___x_888_ = lean_box(v___x_878_);
lean_inc_ref(v_b_865_);
v___x_889_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_889_, 0, v_b_865_);
lean_closure_set(v___x_889_, 1, v___x_888_);
lean_closure_set(v___x_889_, 2, v___x_879_);
v___x_890_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_889_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_1021_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_1021_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_1021_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
if (lean_obj_tag(v_a_891_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_896_; 
lean_del_object(v___x_893_);
v_val_895_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_a_891_, 1);
v___x_896_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_864_, v_a_867_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_865_, v_a_867_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___y_901_; uint8_t v___x_1000_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_1000_ = lean_nat_dec_le(v_a_897_, v_a_899_);
if (v___x_1000_ == 0)
{
lean_dec(v_a_899_);
v___y_901_ = v_a_897_;
goto v___jp_900_;
}
else
{
lean_dec(v_a_897_);
v___y_901_ = v_a_899_;
goto v___jp_900_;
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_val_895_);
lean_inc(v_val_887_);
v___x_902_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_902_, 0, v_val_887_);
lean_ctor_set(v___x_902_, 1, v_val_895_);
v___x_903_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_904_, 0, v_a_864_);
lean_ctor_set(v___x_904_, 1, v_b_865_);
lean_ctor_set(v___x_904_, 2, v_val_887_);
lean_ctor_set(v___x_904_, 3, v_val_895_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_905_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v_p_908_; lean_object* v___x_909_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v_p_908_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v___y_901_);
lean_inc_ref(v_p_908_);
v___x_909_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_908_, v___y_901_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
lean_inc(v___y_901_);
v___x_911_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_910_, v___x_878_, v___y_901_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_975_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_975_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_975_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_975_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
if (lean_obj_tag(v_a_912_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_val_916_ = lean_ctor_get(v_a_912_, 0);
lean_inc_n(v_val_916_, 2);
lean_dec_ref_known(v_a_912_, 1);
v___x_917_ = l_Lean_Grind_Linarith_Expr_norm(v_val_916_);
v___x_918_ = lean_box(0);
v___x_919_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_914_);
lean_inc(v_a_907_);
v___x_920_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_907_);
lean_ctor_set(v___x_920_, 1, v_val_916_);
lean_inc(v___x_917_);
v___x_921_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_921_, 0, v___x_917_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*2, v___x_878_);
v___x_922_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_921_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_965_; 
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_966_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_965_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_965_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_908_);
v___x_927_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_926_, v_p_908_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 1);
lean_ctor_set(v___x_924_, 0, v_a_907_);
v___x_929_ = v___x_924_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_907_);
v___x_929_ = v_reuseFailAlloc_964_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc_ref(v___x_927_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_inc(v___y_901_);
v___x_931_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_927_, v___y_901_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_932_, v___x_878_, v___y_901_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_947_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_947_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_a_934_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_del_object(v___x_936_);
v_val_938_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v_a_934_, 1);
v___x_939_ = l_Lean_Grind_Linarith_Poly_mul(v___x_917_, v___x_926_);
v___x_940_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_930_);
lean_ctor_set(v___x_940_, 1, v_val_938_);
v___x_941_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*2, v___x_878_);
v___x_942_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_941_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_945_; 
lean_dec(v_a_934_);
lean_dec_ref_known(v___x_930_, 2);
lean_dec(v___x_917_);
v___x_943_ = lean_box(0);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_943_);
v___x_945_ = v___x_936_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref_known(v___x_930_, 2);
lean_dec(v___x_917_);
v_a_948_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_933_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_933_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref_known(v___x_930_, 2);
lean_dec(v___x_917_);
lean_dec(v___y_901_);
v_a_956_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_931_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_931_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
else
{
lean_dec(v___x_917_);
lean_dec(v_a_907_);
lean_dec(v___y_901_);
return v___x_922_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec(v___x_917_);
lean_dec(v_val_916_);
lean_dec(v_a_907_);
lean_dec(v___y_901_);
v___x_967_ = lean_box(0);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_967_);
v___x_969_ = v___x_914_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v_a_912_);
lean_dec(v_a_907_);
lean_dec(v___y_901_);
v___x_971_ = lean_box(0);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_971_);
v___x_973_ = v___x_914_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_907_);
lean_dec(v___y_901_);
v_a_976_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_911_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_911_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_907_);
lean_dec(v___y_901_);
v_a_984_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_909_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_909_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___y_901_);
v_a_992_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_906_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_906_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_897_);
lean_dec(v_val_895_);
lean_dec(v_val_887_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v_a_1001_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_898_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_898_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_val_895_);
lean_dec(v_val_887_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v_a_1009_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_896_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_896_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v_a_891_);
lean_dec(v_val_887_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v___x_1017_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_1017_);
v___x_1019_ = v___x_893_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
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
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_val_887_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v_a_1022_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_890_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_890_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v_a_883_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v___x_1030_ = lean_box(0);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_1030_);
v___x_1032_ = v___x_885_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
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
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_b_865_);
lean_dec_ref(v_a_864_);
v_a_1035_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_882_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_882_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1043_, v_b_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1058_, lean_object* v_b_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1058_, v_a_1061_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = 0;
lean_inc_ref(v_a_1058_);
v___x_1075_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1058_, v___x_1074_, v_a_1073_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1130_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1130_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1130_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_a_1076_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; 
lean_del_object(v___x_1078_);
v_val_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1081_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1059_, v_a_1061_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
lean_inc_ref(v_b_1059_);
v___x_1083_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1059_, v___x_1074_, v_a_1082_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1109_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1109_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1109_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
if (lean_obj_tag(v_a_1084_) == 1)
{
lean_object* v_val_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_val_1088_ = lean_ctor_get(v_a_1084_, 0);
lean_inc_n(v_val_1088_, 2);
lean_dec_ref_known(v_a_1084_, 1);
lean_inc(v_val_1080_);
v___x_1089_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_val_1080_);
lean_ctor_set(v___x_1089_, 1, v_val_1088_);
v___x_1090_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1089_);
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_del_object(v___x_1086_);
lean_inc(v_val_1088_);
lean_inc(v_val_1080_);
lean_inc_ref(v_b_1059_);
lean_inc_ref(v_a_1058_);
v___x_1093_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1093_, 0, v_a_1058_);
lean_ctor_set(v___x_1093_, 1, v_b_1059_);
lean_ctor_set(v___x_1093_, 2, v_val_1080_);
lean_ctor_set(v___x_1093_, 3, v_val_1088_);
lean_inc(v___x_1090_);
v___x_1094_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1094_, 0, v___x_1090_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*2, v___x_1074_);
v___x_1095_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1094_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref_known(v___x_1095_, 1);
v___x_1096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1097_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1090_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1098_, 0, v_b_1059_);
lean_ctor_set(v___x_1098_, 1, v_a_1058_);
lean_ctor_set(v___x_1098_, 2, v_val_1088_);
lean_ctor_set(v___x_1098_, 3, v_val_1080_);
v___x_1099_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*2, v___x_1074_);
v___x_1100_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1099_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1100_;
}
else
{
lean_dec(v___x_1090_);
lean_dec(v_val_1088_);
lean_dec(v_val_1080_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
return v___x_1095_;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_dec(v___x_1090_);
lean_dec(v_val_1088_);
lean_dec(v_val_1080_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v___x_1101_ = lean_box(0);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1101_);
v___x_1103_ = v___x_1086_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_dec(v_a_1084_);
lean_dec(v_val_1080_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v___x_1105_ = lean_box(0);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1105_);
v___x_1107_ = v___x_1086_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_val_1080_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v_a_1110_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1083_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1083_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_val_1080_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v_a_1118_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1081_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1081_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_dec(v_a_1076_);
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v___x_1126_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1126_);
v___x_1128_ = v___x_1078_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v_a_1131_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1075_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1075_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_b_1059_);
lean_dec_ref(v_a_1058_);
v_a_1139_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1072_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1072_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
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
v___x_1162_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_nat_to_int(v_a_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1200_ = lean_unsigned_to_nat(42u);
v___x_1201_ = lean_unsigned_to_nat(87u);
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v_c_1221_; lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_c_1229_; lean_object* v_p_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___x_1266_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1266_ = lean_unbox(v_a_1227_);
lean_dec(v_a_1227_);
if (v___x_1266_ == 0)
{
lean_object* v_p_1267_; 
v_p_1267_ = lean_ctor_get(v_c_1205_, 0);
lean_inc(v_p_1267_);
v_c_1229_ = v_c_1205_;
v_p_1230_ = v_p_1267_;
v___y_1231_ = v_a_1206_;
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
goto v___jp_1228_;
}
else
{
lean_object* v_p_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_p_1268_ = lean_ctor_get(v_c_1205_, 0);
v___x_1269_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1268_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_dec_eq(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc(v___x_1269_);
v___x_1272_ = lean_nat_to_int(v___x_1269_);
lean_inc(v_p_1268_);
v___x_1273_ = l_Lean_Grind_Linarith_Poly_div(v_p_1268_, v___x_1272_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1269_);
lean_ctor_set(v___x_1274_, 1, v_c_1205_);
lean_inc(v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v_c_1229_ = v___x_1275_;
v_p_1230_ = v___x_1273_;
v___y_1231_ = v_a_1206_;
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
goto v___jp_1228_;
}
else
{
lean_inc(v_p_1268_);
lean_dec(v___x_1269_);
v_c_1229_ = v_c_1205_;
v_p_1230_ = v_p_1268_;
v___y_1231_ = v_a_1206_;
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
goto v___jp_1228_;
}
}
v___jp_1228_:
{
lean_object* v___x_1242_; 
lean_inc(v_p_1230_);
v___x_1242_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1230_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1263_; 
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1262_; 
v_fst_1247_ = lean_ctor_get(v_val_1243_, 0);
v_snd_1248_ = lean_ctor_get(v_val_1243_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_val_1243_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1250_ = v_val_1243_;
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v_val_1243_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1253_ = lean_int_dec_lt(v_fst_1247_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_del_object(v___x_1250_);
lean_del_object(v___x_1245_);
lean_dec(v_p_1230_);
v___y_1219_ = v_fst_1247_;
v___y_1220_ = v_snd_1248_;
v_c_1221_ = v_c_1229_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1255_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1230_, v___x_1254_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 3);
lean_ctor_set(v___x_1245_, 0, v_c_1229_);
v___x_1257_ = v___x_1245_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_c_1229_);
v___x_1257_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1257_);
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1259_ = v___x_1250_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v___y_1219_ = v_fst_1247_;
v___y_1220_ = v_snd_1248_;
v_c_1221_ = v___x_1259_;
goto v___jp_1218_;
}
}
}
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v___x_1242_);
lean_dec(v_p_1230_);
lean_dec_ref(v_c_1229_);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1265_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1264_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_c_1205_);
v_a_1276_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1226_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1226_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_nat_abs(v___y_1219_);
lean_dec(v___y_1219_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1220_);
lean_ctor_set(v___x_1223_, 1, v_c_1221_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec(v_a_1285_);
return v_res_1297_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = l_Lean_maxRecDepthErrorMessage;
v___x_1304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1306_ = l_Lean_MessageData_ofFormat(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1308_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1309_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_ref_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1319_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_ref_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1333_, v_ref_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v_p_1379_; lean_object* v_fileName_1380_; lean_object* v_fileMap_1381_; lean_object* v_options_1382_; lean_object* v_currRecDepth_1383_; lean_object* v_maxRecDepth_1384_; lean_object* v_ref_1385_; lean_object* v_currNamespace_1386_; lean_object* v_openDecls_1387_; lean_object* v_initHeartbeats_1388_; lean_object* v_maxHeartbeats_1389_; lean_object* v_quotContext_1390_; lean_object* v_currMacroScope_1391_; uint8_t v_diag_1392_; lean_object* v_cancelTk_x3f_1393_; uint8_t v_suppressElabErrors_1394_; lean_object* v_inheritedTraceOptions_1395_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_p_1379_ = lean_ctor_get(v_c_1348_, 0);
v_fileName_1380_ = lean_ctor_get(v_a_1358_, 0);
lean_inc_ref(v_fileName_1380_);
v_fileMap_1381_ = lean_ctor_get(v_a_1358_, 1);
lean_inc_ref(v_fileMap_1381_);
v_options_1382_ = lean_ctor_get(v_a_1358_, 2);
lean_inc_ref(v_options_1382_);
v_currRecDepth_1383_ = lean_ctor_get(v_a_1358_, 3);
lean_inc(v_currRecDepth_1383_);
v_maxRecDepth_1384_ = lean_ctor_get(v_a_1358_, 4);
lean_inc(v_maxRecDepth_1384_);
v_ref_1385_ = lean_ctor_get(v_a_1358_, 5);
lean_inc(v_ref_1385_);
v_currNamespace_1386_ = lean_ctor_get(v_a_1358_, 6);
lean_inc(v_currNamespace_1386_);
v_openDecls_1387_ = lean_ctor_get(v_a_1358_, 7);
lean_inc(v_openDecls_1387_);
v_initHeartbeats_1388_ = lean_ctor_get(v_a_1358_, 8);
lean_inc(v_initHeartbeats_1388_);
v_maxHeartbeats_1389_ = lean_ctor_get(v_a_1358_, 9);
lean_inc(v_maxHeartbeats_1389_);
v_quotContext_1390_ = lean_ctor_get(v_a_1358_, 10);
lean_inc(v_quotContext_1390_);
v_currMacroScope_1391_ = lean_ctor_get(v_a_1358_, 11);
lean_inc(v_currMacroScope_1391_);
v_diag_1392_ = lean_ctor_get_uint8(v_a_1358_, sizeof(void*)*14);
v_cancelTk_x3f_1393_ = lean_ctor_get(v_a_1358_, 12);
lean_inc(v_cancelTk_x3f_1393_);
v_suppressElabErrors_1394_ = lean_ctor_get_uint8(v_a_1358_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1395_ = lean_ctor_get(v_a_1358_, 13);
lean_inc_ref(v_inheritedTraceOptions_1395_);
lean_dec_ref(v_a_1358_);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_nat_dec_eq(v_maxRecDepth_1384_, v___x_1489_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_eq(v_currRecDepth_1383_, v_maxRecDepth_1384_);
if (v___x_1491_ == 0)
{
goto v___jp_1396_;
}
else
{
lean_object* v___x_1492_; 
lean_dec_ref(v_inheritedTraceOptions_1395_);
lean_dec(v_cancelTk_x3f_1393_);
lean_dec(v_currMacroScope_1391_);
lean_dec(v_quotContext_1390_);
lean_dec(v_maxHeartbeats_1389_);
lean_dec(v_initHeartbeats_1388_);
lean_dec(v_openDecls_1387_);
lean_dec(v_currNamespace_1386_);
lean_dec(v_maxRecDepth_1384_);
lean_dec(v_currRecDepth_1383_);
lean_dec_ref(v_options_1382_);
lean_dec_ref(v_fileMap_1381_);
lean_dec_ref(v_fileName_1380_);
lean_dec_ref(v_c_1348_);
v___x_1492_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1385_);
return v___x_1492_;
}
}
else
{
goto v___jp_1396_;
}
v___jp_1361_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1364_);
lean_ctor_set(v___x_1376_, 1, v___y_1362_);
lean_ctor_set(v___x_1376_, 2, v_c_1348_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___y_1363_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v_c_1348_ = v___x_1377_;
v_a_1349_ = v___y_1365_;
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
goto _start;
}
v___jp_1396_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_add(v_currRecDepth_1383_, v___x_1397_);
lean_dec(v_currRecDepth_1383_);
lean_inc_ref(v_inheritedTraceOptions_1395_);
lean_inc_ref(v_options_1382_);
v___x_1399_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1399_, 0, v_fileName_1380_);
lean_ctor_set(v___x_1399_, 1, v_fileMap_1381_);
lean_ctor_set(v___x_1399_, 2, v_options_1382_);
lean_ctor_set(v___x_1399_, 3, v___x_1398_);
lean_ctor_set(v___x_1399_, 4, v_maxRecDepth_1384_);
lean_ctor_set(v___x_1399_, 5, v_ref_1385_);
lean_ctor_set(v___x_1399_, 6, v_currNamespace_1386_);
lean_ctor_set(v___x_1399_, 7, v_openDecls_1387_);
lean_ctor_set(v___x_1399_, 8, v_initHeartbeats_1388_);
lean_ctor_set(v___x_1399_, 9, v_maxHeartbeats_1389_);
lean_ctor_set(v___x_1399_, 10, v_quotContext_1390_);
lean_ctor_set(v___x_1399_, 11, v_currMacroScope_1391_);
lean_ctor_set(v___x_1399_, 12, v_cancelTk_x3f_1393_);
lean_ctor_set(v___x_1399_, 13, v_inheritedTraceOptions_1395_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*14, v_diag_1392_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*14 + 1, v_suppressElabErrors_1394_);
lean_inc(v_p_1379_);
v___x_1400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1379_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v___x_1399_, v_a_1359_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1480_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1480_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1480_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
if (lean_obj_tag(v_a_1401_) == 1)
{
lean_object* v_val_1405_; lean_object* v_snd_1406_; uint8_t v_hasTrace_1407_; 
lean_del_object(v___x_1403_);
v_val_1405_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v_a_1401_, 1);
v_snd_1406_ = lean_ctor_get(v_val_1405_, 1);
lean_inc(v_snd_1406_);
v_hasTrace_1407_ = lean_ctor_get_uint8(v_options_1382_, sizeof(void*)*1);
if (v_hasTrace_1407_ == 0)
{
lean_object* v_fst_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; 
lean_dec_ref(v_inheritedTraceOptions_1395_);
lean_dec_ref(v_options_1382_);
v_fst_1408_ = lean_ctor_get(v_val_1405_, 0);
lean_inc(v_fst_1408_);
lean_dec(v_val_1405_);
v_fst_1409_ = lean_ctor_get(v_snd_1406_, 0);
lean_inc(v_fst_1409_);
v_snd_1410_ = lean_ctor_get(v_snd_1406_, 1);
lean_inc(v_snd_1410_);
lean_dec(v_snd_1406_);
v___y_1362_ = v_fst_1409_;
v___y_1363_ = v_snd_1410_;
v___y_1364_ = v_fst_1408_;
v___y_1365_ = v_a_1349_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v___x_1399_;
v___y_1375_ = v_a_1359_;
goto v___jp_1361_;
}
else
{
lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1475_; 
v_fst_1411_ = lean_ctor_get(v_val_1405_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_val_1405_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v_val_1405_, 1);
lean_dec(v_unused_1476_);
v___x_1413_ = v_val_1405_;
v_isShared_1414_ = v_isSharedCheck_1475_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v_val_1405_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1475_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1474_; 
v_fst_1415_ = lean_ctor_get(v_snd_1406_, 0);
v_snd_1416_ = lean_ctor_get(v_snd_1406_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_snd_1406_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1418_ = v_snd_1406_;
v_isShared_1419_ = v_isSharedCheck_1474_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_inc(v_fst_1415_);
lean_dec(v_snd_1406_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1474_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1422_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1395_, v_options_1382_, v___x_1421_);
lean_dec_ref(v_options_1382_);
lean_dec_ref(v_inheritedTraceOptions_1395_);
if (v___x_1422_ == 0)
{
lean_del_object(v___x_1418_);
lean_del_object(v___x_1413_);
v___y_1362_ = v_fst_1415_;
v___y_1363_ = v_snd_1416_;
v___y_1364_ = v_fst_1411_;
v___y_1365_ = v_a_1349_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v___x_1399_;
v___y_1375_ = v_a_1359_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1411_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v___x_1399_, v_a_1359_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v___x_1399_, v_a_1359_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1415_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v___x_1399_, v_a_1359_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = l_Lean_MessageData_ofExpr(v_a_1424_);
v___x_1430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 7);
lean_ctor_set(v___x_1418_, 1, v___x_1430_);
lean_ctor_set(v___x_1418_, 0, v___x_1429_);
v___x_1432_ = v___x_1418_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = l_Lean_MessageData_ofExpr(v_a_1426_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 7);
lean_ctor_set(v___x_1413_, 1, v___x_1433_);
lean_ctor_set(v___x_1413_, 0, v___x_1432_);
v___x_1435_ = v___x_1413_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1430_);
v___x_1437_ = l_Lean_MessageData_ofExpr(v_a_1428_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1420_, v___x_1438_, v_a_1356_, v_a_1357_, v___x_1399_, v_a_1359_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
v___y_1362_ = v_fst_1415_;
v___y_1363_ = v_snd_1416_;
v___y_1364_ = v_fst_1411_;
v___y_1365_ = v_a_1349_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v___x_1399_;
v___y_1375_ = v_a_1359_;
goto v___jp_1361_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_dec(v_fst_1411_);
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_c_1348_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1426_);
lean_dec(v_a_1424_);
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_del_object(v___x_1413_);
lean_dec(v_fst_1411_);
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_c_1348_);
v_a_1450_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1427_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1427_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1424_);
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_del_object(v___x_1413_);
lean_dec(v_fst_1411_);
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_c_1348_);
v_a_1458_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1425_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1425_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1418_);
lean_dec(v_snd_1416_);
lean_dec(v_fst_1415_);
lean_del_object(v___x_1413_);
lean_dec(v_fst_1411_);
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_c_1348_);
v_a_1466_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1423_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1423_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
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
lean_object* v___x_1478_; 
lean_dec(v_a_1401_);
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_inheritedTraceOptions_1395_);
lean_dec_ref(v_options_1382_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_c_1348_);
v___x_1478_ = v___x_1403_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_c_1348_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref_known(v___x_1399_, 14);
lean_dec_ref(v_inheritedTraceOptions_1395_);
lean_dec_ref(v_options_1382_);
lean_dec_ref(v_c_1348_);
v_a_1481_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1400_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1400_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_ref_1513_; lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1523_; 
v_ref_1513_ = lean_ctor_get(v___y_1510_, 5);
v___x_1514_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_inc(v_ref_1513_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_ref_1513_);
lean_ctor_set(v___x_1519_, 1, v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
lean_ctor_set(v___x_1517_, 0, v___x_1519_);
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1558_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1558_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_leFn_x3f_1551_; 
v_leFn_x3f_1551_ = lean_ctor_get(v_a_1547_, 20);
lean_inc(v_leFn_x3f_1551_);
lean_dec(v_a_1547_);
if (lean_obj_tag(v_leFn_x3f_1551_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; 
v_val_1552_ = lean_ctor_get(v_leFn_x3f_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v_leFn_x3f_1551_, 1);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_val_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v_leFn_x3f_1551_);
lean_del_object(v___x_1549_);
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1557_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1556_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1546_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1546_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec(v___y_1616_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1629_, uint8_t v_strict_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (v_strict_1630_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1657_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_ofNatZero_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v_ofNatZero_1652_ = lean_ctor_get(v_a_1648_, 18);
lean_inc_ref(v_ofNatZero_1652_);
lean_dec(v_a_1648_);
v___x_1653_ = l_Lean_mkAppB(v_a_1644_, v_a_1646_, v_ofNatZero_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1646_);
lean_dec(v_a_1644_);
v_a_1658_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1647_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1647_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_dec(v_a_1644_);
return v___x_1645_;
}
}
else
{
return v___x_1643_;
}
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_ofNatZero_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v_ofNatZero_1675_ = lean_ctor_get(v_a_1671_, 18);
lean_inc_ref(v_ofNatZero_1675_);
lean_dec(v_a_1671_);
v___x_1676_ = l_Lean_mkAppB(v_a_1667_, v_a_1669_, v_ofNatZero_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1667_);
v_a_1681_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1670_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1670_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_dec(v_a_1667_);
return v___x_1668_;
}
}
else
{
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1689_, lean_object* v_strict_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
uint8_t v_strict_boxed_1703_; lean_object* v_res_1704_; 
v_strict_boxed_1703_ = lean_unbox(v_strict_1690_);
v_res_1704_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1689_, v_strict_boxed_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec(v_p_1689_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_p_1718_; uint8_t v_strict_1719_; lean_object* v___x_1720_; 
v_p_1718_ = lean_ctor_get(v_c_1705_, 0);
v_strict_1719_ = lean_ctor_get_uint8(v_c_1705_, sizeof(void*)*2);
v___x_1720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1718_, v_strict_1719_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v_c_1721_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1735_, lean_object* v_x_1736_, lean_object* v_c_u2081_1737_, lean_object* v_b_1738_, lean_object* v_c_u2082_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_options_1752_; lean_object* v_p_1753_; lean_object* v_p_1754_; uint8_t v_strict_1755_; lean_object* v_inheritedTraceOptions_1756_; uint8_t v_hasTrace_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_p_1762_; 
v_options_1752_ = lean_ctor_get(v_a_1749_, 2);
v_p_1753_ = lean_ctor_get(v_c_u2081_1737_, 0);
v_p_1754_ = lean_ctor_get(v_c_u2082_1739_, 0);
v_strict_1755_ = lean_ctor_get_uint8(v_c_u2082_1739_, sizeof(void*)*2);
v_inheritedTraceOptions_1756_ = lean_ctor_get(v_a_1749_, 13);
v_hasTrace_1757_ = lean_ctor_get_uint8(v_options_1752_, sizeof(void*)*1);
v___x_1758_ = lean_nat_to_int(v_a_1735_);
lean_inc(v_p_1754_);
v___x_1759_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1754_, v___x_1758_);
lean_dec(v___x_1758_);
v___x_1760_ = lean_int_neg(v_b_1738_);
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
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1736_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1737_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
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
v___x_1784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1767_, v___x_1783_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref_known(v___x_1784_, 1);
goto v___jp_1763_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_p_1762_);
lean_dec_ref(v_c_u2082_1739_);
lean_dec_ref(v_c_u2081_1737_);
lean_dec(v_x_1736_);
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
lean_dec_ref(v_c_u2082_1739_);
lean_dec_ref(v_c_u2081_1737_);
lean_dec(v_x_1736_);
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
lean_dec_ref(v_c_u2082_1739_);
lean_dec_ref(v_c_u2081_1737_);
lean_dec(v_x_1736_);
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
lean_dec_ref(v_c_u2082_1739_);
lean_dec_ref(v_c_u2081_1737_);
lean_dec(v_x_1736_);
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
lean_ctor_set(v___x_1764_, 0, v_x_1736_);
lean_ctor_set(v___x_1764_, 1, v_c_u2081_1737_);
lean_ctor_set(v___x_1764_, 2, v_c_u2082_1739_);
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
v_options_2805_ = lean_ctor_get(v_a_2777_, 2);
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
lean_object* v_inheritedTraceOptions_2807_; lean_object* v_cls_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_inheritedTraceOptions_2807_ = lean_ctor_get(v_a_2777_, 13);
v_cls_2808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2807_, v_options_2805_, v___x_2809_);
if (v___x_2810_ == 0)
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
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = l_Lean_MessageData_ofExpr(v_a_2812_);
v___x_2814_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2808_, v___x_2813_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
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
return v___x_2814_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_a_2815_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2811_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2811_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_c_2823_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_p_2850_; lean_object* v_fileName_2851_; lean_object* v_fileMap_2852_; lean_object* v_options_2853_; lean_object* v_currRecDepth_2854_; lean_object* v_maxRecDepth_2855_; lean_object* v_ref_2856_; lean_object* v_currNamespace_2857_; lean_object* v_openDecls_2858_; lean_object* v_initHeartbeats_2859_; lean_object* v_maxHeartbeats_2860_; lean_object* v_quotContext_2861_; lean_object* v_currMacroScope_2862_; uint8_t v_diag_2863_; lean_object* v_cancelTk_x3f_2864_; uint8_t v_suppressElabErrors_2865_; lean_object* v_inheritedTraceOptions_2866_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v_p_2850_ = lean_ctor_get(v_c_u2082_2837_, 0);
v_fileName_2851_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_ref(v_fileName_2851_);
v_fileMap_2852_ = lean_ctor_get(v_a_2847_, 1);
lean_inc_ref(v_fileMap_2852_);
v_options_2853_ = lean_ctor_get(v_a_2847_, 2);
lean_inc_ref(v_options_2853_);
v_currRecDepth_2854_ = lean_ctor_get(v_a_2847_, 3);
lean_inc(v_currRecDepth_2854_);
v_maxRecDepth_2855_ = lean_ctor_get(v_a_2847_, 4);
lean_inc(v_maxRecDepth_2855_);
v_ref_2856_ = lean_ctor_get(v_a_2847_, 5);
lean_inc(v_ref_2856_);
v_currNamespace_2857_ = lean_ctor_get(v_a_2847_, 6);
lean_inc(v_currNamespace_2857_);
v_openDecls_2858_ = lean_ctor_get(v_a_2847_, 7);
lean_inc(v_openDecls_2858_);
v_initHeartbeats_2859_ = lean_ctor_get(v_a_2847_, 8);
lean_inc(v_initHeartbeats_2859_);
v_maxHeartbeats_2860_ = lean_ctor_get(v_a_2847_, 9);
lean_inc(v_maxHeartbeats_2860_);
v_quotContext_2861_ = lean_ctor_get(v_a_2847_, 10);
lean_inc(v_quotContext_2861_);
v_currMacroScope_2862_ = lean_ctor_get(v_a_2847_, 11);
lean_inc(v_currMacroScope_2862_);
v_diag_2863_ = lean_ctor_get_uint8(v_a_2847_, sizeof(void*)*14);
v_cancelTk_x3f_2864_ = lean_ctor_get(v_a_2847_, 12);
lean_inc(v_cancelTk_x3f_2864_);
v_suppressElabErrors_2865_ = lean_ctor_get_uint8(v_a_2847_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2866_ = lean_ctor_get(v_a_2847_, 13);
lean_inc_ref(v_inheritedTraceOptions_2866_);
lean_dec_ref(v_a_2847_);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = lean_nat_dec_eq(v_maxRecDepth_2855_, v___x_2918_);
if (v___x_2919_ == 0)
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_nat_dec_eq(v_currRecDepth_2854_, v_maxRecDepth_2855_);
if (v___x_2920_ == 0)
{
goto v___jp_2867_;
}
else
{
lean_object* v___x_2921_; 
lean_dec_ref(v_inheritedTraceOptions_2866_);
lean_dec(v_cancelTk_x3f_2864_);
lean_dec(v_currMacroScope_2862_);
lean_dec(v_quotContext_2861_);
lean_dec(v_maxHeartbeats_2860_);
lean_dec(v_initHeartbeats_2859_);
lean_dec(v_openDecls_2858_);
lean_dec(v_currNamespace_2857_);
lean_dec(v_maxRecDepth_2855_);
lean_dec(v_currRecDepth_2854_);
lean_dec_ref(v_options_2853_);
lean_dec_ref(v_fileMap_2852_);
lean_dec_ref(v_fileName_2851_);
lean_dec_ref(v_c_u2082_2837_);
v___x_2921_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2856_);
return v___x_2921_;
}
}
else
{
goto v___jp_2867_;
}
v___jp_2867_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_currRecDepth_2854_, v___x_2868_);
lean_dec(v_currRecDepth_2854_);
v___x_2870_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2870_, 0, v_fileName_2851_);
lean_ctor_set(v___x_2870_, 1, v_fileMap_2852_);
lean_ctor_set(v___x_2870_, 2, v_options_2853_);
lean_ctor_set(v___x_2870_, 3, v___x_2869_);
lean_ctor_set(v___x_2870_, 4, v_maxRecDepth_2855_);
lean_ctor_set(v___x_2870_, 5, v_ref_2856_);
lean_ctor_set(v___x_2870_, 6, v_currNamespace_2857_);
lean_ctor_set(v___x_2870_, 7, v_openDecls_2858_);
lean_ctor_set(v___x_2870_, 8, v_initHeartbeats_2859_);
lean_ctor_set(v___x_2870_, 9, v_maxHeartbeats_2860_);
lean_ctor_set(v___x_2870_, 10, v_quotContext_2861_);
lean_ctor_set(v___x_2870_, 11, v_currMacroScope_2862_);
lean_ctor_set(v___x_2870_, 12, v_cancelTk_x3f_2864_);
lean_ctor_set(v___x_2870_, 13, v_inheritedTraceOptions_2866_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14, v_diag_2863_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14 + 1, v_suppressElabErrors_2865_);
v___x_2871_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2850_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v___x_2870_, v_a_2848_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2909_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2909_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2909_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_val_2876_; lean_object* v_snd_2877_; lean_object* v_snd_2878_; lean_object* v_fst_2879_; lean_object* v_fst_2880_; lean_object* v_p_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_del_object(v___x_2874_);
v_val_2876_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2872_, 1);
v_snd_2877_ = lean_ctor_get(v_val_2876_, 1);
lean_inc(v_snd_2877_);
v_snd_2878_ = lean_ctor_get(v_snd_2877_, 1);
lean_inc(v_snd_2878_);
v_fst_2879_ = lean_ctor_get(v_val_2876_, 0);
lean_inc(v_fst_2879_);
lean_dec(v_val_2876_);
v_fst_2880_ = lean_ctor_get(v_snd_2877_, 0);
lean_inc(v_fst_2880_);
lean_dec(v_snd_2877_);
v_p_2881_ = lean_ctor_get(v_snd_2878_, 0);
v___x_2882_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2881_, v_fst_2880_);
lean_inc_ref(v_c_u2082_2837_);
v___x_2883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2882_, v_fst_2880_, v_snd_2878_, v_fst_2879_, v_c_u2082_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v___x_2870_, v_a_2848_);
lean_dec(v_fst_2880_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
if (lean_obj_tag(v_a_2884_) == 1)
{
lean_object* v_val_2885_; 
lean_dec_ref(v_c_u2082_2837_);
v_val_2885_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v_a_2884_, 1);
v_c_u2082_2837_ = v_val_2885_;
v_a_2847_ = v___x_2870_;
goto _start;
}
else
{
lean_object* v___x_2887_; 
lean_dec(v_a_2884_);
v___x_2887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v___x_2870_, v_a_2848_);
lean_dec_ref_known(v___x_2870_, 14);
lean_dec_ref(v_c_u2082_2837_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2895_; 
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; 
v_unused_2896_ = lean_ctor_get(v___x_2887_, 0);
lean_dec(v_unused_2896_);
v___x_2889_ = v___x_2887_;
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
else
{
lean_dec(v___x_2887_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2891_ = lean_box(0);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v___x_2891_);
v___x_2893_ = v___x_2889_;
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
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2887_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2887_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2870_, 14);
lean_dec_ref(v_c_u2082_2837_);
return v___x_2883_;
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_a_2872_);
lean_dec_ref_known(v___x_2870_, 14);
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_c_u2082_2837_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2905_);
v___x_2907_ = v___x_2874_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
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
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref_known(v___x_2870_, 14);
lean_dec_ref(v_c_u2082_2837_);
v_a_2910_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2871_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2871_);
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
size_t v_x_41010__boxed_2985_; size_t v_x_41011__boxed_2986_; lean_object* v_res_2987_; 
v_x_41010__boxed_2985_ = lean_unbox_usize(v_x_2983_);
lean_dec(v_x_2983_);
v_x_41011__boxed_2986_ = lean_unbox_usize(v_x_2984_);
lean_dec(v_x_2984_);
v_res_2987_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2981_, v_x_2982_, v_x_41010__boxed_2985_, v_x_41011__boxed_2986_);
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
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_MessageData_ofExpr(v_a_3285_);
v___x_3287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3281_, v___x_3286_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref_known(v___x_3287_, 1);
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
v___x_3167_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref_known(v___x_3167_, 1);
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
lean_dec_ref_known(v___x_3170_, 1);
v___x_3171_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3154_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
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
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
return v___x_3170_;
}
}
else
{
lean_dec_ref(v___y_3154_);
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
lean_dec_ref_known(v_a_3224_, 1);
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
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = l_Lean_MessageData_ofExpr(v_a_3237_);
v___x_3239_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3233_, v___x_3238_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref_known(v___x_3239_, 1);
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
v___y_3154_ = v_val_3228_;
v___y_3155_ = v_p_3229_;
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
v___y_3154_ = v_val_3228_;
v___y_3155_ = v_p_3229_;
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
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l_Lean_MessageData_ofExpr(v_a_3257_);
v___x_3259_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3253_, v___x_3258_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_dec_ref_known(v___x_3259_, 1);
lean_inc(v_val_3228_);
lean_inc(v_v_3251_);
v___y_3151_ = v_v_3251_;
v___y_3152_ = v_val_3228_;
v___y_3153_ = v_v_3251_;
v___y_3154_ = v_val_3228_;
v___y_3155_ = v_p_3229_;
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
lean_dec_ref_known(v_p_3229_, 3);
lean_dec(v_val_3228_);
return v___x_3259_;
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_v_3251_);
lean_dec_ref_known(v_p_3229_, 3);
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
lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v_options_4520_; lean_object* v_inheritedTraceOptions_4521_; uint8_t v_hasTrace_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v_options_4539_; lean_object* v_inheritedTraceOptions_4540_; lean_object* v___y_4541_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; 
v_options_4520_ = lean_ctor_get(v_a_4451_, 2);
v_inheritedTraceOptions_4521_ = lean_ctor_get(v_a_4451_, 13);
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
lean_object* v_cls_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v_cls_4664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4521_, v_options_4520_, v___x_4665_);
if (v___x_4666_ == 0)
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
lean_object* v___x_4667_; 
v___x_4667_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = l_Lean_MessageData_ofExpr(v_a_4668_);
v___x_4670_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4664_, v___x_4669_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_dec_ref_known(v___x_4670_, 1);
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
return v___x_4670_;
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec_ref(v_c_4441_);
v_a_4671_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4667_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4667_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
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
v___x_4477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4462_, v___y_4460_, v___y_4461_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4477_;
}
else
{
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
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
v___x_4498_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4482_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
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
lean_inc_ref(v___y_4482_);
v___x_4501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4482_);
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
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
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
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
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
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
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
v___x_4544_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4540_, v_options_4539_, v___x_4543_);
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
v___x_4545_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4527_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4541_);
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
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
return v___x_4548_;
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
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
v_options_4577_ = lean_ctor_get(v___y_4567_, 2);
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
v___y_4482_ = v_snd_4581_;
v___y_4483_ = v_fst_4579_;
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
lean_object* v_fst_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4628_; 
v_fst_4582_ = lean_ctor_get(v_a_4575_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_a_4575_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v_a_4575_, 1);
lean_dec(v_unused_4629_);
v___x_4584_ = v_a_4575_;
v_isShared_4585_ = v_isSharedCheck_4628_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_fst_4582_);
lean_dec(v_a_4575_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4628_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v_fst_4586_; lean_object* v_snd_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4627_; 
v_fst_4586_ = lean_ctor_get(v_snd_4576_, 0);
v_snd_4587_ = lean_ctor_get(v_snd_4576_, 1);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_snd_4576_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4589_ = v_snd_4576_;
v_isShared_4590_ = v_isSharedCheck_4627_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_snd_4587_);
lean_inc(v_fst_4586_);
lean_dec(v_snd_4576_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4627_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v_inheritedTraceOptions_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v_inheritedTraceOptions_4591_ = lean_ctor_get(v___y_4567_, 13);
v___x_4592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4591_, v_options_4577_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_del_object(v___x_4589_);
lean_del_object(v___x_4584_);
lean_inc(v_snd_4587_);
lean_inc(v_fst_4586_);
v___y_4524_ = v_fst_4586_;
v___y_4525_ = v_snd_4587_;
v___y_4526_ = v_fst_4586_;
v___y_4527_ = v_snd_4587_;
v___y_4528_ = v_fst_4582_;
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
v_options_4539_ = v_options_4577_;
v_inheritedTraceOptions_4540_ = v_inheritedTraceOptions_4591_;
v___y_4541_ = v___y_4568_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4595_; 
v___x_4595_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4586_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4597_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_a_4596_);
lean_dec_ref_known(v___x_4595_, 1);
v___x_4597_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4587_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
v___x_4599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4600_ = l_Lean_MessageData_ofExpr(v_a_4596_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set_tag(v___x_4589_, 7);
lean_ctor_set(v___x_4589_, 1, v___x_4600_);
lean_ctor_set(v___x_4589_, 0, v___x_4599_);
v___x_4602_ = v___x_4589_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4585_ == 0)
{
lean_ctor_set_tag(v___x_4584_, 7);
lean_ctor_set(v___x_4584_, 1, v___x_4603_);
lean_ctor_set(v___x_4584_, 0, v___x_4602_);
v___x_4605_ = v___x_4584_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = l_Lean_MessageData_ofExpr(v_a_4598_);
v___x_4607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4605_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
v___x_4608_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4592_, v___x_4607_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_dec_ref_known(v___x_4608_, 1);
lean_inc(v_snd_4587_);
lean_inc(v_fst_4586_);
v___y_4524_ = v_fst_4586_;
v___y_4525_ = v_snd_4587_;
v___y_4526_ = v_fst_4586_;
v___y_4527_ = v_snd_4587_;
v___y_4528_ = v_fst_4582_;
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
v_options_4539_ = v_options_4577_;
v_inheritedTraceOptions_4540_ = v_inheritedTraceOptions_4591_;
v___y_4541_ = v___y_4568_;
goto v___jp_4523_;
}
else
{
lean_dec(v_snd_4587_);
lean_dec(v_fst_4586_);
lean_dec(v_fst_4582_);
return v___x_4608_;
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_dec(v_a_4596_);
lean_del_object(v___x_4589_);
lean_dec(v_snd_4587_);
lean_dec(v_fst_4586_);
lean_del_object(v___x_4584_);
lean_dec(v_fst_4582_);
v_a_4611_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4597_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4597_);
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
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_del_object(v___x_4589_);
lean_dec(v_snd_4587_);
lean_dec(v_fst_4586_);
lean_del_object(v___x_4584_);
lean_dec(v_fst_4582_);
v_a_4619_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4595_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4595_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
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
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
v_a_4630_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4574_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4574_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
else
{
lean_object* v_options_4638_; uint8_t v_hasTrace_4639_; 
v_options_4638_ = lean_ctor_get(v___y_4567_, 2);
v_hasTrace_4639_ = lean_ctor_get_uint8(v_options_4638_, sizeof(void*)*1);
if (v_hasTrace_4639_ == 0)
{
lean_dec(v_a_4570_);
goto v___jp_4454_;
}
else
{
lean_object* v_inheritedTraceOptions_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; 
v_inheritedTraceOptions_4640_ = lean_ctor_get(v___y_4567_, 13);
v___x_4641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4640_, v_options_4638_, v___x_4642_);
if (v___x_4643_ == 0)
{
lean_dec(v_a_4570_);
goto v___jp_4454_;
}
else
{
lean_object* v___x_4644_; 
v___x_4644_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4570_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v_a_4570_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = l_Lean_MessageData_ofExpr(v_a_4645_);
v___x_4647_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4641_, v___x_4646_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_dec_ref_known(v___x_4647_, 1);
goto v___jp_4454_;
}
else
{
return v___x_4647_;
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
v_a_4648_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4644_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4644_);
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
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
v_a_4656_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4569_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4569_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec(v_a_4680_);
return v_res_4692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_cls_4697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4699_ = l_Lean_Name_append(v___x_4698_, v_cls_4697_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4700_, lean_object* v_b_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_options_4710_; uint8_t v_hasTrace_4711_; 
v_options_4710_ = lean_ctor_get(v_a_4704_, 2);
v_hasTrace_4711_ = lean_ctor_get_uint8(v_options_4710_, sizeof(void*)*1);
if (v_hasTrace_4711_ == 0)
{
lean_dec_ref(v_b_4701_);
lean_dec_ref(v_a_4700_);
goto v___jp_4707_;
}
else
{
lean_object* v_inheritedTraceOptions_4712_; lean_object* v_cls_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v_inheritedTraceOptions_4712_ = lean_ctor_get(v_a_4704_, 13);
v_cls_4713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4715_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4712_, v_options_4710_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_dec_ref(v_b_4701_);
lean_dec_ref(v_a_4700_);
goto v___jp_4707_;
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4716_ = l_Lean_MessageData_ofExpr(v_a_4700_);
v___x_4717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4716_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
v___x_4719_ = l_Lean_MessageData_ofExpr(v_b_4701_);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4713_, v___x_4720_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
return v___x_4721_;
}
}
v___jp_4707_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4722_, lean_object* v_b_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4722_, v_b_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4730_, lean_object* v_b_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4730_, v_b_4731_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4745_, lean_object* v_b_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4745_, v_b_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec(v_a_4747_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4760_, lean_object* v_b_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4760_, v_a_4763_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; uint8_t v___x_4776_; lean_object* v___x_4777_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v___x_4774_, 1);
v___x_4776_ = 0;
lean_inc_ref(v_a_4760_);
v___x_4777_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4760_, v___x_4776_, v_a_4775_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4827_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4827_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4827_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
if (lean_obj_tag(v_a_4778_) == 1)
{
lean_object* v_val_4782_; lean_object* v___x_4783_; 
lean_del_object(v___x_4780_);
v_val_4782_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_val_4782_);
lean_dec_ref_known(v_a_4778_, 1);
v___x_4783_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4761_, v_a_4763_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4785_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
lean_inc_ref(v_b_4761_);
v___x_4785_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4761_, v___x_4776_, v_a_4784_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4806_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4806_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4806_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
if (lean_obj_tag(v_a_4786_) == 1)
{
lean_object* v_val_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v_val_4790_ = lean_ctor_get(v_a_4786_, 0);
lean_inc_n(v_val_4790_, 2);
lean_dec_ref_known(v_a_4786_, 1);
lean_inc(v_val_4782_);
v___x_4791_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4791_, 0, v_val_4782_);
lean_ctor_set(v___x_4791_, 1, v_val_4790_);
v___x_4792_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4791_);
v___x_4793_ = lean_box(0);
v___x_4794_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4792_, v___x_4793_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_del_object(v___x_4788_);
v___x_4795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4795_, 0, v_a_4760_);
lean_ctor_set(v___x_4795_, 1, v_b_4761_);
lean_ctor_set(v___x_4795_, 2, v_val_4782_);
lean_ctor_set(v___x_4795_, 3, v_val_4790_);
v___x_4796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4792_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
v___x_4797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4796_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
return v___x_4797_;
}
else
{
lean_object* v___x_4798_; lean_object* v___x_4800_; 
lean_dec(v___x_4792_);
lean_dec(v_val_4790_);
lean_dec(v_val_4782_);
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v___x_4798_ = lean_box(0);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4798_);
v___x_4800_ = v___x_4788_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v_a_4786_);
lean_dec(v_val_4782_);
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v___x_4802_ = lean_box(0);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4802_);
v___x_4804_ = v___x_4788_;
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
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec(v_val_4782_);
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v_a_4807_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4785_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4785_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
lean_dec(v_val_4782_);
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v_a_4815_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4783_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4783_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
lean_dec(v_a_4778_);
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v___x_4823_ = lean_box(0);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4823_);
v___x_4825_ = v___x_4780_;
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
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v_a_4828_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4777_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4777_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
lean_dec_ref(v_b_4761_);
lean_dec_ref(v_a_4760_);
v_a_4836_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4774_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4774_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4839_ == 0)
{
v___x_4841_ = v___x_4838_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4844_, lean_object* v_b_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4844_, v_b_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec(v_a_4846_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4859_, lean_object* v_b_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4873_, 1);
lean_inc_ref(v_a_4859_);
v___x_4875_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4859_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v_fst_4877_; lean_object* v___x_4878_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
v_fst_4877_ = lean_ctor_get(v_a_4876_, 0);
lean_inc(v_fst_4877_);
lean_dec(v_a_4876_);
lean_inc_ref(v_b_4860_);
v___x_4878_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v_fst_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4963_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4878_, 1);
v_fst_4880_ = lean_ctor_get(v_a_4879_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v_a_4879_);
if (v_isSharedCheck_4963_ == 0)
{
lean_object* v_unused_4964_; 
v_unused_4964_ = lean_ctor_get(v_a_4879_, 1);
lean_dec(v_unused_4964_);
v___x_4882_ = v_a_4879_;
v_isShared_4883_ = v_isSharedCheck_4963_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_fst_4880_);
lean_dec(v_a_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4963_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; 
v___x_4884_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4859_, v_a_4862_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v_id_4886_; lean_object* v_structId_4887_; uint8_t v___x_4888_; lean_object* v___x_4889_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v_id_4886_ = lean_ctor_get(v_a_4874_, 0);
lean_inc(v_id_4886_);
v_structId_4887_ = lean_ctor_get(v_a_4874_, 1);
lean_inc(v_structId_4887_);
lean_dec(v_a_4874_);
v___x_4888_ = 0;
v___x_4889_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4877_, v___x_4888_, v_a_4885_, v_structId_4887_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4946_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4946_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4946_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
if (lean_obj_tag(v_a_4890_) == 1)
{
lean_object* v_val_4894_; lean_object* v___x_4895_; 
lean_del_object(v___x_4892_);
v_val_4894_ = lean_ctor_get(v_a_4890_, 0);
lean_inc(v_val_4894_);
lean_dec_ref_known(v_a_4890_, 1);
v___x_4895_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4860_, v_a_4862_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref_known(v___x_4895_, 1);
v___x_4897_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4880_, v___x_4888_, v_a_4896_, v_structId_4887_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4925_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4925_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4925_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
if (lean_obj_tag(v_a_4898_) == 1)
{
lean_object* v_val_4902_; lean_object* v___x_4904_; 
v_val_4902_ = lean_ctor_get(v_a_4898_, 0);
lean_inc_n(v_val_4902_, 2);
lean_dec_ref_known(v_a_4898_, 1);
lean_inc(v_val_4894_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set_tag(v___x_4882_, 3);
lean_ctor_set(v___x_4882_, 1, v_val_4902_);
lean_ctor_set(v___x_4882_, 0, v_val_4894_);
v___x_4904_ = v___x_4882_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_val_4894_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_val_4902_);
v___x_4904_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4905_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4904_);
v___x_4906_ = lean_box(0);
v___x_4907_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4905_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
lean_del_object(v___x_4900_);
lean_inc(v_val_4902_);
lean_inc(v_val_4894_);
lean_inc(v_id_4886_);
lean_inc_ref(v_b_4860_);
lean_inc_ref(v_a_4859_);
v___x_4908_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4908_, 0, v_a_4859_);
lean_ctor_set(v___x_4908_, 1, v_b_4860_);
lean_ctor_set(v___x_4908_, 2, v_id_4886_);
lean_ctor_set(v___x_4908_, 3, v_val_4894_);
lean_ctor_set(v___x_4908_, 4, v_val_4902_);
lean_inc(v___x_4905_);
v___x_4909_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4909_, 0, v___x_4905_);
lean_ctor_set(v___x_4909_, 1, v___x_4908_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*2, v___x_4888_);
v___x_4910_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4909_, v_structId_4887_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec_ref_known(v___x_4910_, 1);
v___x_4911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4912_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4905_, v___x_4911_);
v___x_4913_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4913_, 0, v_b_4860_);
lean_ctor_set(v___x_4913_, 1, v_a_4859_);
lean_ctor_set(v___x_4913_, 2, v_id_4886_);
lean_ctor_set(v___x_4913_, 3, v_val_4902_);
lean_ctor_set(v___x_4913_, 4, v_val_4894_);
v___x_4914_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
lean_ctor_set_uint8(v___x_4914_, sizeof(void*)*2, v___x_4888_);
v___x_4915_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4914_, v_structId_4887_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
lean_dec(v_structId_4887_);
return v___x_4915_;
}
else
{
lean_dec(v___x_4905_);
lean_dec(v_val_4902_);
lean_dec(v_val_4894_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
return v___x_4910_;
}
}
else
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
lean_dec(v___x_4905_);
lean_dec(v_val_4902_);
lean_dec(v_val_4894_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v___x_4916_ = lean_box(0);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_4916_);
v___x_4918_ = v___x_4900_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
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
lean_object* v___x_4921_; lean_object* v___x_4923_; 
lean_dec(v_a_4898_);
lean_dec(v_val_4894_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_del_object(v___x_4882_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v___x_4921_ = lean_box(0);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_4921_);
v___x_4923_ = v___x_4900_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_dec(v_val_4894_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_del_object(v___x_4882_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4926_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4897_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4897_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_dec(v_val_4894_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_del_object(v___x_4882_);
lean_dec(v_fst_4880_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4934_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4895_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4895_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
else
{
lean_object* v___x_4942_; lean_object* v___x_4944_; 
lean_dec(v_a_4890_);
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_del_object(v___x_4882_);
lean_dec(v_fst_4880_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v___x_4942_ = lean_box(0);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 0, v___x_4942_);
v___x_4944_ = v___x_4892_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___x_4942_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec(v_structId_4887_);
lean_dec(v_id_4886_);
lean_del_object(v___x_4882_);
lean_dec(v_fst_4880_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4947_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4889_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4889_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
else
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
lean_del_object(v___x_4882_);
lean_dec(v_fst_4880_);
lean_dec(v_fst_4877_);
lean_dec(v_a_4874_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4955_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4884_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4884_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
lean_dec(v_fst_4877_);
lean_dec(v_a_4874_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4965_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4878_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4878_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec(v_a_4874_);
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4973_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4875_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4875_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_a_4859_);
v_a_4981_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4873_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4873_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4989_, lean_object* v_b_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4989_, v_b_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec(v_a_4991_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5004_, lean_object* v_b_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5020_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref_known(v___x_5018_, 1);
lean_inc_ref(v_a_5004_);
v___x_5020_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5004_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v_fst_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5118_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5020_, 1);
v_fst_5022_ = lean_ctor_get(v_a_5021_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v_a_5021_);
if (v_isSharedCheck_5118_ == 0)
{
lean_object* v_unused_5119_; 
v_unused_5119_ = lean_ctor_get(v_a_5021_, 1);
lean_dec(v_unused_5119_);
v___x_5024_ = v_a_5021_;
v_isShared_5025_ = v_isSharedCheck_5118_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_fst_5022_);
lean_dec(v_a_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5118_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; 
lean_inc_ref(v_b_5005_);
v___x_5026_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v_fst_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5108_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5026_, 1);
v_fst_5028_ = lean_ctor_get(v_a_5027_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v_a_5027_);
if (v_isSharedCheck_5108_ == 0)
{
lean_object* v_unused_5109_; 
v_unused_5109_ = lean_ctor_get(v_a_5027_, 1);
lean_dec(v_unused_5109_);
v___x_5030_ = v_a_5027_;
v_isShared_5031_ = v_isSharedCheck_5108_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_fst_5028_);
lean_dec(v_a_5027_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5108_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5032_; 
v___x_5032_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5004_, v_a_5007_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v_id_5034_; lean_object* v_structId_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v_id_5034_ = lean_ctor_get(v_a_5019_, 0);
lean_inc(v_id_5034_);
v_structId_5035_ = lean_ctor_get(v_a_5019_, 1);
lean_inc(v_structId_5035_);
lean_dec(v_a_5019_);
v___x_5036_ = 0;
v___x_5037_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5022_, v___x_5036_, v_a_5033_, v_structId_5035_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5091_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5040_ = v___x_5037_;
v_isShared_5041_ = v_isSharedCheck_5091_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5037_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5091_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
if (lean_obj_tag(v_a_5038_) == 1)
{
lean_object* v_val_5042_; lean_object* v___x_5043_; 
lean_del_object(v___x_5040_);
v_val_5042_ = lean_ctor_get(v_a_5038_, 0);
lean_inc(v_val_5042_);
lean_dec_ref_known(v_a_5038_, 1);
v___x_5043_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5005_, v_a_5007_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5045_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref_known(v___x_5043_, 1);
v___x_5045_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5028_, v___x_5036_, v_a_5044_, v_structId_5035_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5070_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5070_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5070_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
if (lean_obj_tag(v_a_5046_) == 1)
{
lean_object* v_val_5050_; lean_object* v___x_5052_; 
v_val_5050_ = lean_ctor_get(v_a_5046_, 0);
lean_inc_n(v_val_5050_, 2);
lean_dec_ref_known(v_a_5046_, 1);
lean_inc(v_val_5042_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set_tag(v___x_5030_, 3);
lean_ctor_set(v___x_5030_, 1, v_val_5050_);
lean_ctor_set(v___x_5030_, 0, v_val_5042_);
v___x_5052_ = v___x_5030_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_val_5042_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_val_5050_);
v___x_5052_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v___x_5053_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5052_);
v___x_5054_ = lean_box(0);
v___x_5055_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5053_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
lean_del_object(v___x_5048_);
v___x_5056_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5056_, 0, v_a_5004_);
lean_ctor_set(v___x_5056_, 1, v_b_5005_);
lean_ctor_set(v___x_5056_, 2, v_id_5034_);
lean_ctor_set(v___x_5056_, 3, v_val_5042_);
lean_ctor_set(v___x_5056_, 4, v_val_5050_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v___x_5056_);
lean_ctor_set(v___x_5024_, 0, v___x_5053_);
v___x_5058_ = v___x_5024_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5053_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; 
v___x_5059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5058_, v_structId_5035_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
lean_dec(v_structId_5035_);
return v___x_5059_;
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5063_; 
lean_dec(v___x_5053_);
lean_dec(v_val_5050_);
lean_dec(v_val_5042_);
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v___x_5061_ = lean_box(0);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 0, v___x_5061_);
v___x_5063_ = v___x_5048_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5061_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5068_; 
lean_dec(v_a_5046_);
lean_dec(v_val_5042_);
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5030_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v___x_5066_ = lean_box(0);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 0, v___x_5066_);
v___x_5068_ = v___x_5048_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
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
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec(v_val_5042_);
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5030_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5071_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5045_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5045_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v_val_5042_);
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5079_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5043_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5043_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
else
{
lean_object* v___x_5087_; lean_object* v___x_5089_; 
lean_dec(v_a_5038_);
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v___x_5087_ = lean_box(0);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5087_);
v___x_5089_ = v___x_5040_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec(v_structId_5035_);
lean_dec(v_id_5034_);
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_del_object(v___x_5024_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5092_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5037_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5037_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_dec(v_a_5019_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5100_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5032_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5032_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_del_object(v___x_5024_);
lean_dec(v_fst_5022_);
lean_dec(v_a_5019_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5110_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5026_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5026_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_dec(v_a_5019_);
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5120_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5020_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5020_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
lean_dec_ref(v_b_5005_);
lean_dec_ref(v_a_5004_);
v_a_5128_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5130_ = v___x_5018_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5018_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5136_, lean_object* v_b_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5136_, v_b_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_a_5144_);
lean_dec_ref(v_a_5143_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec(v_a_5139_);
lean_dec(v_a_5138_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5151_, lean_object* v_b_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
size_t v___x_5164_; size_t v___x_5165_; uint8_t v___x_5166_; 
v___x_5164_ = lean_ptr_addr(v_a_5151_);
v___x_5165_ = lean_ptr_addr(v_b_5152_);
v___x_5166_ = lean_usize_dec_eq(v___x_5164_, v___x_5165_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
v___x_5167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5151_, v_b_5152_, v_a_5153_, v_a_5161_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
if (lean_obj_tag(v_a_5168_) == 1)
{
lean_object* v_val_5169_; lean_object* v___x_5170_; 
v_val_5169_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5169_);
lean_dec_ref_known(v_a_5168_, 1);
v___x_5170_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; uint8_t v___x_5172_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_a_5171_);
lean_dec_ref_known(v___x_5170_, 1);
v___x_5172_ = lean_unbox(v_a_5171_);
lean_dec(v_a_5171_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; 
v___x_5173_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; uint8_t v___x_5175_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
lean_dec_ref_known(v___x_5173_, 1);
v___x_5175_ = lean_unbox(v_a_5174_);
lean_dec(v_a_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5151_, v_b_5152_, v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_val_5169_);
return v___x_5176_;
}
else
{
lean_object* v___x_5177_; 
lean_dec(v_val_5169_);
v___x_5177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5151_, v_b_5152_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
return v___x_5177_;
}
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec(v_val_5169_);
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
v___x_5186_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; uint8_t v___x_5188_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5186_, 1);
v___x_5188_ = lean_unbox(v_a_5187_);
lean_dec(v_a_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5151_, v_b_5152_, v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_val_5169_);
return v___x_5189_;
}
else
{
lean_object* v___x_5190_; 
v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5151_, v_b_5152_, v_val_5169_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_val_5169_);
return v___x_5190_;
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
lean_dec(v_val_5169_);
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
v___x_5207_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5151_, v_b_5152_, v_a_5153_, v_a_5161_);
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
lean_dec_ref_known(v_a_5208_, 1);
v___x_5213_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5212_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v_orderedAddInst_x3f_5215_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc(v_a_5214_);
lean_dec_ref_known(v___x_5213_, 1);
v_orderedAddInst_x3f_5215_ = lean_ctor_get(v_a_5214_, 9);
lean_inc(v_orderedAddInst_x3f_5215_);
lean_dec(v_a_5214_);
if (lean_obj_tag(v_orderedAddInst_x3f_5215_) == 0)
{
lean_object* v___x_5216_; 
v___x_5216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5151_, v_b_5152_, v_val_5212_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_val_5212_);
return v___x_5216_;
}
else
{
lean_object* v___x_5217_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5215_, 1);
v___x_5217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5151_, v_b_5152_, v_val_5212_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_val_5212_);
return v___x_5217_;
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_dec(v_val_5212_);
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref(v_b_5152_);
lean_dec_ref(v_a_5151_);
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
lean_dec_ref_known(v_a_5282_, 1);
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
lean_dec_ref_known(v_a_5290_, 1);
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
lean_dec_ref_known(v___x_5299_, 1);
v___x_5301_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5263_, v_a_5266_);
lean_dec_ref(v_a_5263_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5303_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref_known(v___x_5301_, 1);
v___x_5303_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5264_, v_a_5266_);
lean_dec_ref(v_b_5264_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v_p_5305_; lean_object* v___y_5307_; uint8_t v___x_5341_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref_known(v___x_5303_, 1);
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
lean_dec_ref_known(v___x_5308_, 1);
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
lean_dec_ref_known(v_a_5311_, 1);
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
lean_dec_ref_known(v___x_5421_, 1);
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
lean_dec_ref_known(v_a_5425_, 1);
v___x_5430_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5408_, v_a_5410_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5432_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_a_5431_);
lean_dec_ref_known(v___x_5430_, 1);
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
lean_dec_ref_known(v_a_5433_, 1);
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
lean_dec_ref_known(v___x_5514_, 1);
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
lean_dec_ref_known(v___x_5520_, 1);
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
lean_dec_ref_known(v___x_5526_, 1);
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
lean_dec_ref_known(v___x_5532_, 1);
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
lean_dec_ref_known(v_a_5536_, 1);
v___x_5541_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5501_, v_a_5503_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5543_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref_known(v___x_5541_, 1);
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
lean_dec_ref_known(v_a_5544_, 1);
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
lean_dec_ref_known(v___x_5656_, 1);
if (lean_obj_tag(v_a_5657_) == 1)
{
lean_object* v_val_5658_; lean_object* v___x_5659_; 
v_val_5658_ = lean_ctor_get(v_a_5657_, 0);
lean_inc(v_val_5658_);
lean_dec_ref_known(v_a_5657_, 1);
v___x_5659_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5658_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; uint8_t v___x_5661_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref_known(v___x_5659_, 1);
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
lean_dec_ref_known(v_a_5673_, 1);
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
