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
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_377_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 2);
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
lean_object* v___x_336_; lean_object* v_traceState_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_cache_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_376_; 
v___x_336_ = lean_st_ref_take(v___y_328_);
v_traceState_337_ = lean_ctor_get(v___x_336_, 4);
v_env_338_ = lean_ctor_get(v___x_336_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_336_, 1);
v_ngen_340_ = lean_ctor_get(v___x_336_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_336_, 3);
v_cache_342_ = lean_ctor_get(v___x_336_, 5);
v_recordedDeps_343_ = lean_ctor_get(v___x_336_, 6);
v_messages_344_ = lean_ctor_get(v___x_336_, 7);
v_infoState_345_ = lean_ctor_get(v___x_336_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_336_, 9);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_376_ == 0)
{
v___x_348_ = v___x_336_;
v_isShared_349_ = v_isSharedCheck_376_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
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
lean_object* v___x_355_; lean_object* v___x_356_; double v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_box(0);
v___x_357_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_358_ = 0;
v___x_359_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_360_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_360_, 0, v_cls_323_);
lean_ctor_set(v___x_360_, 1, v___x_356_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_ctor_set_float(v___x_360_, sizeof(void*)*3, v___x_357_);
lean_ctor_set_float(v___x_360_, sizeof(void*)*3 + 8, v___x_357_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*3 + 16, v___x_358_);
v___x_361_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_362_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v_a_332_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_inc(v_ref_330_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_ref_330_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = l_Lean_PersistentArray_push___redArg(v_traces_351_, v___x_363_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_364_);
v___x_366_ = v___x_353_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_364_);
lean_ctor_set_uint64(v_reuseFailAlloc_374_, sizeof(void*)*1, v_tid_350_);
v___x_366_ = v_reuseFailAlloc_374_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 4, v___x_366_);
v___x_368_ = v___x_348_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_338_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_342_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_snapshotTasks_346_);
v___x_368_ = v_reuseFailAlloc_373_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_st_ref_put(v___y_328_, v___x_368_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_355_);
v___x_371_ = v___x_334_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_355_);
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
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_541_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_541_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_541_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_541_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_536_; 
v_val_422_ = lean_ctor_get(v_a_418_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_536_ == 0)
{
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_536_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_536_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_snd_426_; lean_object* v_snd_427_; lean_object* v_toCold_428_; lean_object* v_options_429_; lean_object* v_fst_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_534_; 
v_snd_426_ = lean_ctor_get(v_val_422_, 1);
lean_inc(v_snd_426_);
v_snd_427_ = lean_ctor_get(v_snd_426_, 1);
lean_inc(v_snd_427_);
v_toCold_428_ = lean_ctor_get(v_a_414_, 0);
v_options_429_ = lean_ctor_get(v_toCold_428_, 2);
v_fst_430_ = lean_ctor_get(v_val_422_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_val_422_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_val_422_, 1);
lean_dec(v_unused_535_);
v___x_432_ = v_val_422_;
v_isShared_433_ = v_isSharedCheck_534_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_fst_430_);
lean_dec(v_val_422_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_534_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_fst_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_532_; 
v_fst_434_ = lean_ctor_get(v_snd_426_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_snd_426_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_snd_426_, 1);
lean_dec(v_unused_533_);
v___x_436_ = v_snd_426_;
v_isShared_437_ = v_isSharedCheck_532_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_fst_434_);
lean_dec(v_snd_426_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_532_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_p_438_; lean_object* v_inheritedTraceOptions_439_; uint8_t v_hasTrace_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_p_438_ = lean_ctor_get(v_snd_427_, 0);
v_inheritedTraceOptions_439_ = lean_ctor_get(v_toCold_428_, 11);
v_hasTrace_440_ = lean_ctor_get_uint8(v_options_429_, sizeof(void*)*1);
v___x_441_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_438_, v_fst_434_);
lean_inc(v_p_404_);
v___x_442_ = l_Lean_Grind_Linarith_Poly_mul(v_p_404_, v___x_441_);
v___x_443_ = lean_int_neg(v_fst_430_);
lean_inc(v_p_438_);
v___x_444_ = l_Lean_Grind_Linarith_Poly_mul(v_p_438_, v___x_443_);
lean_dec(v___x_443_);
v___x_445_ = l_Lean_Grind_Linarith_Poly_combine(v___x_442_, v___x_444_);
if (v_hasTrace_440_ == 0)
{
lean_dec(v___x_441_);
lean_dec(v_fst_430_);
lean_dec(v_p_404_);
goto v___jp_446_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_460_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_439_, v_options_429_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v___x_441_);
lean_dec(v_fst_430_);
lean_dec(v_p_404_);
goto v___jp_446_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_p_404_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_434_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_427_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_445_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l_Lean_MessageData_ofExpr(v_a_463_);
v___x_471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Int_repr(v_fst_430_);
lean_dec(v_fst_430_);
v___x_474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___x_475_ = l_Lean_MessageData_ofFormat(v___x_474_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_472_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_471_);
v___x_478_ = l_Lean_MessageData_ofExpr(v_a_465_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_471_);
v___x_481_ = l_Lean_MessageData_ofExpr(v_a_467_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_471_);
v___x_484_ = l_Int_repr(v___x_441_);
lean_dec(v___x_441_);
v___x_485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
v___x_486_ = l_Lean_MessageData_ofFormat(v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_483_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_471_);
v___x_489_ = l_Lean_MessageData_ofExpr(v_a_469_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_459_, v___x_490_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec_ref_known(v___x_491_, 1);
goto v___jp_446_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v___x_445_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_del_object(v___x_432_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_467_);
lean_dec(v_a_465_);
lean_dec(v_a_463_);
lean_dec(v___x_445_);
lean_dec(v___x_441_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_del_object(v___x_432_);
lean_dec(v_fst_430_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_500_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_468_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_468_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_465_);
lean_dec(v_a_463_);
lean_dec(v___x_445_);
lean_dec(v___x_441_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_del_object(v___x_432_);
lean_dec(v_fst_430_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_508_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_466_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_466_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_a_463_);
lean_dec(v___x_445_);
lean_dec(v___x_441_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_del_object(v___x_432_);
lean_dec(v_fst_430_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_516_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_464_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_464_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v___x_445_);
lean_dec(v___x_441_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_del_object(v___x_432_);
lean_dec(v_fst_430_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_524_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_462_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_462_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
v___jp_446_:
{
lean_object* v___x_448_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_445_);
lean_ctor_set(v___x_436_, 0, v_snd_427_);
v___x_448_ = v___x_436_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_snd_427_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_445_);
v___x_448_ = v_reuseFailAlloc_458_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_448_);
lean_ctor_set(v___x_432_, 0, v_fst_434_);
v___x_450_ = v___x_432_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_457_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_450_);
v___x_452_ = v___x_424_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_452_);
v___x_454_ = v___x_420_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
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
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_a_418_);
lean_dec(v_p_404_);
v___x_537_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_537_);
v___x_539_ = v___x_420_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_p_404_);
v_a_542_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_417_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_417_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
lean_dec(v_a_551_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_564_, v_msg_565_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_579_, v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec(v___y_582_);
lean_dec(v___y_581_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_p_607_; lean_object* v___x_608_; 
v_p_607_ = lean_ctor_get(v_c_594_, 0);
v___x_608_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_607_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v_ofNatZero_612_; lean_object* v___x_613_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v_ofNatZero_612_ = lean_ctor_get(v_a_611_, 18);
lean_inc_ref(v_ofNatZero_612_);
lean_dec(v_a_611_);
v___x_613_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_609_, v_ofNatZero_612_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_622_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_mkNot(v_a_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
return v___x_613_;
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_609_);
v_a_623_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_610_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_610_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v_c_631_);
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_nat_to_int(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_cls_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_653_ = l_Lean_Name_append(v___x_652_, v_cls_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_654_, lean_object* v_x_655_, lean_object* v_c_u2081_656_, lean_object* v_b_657_, lean_object* v_c_u2082_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v_toCold_725_; lean_object* v_options_726_; uint8_t v_hasTrace_727_; 
v_toCold_725_ = lean_ctor_get(v_a_668_, 0);
v_options_726_ = lean_ctor_get(v_toCold_725_, 2);
v_hasTrace_727_ = lean_ctor_get_uint8(v_options_726_, sizeof(void*)*1);
if (v_hasTrace_727_ == 0)
{
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
v___y_682_ = v_a_669_;
goto v___jp_671_;
}
else
{
lean_object* v_inheritedTraceOptions_728_; lean_object* v_cls_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_inheritedTraceOptions_728_ = lean_ctor_get(v_toCold_725_, 11);
v_cls_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_728_, v_options_726_, v___x_730_);
if (v___x_731_ == 0)
{
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
v___y_682_ = v_a_669_;
goto v___jp_671_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_655_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_656_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_MessageData_ofExpr(v_a_733_);
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_MessageData_ofExpr(v_a_735_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_739_);
v___x_744_ = l_Lean_MessageData_ofExpr(v_a_737_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_729_, v___x_745_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref_known(v___x_746_, 1);
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
v___y_682_ = v_a_669_;
goto v___jp_671_;
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_735_);
lean_dec(v_a_733_);
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v_a_755_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_736_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_736_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_733_);
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v_a_763_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_734_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_734_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v_a_771_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_732_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_732_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
v___jp_671_:
{
lean_object* v_p_683_; lean_object* v_p_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_p_683_ = lean_ctor_get(v_c_u2081_656_, 0);
v_p_684_ = lean_ctor_get(v_c_u2082_658_, 0);
v___x_685_ = lean_int_emod(v_b_657_, v_a_654_);
v___x_686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_687_ = lean_int_dec_eq(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_708_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = lean_unbox(v_a_689_);
lean_dec(v_a_689_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v___x_694_ = lean_box(0);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_inc(v_p_683_);
v___x_698_ = l_Lean_Grind_Linarith_Poly_mul(v_p_683_, v_b_657_);
v___x_699_ = lean_int_neg(v_a_654_);
lean_inc(v_p_684_);
v___x_700_ = l_Lean_Grind_Linarith_Poly_mul(v_p_684_, v___x_699_);
v___x_701_ = l_Lean_Grind_Linarith_Poly_combine(v___x_698_, v___x_700_);
v___x_702_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_702_, 0, v___x_699_);
lean_ctor_set(v___x_702_, 1, v_b_657_);
lean_ctor_set(v___x_702_, 2, v_c_u2081_656_);
lean_ctor_set(v___x_702_, 3, v_c_u2082_658_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_704_);
v___x_706_ = v___x_691_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_c_u2082_658_);
lean_dec(v_b_657_);
lean_dec_ref(v_c_u2081_656_);
v_a_709_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_688_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_688_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_717_ = lean_int_neg(v_b_657_);
lean_dec(v_b_657_);
v___x_718_ = lean_int_ediv(v___x_717_, v_a_654_);
lean_dec(v___x_717_);
lean_inc(v_p_683_);
v___x_719_ = l_Lean_Grind_Linarith_Poly_mul(v_p_683_, v___x_718_);
lean_inc(v_p_684_);
v___x_720_ = l_Lean_Grind_Linarith_Poly_combine(v___x_719_, v_p_684_);
v___x_721_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_718_);
lean_ctor_set(v___x_721_, 1, v_c_u2081_656_);
lean_ctor_set(v___x_721_, 2, v_c_u2082_658_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_779_ = _args[0];
lean_object* v_x_780_ = _args[1];
lean_object* v_c_u2081_781_ = _args[2];
lean_object* v_b_782_ = _args[3];
lean_object* v_c_u2082_783_ = _args[4];
lean_object* v_a_784_ = _args[5];
lean_object* v_a_785_ = _args[6];
lean_object* v_a_786_ = _args[7];
lean_object* v_a_787_ = _args[8];
lean_object* v_a_788_ = _args[9];
lean_object* v_a_789_ = _args[10];
lean_object* v_a_790_ = _args[11];
lean_object* v_a_791_ = _args[12];
lean_object* v_a_792_ = _args[13];
lean_object* v_a_793_ = _args[14];
lean_object* v_a_794_ = _args[15];
lean_object* v_a_795_ = _args[16];
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_779_, v_x_780_, v_c_u2081_781_, v_b_782_, v_c_u2082_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec(v_a_785_);
lean_dec(v_a_784_);
lean_dec(v_x_780_);
lean_dec(v_a_779_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_797_, lean_object* v_b_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_797_, v_a_799_, v_a_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_831_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_831_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
if (lean_obj_tag(v_a_803_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_808_; 
lean_del_object(v___x_805_);
v_val_807_ = lean_ctor_get(v_a_803_, 0);
v___x_808_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_798_, v_a_799_, v_a_800_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_826_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_826_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_826_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_826_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
if (lean_obj_tag(v_a_809_) == 1)
{
lean_object* v_val_813_; uint8_t v___x_814_; 
v_val_813_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_a_809_, 1);
v___x_814_ = lean_nat_dec_eq(v_val_807_, v_val_813_);
lean_dec(v_val_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref_known(v_a_803_, 1);
v___x_815_ = lean_box(0);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_820_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_a_803_);
v___x_820_ = v___x_811_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_803_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_a_809_);
lean_dec_ref_known(v_a_803_, 1);
v___x_822_ = lean_box(0);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_822_);
v___x_824_ = v___x_811_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_803_, 1);
return v___x_808_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_803_);
v___x_827_ = lean_box(0);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_827_);
v___x_829_ = v___x_805_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_832_, lean_object* v_b_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_832_, v_b_833_, v_a_834_, v_a_835_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_b_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_838_, lean_object* v_b_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_838_, v_b_839_, v_a_840_, v_a_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_852_, v_b_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_b_853_);
lean_dec_ref(v_a_852_);
return v_res_865_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_867_ = lean_int_neg(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_882_ = 0;
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_box(v___x_882_);
lean_inc_ref(v_a_868_);
v___x_885_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_885_, 0, v_a_868_);
lean_closure_set(v___x_885_, 1, v___x_884_);
lean_closure_set(v___x_885_, 2, v___x_883_);
v___x_886_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_885_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_1038_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_1038_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_1038_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
if (lean_obj_tag(v_a_887_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_del_object(v___x_889_);
v_val_891_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v_a_887_, 1);
v___x_892_ = lean_box(v___x_882_);
lean_inc_ref(v_b_869_);
v___x_893_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_893_, 0, v_b_869_);
lean_closure_set(v___x_893_, 1, v___x_892_);
lean_closure_set(v___x_893_, 2, v___x_883_);
v___x_894_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_893_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_1025_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_1025_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_1025_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_900_; 
lean_del_object(v___x_897_);
v_val_899_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_a_895_, 1);
v___x_900_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_868_, v_a_871_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_869_, v_a_871_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___y_905_; uint8_t v___x_1004_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_1004_ = lean_nat_dec_le(v_a_901_, v_a_903_);
if (v___x_1004_ == 0)
{
lean_dec(v_a_903_);
v___y_905_ = v_a_901_;
goto v___jp_904_;
}
else
{
lean_dec(v_a_901_);
v___y_905_ = v_a_903_;
goto v___jp_904_;
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc(v_val_899_);
lean_inc(v_val_891_);
v___x_906_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_906_, 0, v_val_891_);
lean_ctor_set(v___x_906_, 1, v_val_899_);
v___x_907_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_908_, 0, v_a_868_);
lean_ctor_set(v___x_908_, 1, v_b_869_);
lean_ctor_set(v___x_908_, 2, v_val_891_);
lean_ctor_set(v___x_908_, 3, v_val_899_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_909_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v_p_912_; lean_object* v___x_913_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v_p_912_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v___y_905_);
lean_inc_ref(v_p_912_);
v___x_913_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_912_, v___y_905_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
lean_inc(v___y_905_);
v___x_915_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_914_, v___x_882_, v___y_905_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_979_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_979_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_979_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_979_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_a_916_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_val_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc_n(v_val_920_, 2);
lean_dec_ref_known(v_a_916_, 1);
v___x_921_ = l_Lean_Grind_Linarith_Expr_norm(v_val_920_);
v___x_922_ = lean_box(0);
v___x_923_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_918_);
lean_inc(v_a_911_);
v___x_924_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_924_, 0, v_a_911_);
lean_ctor_set(v___x_924_, 1, v_val_920_);
lean_inc(v___x_921_);
v___x_925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_925_, 0, v___x_921_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*2, v___x_882_);
v___x_926_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_925_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_969_; 
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_970_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_969_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_969_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_912_);
v___x_931_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_930_, v_p_912_);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 1);
lean_ctor_set(v___x_928_, 0, v_a_911_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_911_);
v___x_933_ = v_reuseFailAlloc_968_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc_ref(v___x_931_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_Grind_Linarith_Poly_mul(v___x_921_, v___x_930_);
lean_inc(v___y_905_);
v___x_936_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_931_, v___y_905_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_937_, v___x_882_, v___y_905_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_951_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_951_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_941_);
v_val_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_a_939_, 1);
v___x_944_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_934_);
lean_ctor_set(v___x_944_, 1, v_val_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_945_, 0, v___x_935_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*2, v___x_882_);
v___x_946_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_945_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v_a_939_);
lean_dec(v___x_935_);
lean_dec_ref_known(v___x_934_, 2);
v___x_947_ = lean_box(0);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_947_);
v___x_949_ = v___x_941_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v___x_935_);
lean_dec_ref_known(v___x_934_, 2);
v_a_952_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_938_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_938_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v___x_935_);
lean_dec_ref_known(v___x_934_, 2);
lean_dec(v___y_905_);
v_a_960_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_936_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_936_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
else
{
lean_dec(v___x_921_);
lean_dec(v_a_911_);
lean_dec(v___y_905_);
return v___x_926_;
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v___x_921_);
lean_dec(v_val_920_);
lean_dec(v_a_911_);
lean_dec(v___y_905_);
v___x_971_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_971_);
v___x_973_ = v___x_918_;
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
else
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_dec(v_a_916_);
lean_dec(v_a_911_);
lean_dec(v___y_905_);
v___x_975_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_975_);
v___x_977_ = v___x_918_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_911_);
lean_dec(v___y_905_);
v_a_980_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_915_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_915_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_a_911_);
lean_dec(v___y_905_);
v_a_988_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_913_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_913_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v___y_905_);
v_a_996_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_910_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_910_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v_a_901_);
lean_dec(v_val_899_);
lean_dec(v_val_891_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v_a_1005_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_902_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_902_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_val_899_);
lean_dec(v_val_891_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v_a_1013_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_900_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_900_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v_a_895_);
lean_dec(v_val_891_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v___x_1021_ = lean_box(0);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_1021_);
v___x_1023_ = v___x_897_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_val_891_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v_a_1026_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_894_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_894_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec(v_a_887_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v___x_1034_ = lean_box(0);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_1034_);
v___x_1036_ = v___x_889_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
v_a_1039_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_886_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_886_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1047_, lean_object* v_b_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1047_, v_b_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1062_, v_a_1065_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = 0;
lean_inc_ref(v_a_1062_);
v___x_1079_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1062_, v___x_1078_, v_a_1077_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1134_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1134_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1134_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_a_1080_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
lean_del_object(v___x_1082_);
v_val_1084_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_a_1080_, 1);
v___x_1085_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1063_, v_a_1065_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
lean_inc_ref(v_b_1063_);
v___x_1087_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1063_, v___x_1078_, v_a_1086_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1113_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
if (lean_obj_tag(v_a_1088_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_val_1092_ = lean_ctor_get(v_a_1088_, 0);
lean_inc_n(v_val_1092_, 2);
lean_dec_ref_known(v_a_1088_, 1);
lean_inc(v_val_1084_);
v___x_1093_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_val_1084_);
lean_ctor_set(v___x_1093_, 1, v_val_1092_);
v___x_1094_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1093_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_del_object(v___x_1090_);
lean_inc(v_val_1092_);
lean_inc(v_val_1084_);
lean_inc_ref(v_b_1063_);
lean_inc_ref(v_a_1062_);
v___x_1097_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1097_, 0, v_a_1062_);
lean_ctor_set(v___x_1097_, 1, v_b_1063_);
lean_ctor_set(v___x_1097_, 2, v_val_1084_);
lean_ctor_set(v___x_1097_, 3, v_val_1092_);
lean_inc(v___x_1094_);
v___x_1098_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1094_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2, v___x_1078_);
v___x_1099_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1098_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref_known(v___x_1099_, 1);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1101_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1094_, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1102_, 0, v_b_1063_);
lean_ctor_set(v___x_1102_, 1, v_a_1062_);
lean_ctor_set(v___x_1102_, 2, v_val_1092_);
lean_ctor_set(v___x_1102_, 3, v_val_1084_);
v___x_1103_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*2, v___x_1078_);
v___x_1104_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1103_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1104_;
}
else
{
lean_dec(v___x_1094_);
lean_dec(v_val_1092_);
lean_dec(v_val_1084_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
return v___x_1099_;
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_dec(v___x_1094_);
lean_dec(v_val_1092_);
lean_dec(v_val_1084_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v___x_1105_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1105_);
v___x_1107_ = v___x_1090_;
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
else
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec(v_a_1088_);
lean_dec(v_val_1084_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v___x_1109_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1109_);
v___x_1111_ = v___x_1090_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_val_1084_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v_a_1114_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1087_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1087_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_val_1084_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v_a_1122_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1085_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1085_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_1080_);
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v___x_1130_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1130_);
v___x_1132_ = v___x_1082_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v_a_1135_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1079_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1079_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_a_1062_);
v_a_1143_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1076_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1076_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1151_, lean_object* v_b_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1151_, v_b_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
return v_res_1165_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___x_2795__overap_1182_; lean_object* v___x_1183_; 
v___x_1180_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1181_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1181_, 0, v___x_1180_);
v___x_2795__overap_1182_ = lean_panic_fn_borrowed(v___f_1181_, v_msg_1167_);
lean_dec_ref(v___f_1181_);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc(v___y_1168_);
v___x_1183_ = lean_apply_12(v___x_2795__overap_1182_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, lean_box(0));
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_nat_to_int(v_a_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1204_ = lean_unsigned_to_nat(42u);
v___x_1205_ = lean_unsigned_to_nat(87u);
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1208_ = l_mkPanicMessageWithDecl(v___x_1207_, v___x_1206_, v___x_1205_, v___x_1204_, v___x_1203_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v_c_1225_; lean_object* v_c_1231_; lean_object* v_p_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_object* v_p_1271_; 
v_p_1271_ = lean_ctor_get(v_c_1209_, 0);
lean_inc(v_p_1271_);
v_c_1231_ = v_c_1209_;
v_p_1232_ = v_p_1271_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
goto v___jp_1230_;
}
else
{
lean_object* v_p_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_p_1272_ = lean_ctor_get(v_c_1209_, 0);
v___x_1273_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1272_);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_inc(v___x_1273_);
v___x_1276_ = lean_nat_to_int(v___x_1273_);
lean_inc(v_p_1272_);
v___x_1277_ = l_Lean_Grind_Linarith_Poly_div(v_p_1272_, v___x_1276_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1273_);
lean_ctor_set(v___x_1278_, 1, v_c_1209_);
lean_inc(v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v_c_1231_ = v___x_1279_;
v_p_1232_ = v___x_1277_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
goto v___jp_1230_;
}
else
{
lean_inc(v_p_1272_);
lean_dec(v___x_1273_);
v_c_1231_ = v_c_1209_;
v_p_1232_ = v_p_1272_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
goto v___jp_1230_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_c_1209_);
v_a_1280_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1268_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1268_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
v___jp_1222_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_nat_abs(v___y_1223_);
lean_dec(v___y_1223_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___y_1224_);
lean_ctor_set(v___x_1227_, 1, v_c_1225_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
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
v___y_1223_ = v_fst_1249_;
v___y_1224_ = v_snd_1250_;
v_c_1225_ = v_c_1231_;
goto v___jp_1222_;
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
v___y_1223_ = v_fst_1249_;
v___y_1224_ = v_snd_1250_;
v_c_1225_ = v___x_1261_;
goto v___jp_1222_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec(v_a_1289_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_Lean_maxRecDepthErrorMessage;
v___x_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1310_ = l_Lean_MessageData_ofFormat(v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1312_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1313_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_ref_1314_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1322_, lean_object* v_ref_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1323_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_ref_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1337_, v_ref_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v_toCold_1383_; lean_object* v_p_1384_; lean_object* v_currRecDepth_1385_; lean_object* v_ref_1386_; uint16_t v_optionFlags_1387_; uint8_t v_suppressElabErrors_1388_; uint8_t v_isRecordingDeps_1389_; lean_object* v_options_1390_; lean_object* v_maxRecDepth_1391_; lean_object* v_inheritedTraceOptions_1392_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_toCold_1383_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref(v_toCold_1383_);
v_p_1384_ = lean_ctor_get(v_c_1352_, 0);
v_currRecDepth_1385_ = lean_ctor_get(v_a_1362_, 1);
lean_inc(v_currRecDepth_1385_);
v_ref_1386_ = lean_ctor_get(v_a_1362_, 2);
lean_inc(v_ref_1386_);
v_optionFlags_1387_ = lean_ctor_get_uint16(v_a_1362_, sizeof(void*)*3);
v_suppressElabErrors_1388_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1389_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1362_);
v_options_1390_ = lean_ctor_get(v_toCold_1383_, 2);
lean_inc_ref(v_options_1390_);
v_maxRecDepth_1391_ = lean_ctor_get(v_toCold_1383_, 3);
v_inheritedTraceOptions_1392_ = lean_ctor_get(v_toCold_1383_, 11);
lean_inc_ref(v_inheritedTraceOptions_1392_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_nat_dec_eq(v_maxRecDepth_1391_, v___x_1486_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_eq(v_currRecDepth_1385_, v_maxRecDepth_1391_);
if (v___x_1488_ == 0)
{
goto v___jp_1393_;
}
else
{
lean_object* v___x_1489_; 
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
lean_dec(v_currRecDepth_1385_);
lean_dec_ref(v_toCold_1383_);
lean_dec_ref(v_c_1352_);
v___x_1489_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1386_);
return v___x_1489_;
}
}
else
{
goto v___jp_1393_;
}
v___jp_1365_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___y_1367_);
lean_ctor_set(v___x_1380_, 1, v___y_1368_);
lean_ctor_set(v___x_1380_, 2, v_c_1352_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1366_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v_c_1352_ = v___x_1381_;
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
v_a_1363_ = v___y_1379_;
goto _start;
}
v___jp_1393_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_add(v_currRecDepth_1385_, v___x_1394_);
lean_dec(v_currRecDepth_1385_);
v___x_1396_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1396_, 0, v_toCold_1383_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
lean_ctor_set(v___x_1396_, 2, v_ref_1386_);
lean_ctor_set_uint16(v___x_1396_, sizeof(void*)*3, v_optionFlags_1387_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 2, v_suppressElabErrors_1388_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 3, v_isRecordingDeps_1389_);
lean_inc(v_p_1384_);
v___x_1397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1384_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1477_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1477_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1477_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1402_; lean_object* v_snd_1403_; uint8_t v_hasTrace_1404_; 
lean_del_object(v___x_1400_);
v_val_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_a_1398_, 1);
v_snd_1403_ = lean_ctor_get(v_val_1402_, 1);
lean_inc(v_snd_1403_);
v_hasTrace_1404_ = lean_ctor_get_uint8(v_options_1390_, sizeof(void*)*1);
if (v_hasTrace_1404_ == 0)
{
lean_object* v_fst_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; 
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
v_fst_1405_ = lean_ctor_get(v_val_1402_, 0);
lean_inc(v_fst_1405_);
lean_dec(v_val_1402_);
v_fst_1406_ = lean_ctor_get(v_snd_1403_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_snd_1403_);
v___y_1366_ = v_snd_1407_;
v___y_1367_ = v_fst_1405_;
v___y_1368_ = v_fst_1406_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1472_; 
v_fst_1408_ = lean_ctor_get(v_val_1402_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_val_1402_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_val_1402_, 1);
lean_dec(v_unused_1473_);
v___x_1410_ = v_val_1402_;
v_isShared_1411_ = v_isSharedCheck_1472_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_fst_1408_);
lean_dec(v_val_1402_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1472_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1471_; 
v_fst_1412_ = lean_ctor_get(v_snd_1403_, 0);
v_snd_1413_ = lean_ctor_get(v_snd_1403_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_snd_1403_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1415_ = v_snd_1403_;
v_isShared_1416_ = v_isSharedCheck_1471_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snd_1413_);
lean_inc(v_fst_1412_);
lean_dec(v_snd_1403_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1471_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1392_, v_options_1390_, v___x_1418_);
lean_dec_ref(v_options_1390_);
lean_dec_ref(v_inheritedTraceOptions_1392_);
if (v___x_1419_ == 0)
{
lean_del_object(v___x_1415_);
lean_del_object(v___x_1410_);
v___y_1366_ = v_snd_1413_;
v___y_1367_ = v_fst_1408_;
v___y_1368_ = v_fst_1412_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1408_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1412_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_MessageData_ofExpr(v_a_1421_);
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1427_);
lean_ctor_set(v___x_1415_, 0, v___x_1426_);
v___x_1429_ = v___x_1415_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l_Lean_MessageData_ofExpr(v_a_1423_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 7);
lean_ctor_set(v___x_1410_, 1, v___x_1430_);
lean_ctor_set(v___x_1410_, 0, v___x_1429_);
v___x_1432_ = v___x_1410_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1427_);
v___x_1434_ = l_Lean_MessageData_ofExpr(v_a_1425_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1417_, v___x_1435_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
v___y_1366_ = v_snd_1413_;
v___y_1367_ = v_fst_1408_;
v___y_1368_ = v_fst_1412_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
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
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1447_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1424_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1424_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1455_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1422_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1422_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1463_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1420_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1420_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
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
lean_object* v___x_1475_; 
lean_dec(v_a_1398_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_c_1352_);
v___x_1475_ = v___x_1400_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_c_1352_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
lean_dec_ref(v_c_1352_);
v_a_1478_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1397_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1397_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_ref_1510_; lean_object* v___x_1511_; lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1520_; 
v_ref_1510_ = lean_ctor_get(v___y_1507_, 2);
v___x_1511_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_inc(v_ref_1510_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_ref_1510_);
lean_ctor_set(v___x_1516_, 1, v_a_1512_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1555_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_leFn_x3f_1548_; 
v_leFn_x3f_1548_ = lean_ctor_get(v_a_1544_, 20);
lean_inc(v_leFn_x3f_1548_);
lean_dec(v_a_1544_);
if (lean_obj_tag(v_leFn_x3f_1548_) == 1)
{
lean_object* v_val_1549_; lean_object* v___x_1551_; 
v_val_1549_ = lean_ctor_get(v_leFn_x3f_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_leFn_x3f_1548_, 1);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v_val_1549_);
v___x_1551_ = v___x_1546_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_val_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v_leFn_x3f_1548_);
lean_del_object(v___x_1546_);
v___x_1553_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1554_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1553_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1543_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1543_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec(v___y_1564_);
return v_res_1576_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1604_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_ltFn_x3f_1597_; 
v_ltFn_x3f_1597_ = lean_ctor_get(v_a_1593_, 21);
lean_inc(v_ltFn_x3f_1597_);
lean_dec(v_a_1593_);
if (lean_obj_tag(v_ltFn_x3f_1597_) == 1)
{
lean_object* v_val_1598_; lean_object* v___x_1600_; 
v_val_1598_ = lean_ctor_get(v_ltFn_x3f_1597_, 0);
lean_inc(v_val_1598_);
lean_dec_ref_known(v_ltFn_x3f_1597_, 1);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_val_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_val_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_ltFn_x3f_1597_);
lean_del_object(v___x_1595_);
v___x_1602_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1603_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1602_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1592_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1592_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1626_, uint8_t v_strict_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
if (v_strict_1627_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___x_1644_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1654_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v_ofNatZero_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_ofNatZero_1649_ = lean_ctor_get(v_a_1645_, 18);
lean_inc_ref(v_ofNatZero_1649_);
lean_dec(v_a_1645_);
v___x_1650_ = l_Lean_mkAppB(v_a_1641_, v_a_1643_, v_ofNatZero_1649_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_a_1643_);
lean_dec(v_a_1641_);
v_a_1655_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1644_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1644_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_dec(v_a_1641_);
return v___x_1642_;
}
}
else
{
return v___x_1640_;
}
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1677_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_ofNatZero_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v_ofNatZero_1672_ = lean_ctor_get(v_a_1668_, 18);
lean_inc_ref(v_ofNatZero_1672_);
lean_dec(v_a_1668_);
v___x_1673_ = l_Lean_mkAppB(v_a_1664_, v_a_1666_, v_ofNatZero_1672_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1666_);
lean_dec(v_a_1664_);
v_a_1678_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1667_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1667_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_dec(v_a_1664_);
return v___x_1665_;
}
}
else
{
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1686_, lean_object* v_strict_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_strict_boxed_1700_; lean_object* v_res_1701_; 
v_strict_boxed_1700_ = lean_unbox(v_strict_1687_);
v_res_1701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1686_, v_strict_boxed_1700_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v_p_1686_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_p_1715_; uint8_t v_strict_1716_; lean_object* v___x_1717_; 
v_p_1715_ = lean_ctor_get(v_c_1702_, 0);
v_strict_1716_ = lean_ctor_get_uint8(v_c_1702_, sizeof(void*)*2);
v___x_1717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1715_, v_strict_1716_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v_c_1718_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1732_, lean_object* v_x_1733_, lean_object* v_c_u2081_1734_, lean_object* v_b_1735_, lean_object* v_c_u2082_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_toCold_1749_; lean_object* v_options_1750_; lean_object* v_p_1751_; lean_object* v_p_1752_; uint8_t v_strict_1753_; lean_object* v_inheritedTraceOptions_1754_; uint8_t v_hasTrace_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_p_1760_; 
v_toCold_1749_ = lean_ctor_get(v_a_1746_, 0);
v_options_1750_ = lean_ctor_get(v_toCold_1749_, 2);
v_p_1751_ = lean_ctor_get(v_c_u2081_1734_, 0);
v_p_1752_ = lean_ctor_get(v_c_u2082_1736_, 0);
v_strict_1753_ = lean_ctor_get_uint8(v_c_u2082_1736_, sizeof(void*)*2);
v_inheritedTraceOptions_1754_ = lean_ctor_get(v_toCold_1749_, 11);
v_hasTrace_1755_ = lean_ctor_get_uint8(v_options_1750_, sizeof(void*)*1);
v___x_1756_ = lean_nat_to_int(v_a_1732_);
lean_inc(v_p_1752_);
v___x_1757_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1752_, v___x_1756_);
lean_dec(v___x_1756_);
v___x_1758_ = lean_int_neg(v_b_1735_);
lean_inc(v_p_1751_);
v___x_1759_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1751_, v___x_1758_);
lean_dec(v___x_1758_);
v_p_1760_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1757_, v___x_1759_);
if (v_hasTrace_1755_ == 0)
{
goto v___jp_1761_;
}
else
{
lean_object* v_cls_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_cls_1765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1754_, v_options_1750_, v___x_1766_);
if (v___x_1767_ == 0)
{
goto v___jp_1761_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1733_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1734_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_MessageData_ofExpr(v_a_1769_);
v___x_1775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_MessageData_ofExpr(v_a_1771_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1775_);
v___x_1780_ = l_Lean_MessageData_ofExpr(v_a_1773_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1765_, v___x_1781_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_dec_ref_known(v___x_1782_, 1);
goto v___jp_1761_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_p_1760_);
lean_dec_ref(v_c_u2082_1736_);
lean_dec_ref(v_c_u2081_1734_);
lean_dec(v_x_1733_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_a_1771_);
lean_dec(v_a_1769_);
lean_dec(v_p_1760_);
lean_dec_ref(v_c_u2082_1736_);
lean_dec_ref(v_c_u2081_1734_);
lean_dec(v_x_1733_);
v_a_1791_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1772_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1772_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1769_);
lean_dec(v_p_1760_);
lean_dec_ref(v_c_u2082_1736_);
lean_dec_ref(v_c_u2081_1734_);
lean_dec(v_x_1733_);
v_a_1799_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1770_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1770_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_p_1760_);
lean_dec_ref(v_c_u2082_1736_);
lean_dec_ref(v_c_u2081_1734_);
lean_dec(v_x_1733_);
v_a_1807_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1768_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1768_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
v___jp_1761_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1762_, 0, v_x_1733_);
lean_ctor_set(v___x_1762_, 1, v_c_u2081_1734_);
lean_ctor_set(v___x_1762_, 2, v_c_u2082_1736_);
v___x_1763_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1763_, 0, v_p_1760_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*2, v_strict_1753_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1815_ = _args[0];
lean_object* v_x_1816_ = _args[1];
lean_object* v_c_u2081_1817_ = _args[2];
lean_object* v_b_1818_ = _args[3];
lean_object* v_c_u2082_1819_ = _args[4];
lean_object* v_a_1820_ = _args[5];
lean_object* v_a_1821_ = _args[6];
lean_object* v_a_1822_ = _args[7];
lean_object* v_a_1823_ = _args[8];
lean_object* v_a_1824_ = _args[9];
lean_object* v_a_1825_ = _args[10];
lean_object* v_a_1826_ = _args[11];
lean_object* v_a_1827_ = _args[12];
lean_object* v_a_1828_ = _args[13];
lean_object* v_a_1829_ = _args[14];
lean_object* v_a_1830_ = _args[15];
lean_object* v_a_1831_ = _args[16];
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1815_, v_x_1816_, v_c_u2081_1817_, v_b_1818_, v_c_u2082_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec(v_b_1818_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1833_, lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1834_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1848_, v_msg_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1871_, lean_object* v_x_1872_, lean_object* v_c_u2081_1873_, lean_object* v_as_1874_, size_t v_sz_1875_, size_t v_i_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_lt(v_i_1876_, v_sz_1875_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_c_u2081_1873_);
lean_dec(v_x_1872_);
lean_dec(v_a_1871_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_b_1877_);
return v___x_1891_;
}
else
{
lean_object* v_a_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec_ref(v_b_1877_);
v_a_1892_ = lean_array_uget_borrowed(v_as_1874_, v_i_1876_);
v_fst_1893_ = lean_ctor_get(v_a_1892_, 0);
v_snd_1894_ = lean_ctor_get(v_a_1892_, 1);
v___x_1895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_1894_);
lean_inc_ref(v_c_u2081_1873_);
lean_inc(v_x_1872_);
lean_inc(v_a_1871_);
v___x_1896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1871_, v_x_1872_, v_c_u2081_1873_, v_fst_1893_, v_snd_1894_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1897_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref_known(v___x_1898_, 1);
v___x_1899_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1912_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
if (v___x_1904_ == 0)
{
size_t v___x_1905_; size_t v___x_1906_; 
lean_del_object(v___x_1902_);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1876_, v___x_1905_);
v_i_1876_ = v___x_1906_;
v_b_1877_ = v___x_1895_;
goto _start;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_dec_ref(v_c_u2081_1873_);
lean_dec(v_x_1872_);
lean_dec(v_a_1871_);
v___x_1908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1908_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_c_u2081_1873_);
lean_dec(v_x_1872_);
lean_dec(v_a_1871_);
v_a_1913_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1899_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1899_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_c_u2081_1873_);
lean_dec(v_x_1872_);
lean_dec(v_a_1871_);
v_a_1921_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1898_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1898_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_c_u2081_1873_);
lean_dec(v_x_1872_);
lean_dec(v_a_1871_);
v_a_1929_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1896_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1896_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1937_ = _args[0];
lean_object* v_x_1938_ = _args[1];
lean_object* v_c_u2081_1939_ = _args[2];
lean_object* v_as_1940_ = _args[3];
lean_object* v_sz_1941_ = _args[4];
lean_object* v_i_1942_ = _args[5];
lean_object* v_b_1943_ = _args[6];
lean_object* v___y_1944_ = _args[7];
lean_object* v___y_1945_ = _args[8];
lean_object* v___y_1946_ = _args[9];
lean_object* v___y_1947_ = _args[10];
lean_object* v___y_1948_ = _args[11];
lean_object* v___y_1949_ = _args[12];
lean_object* v___y_1950_ = _args[13];
lean_object* v___y_1951_ = _args[14];
lean_object* v___y_1952_ = _args[15];
lean_object* v___y_1953_ = _args[16];
lean_object* v___y_1954_ = _args[17];
lean_object* v___y_1955_ = _args[18];
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1937_, v_x_1938_, v_c_u2081_1939_, v_as_1940_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v_as_1940_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1959_, lean_object* v_x_1960_, lean_object* v_c_u2081_1961_, lean_object* v_todo_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v_sz_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1977_ = lean_array_size(v_todo_1962_);
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1959_, v_x_1960_, v_c_u2081_1961_, v_todo_1962_, v_sz_1977_, v___x_1978_, v___x_1976_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1992_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_fst_1984_; 
v_fst_1984_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_fst_1984_);
lean_dec(v_a_1980_);
if (lean_obj_tag(v_fst_1984_) == 0)
{
lean_object* v___x_1986_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1975_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1975_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; 
v_val_1988_ = lean_ctor_get(v_fst_1984_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_fst_1984_, 1);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_val_1988_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_val_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_a_1993_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1979_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1979_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2001_, lean_object* v_x_2002_, lean_object* v_c_u2081_2003_, lean_object* v_todo_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2001_, v_x_2002_, v_c_u2081_2003_, v_todo_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_todo_2004_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2018_, lean_object* v_as_2019_, size_t v_sz_2020_, size_t v_i_2021_, lean_object* v_b_2022_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_usize_dec_lt(v_i_2021_, v_sz_2020_);
if (v___x_2023_ == 0)
{
return v_b_2022_;
}
else
{
lean_object* v_snd_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2057_; 
v_snd_2024_ = lean_ctor_get(v_b_2022_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_2022_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_b_2022_, 0);
lean_dec(v_unused_2058_);
v___x_2026_ = v_b_2022_;
v_isShared_2027_ = v_isSharedCheck_2057_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snd_2024_);
lean_dec(v_b_2022_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2057_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2056_; 
v_fst_2028_ = lean_ctor_get(v_snd_2024_, 0);
v_snd_2029_ = lean_ctor_get(v_snd_2024_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_2024_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2031_ = v_snd_2024_;
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_snd_2024_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_a_2033_; lean_object* v_p_2034_; lean_object* v___x_2035_; lean_object* v_a_2037_; lean_object* v_b_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_a_2033_ = lean_array_uget_borrowed(v_as_2019_, v_i_2021_);
v_p_2034_ = lean_ctor_get(v_a_2033_, 0);
v___x_2035_ = lean_box(0);
v_b_2044_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2034_, v_x_2018_);
v___x_2045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2046_ = lean_int_dec_eq(v_b_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2048_; 
lean_inc(v_a_2033_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v_a_2033_);
lean_ctor_set(v___x_2026_, 0, v_b_2044_);
v___x_2048_ = v___x_2026_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_b_2044_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_a_2033_);
v___x_2048_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v_todo_2049_; lean_object* v___x_2050_; 
v_todo_2049_ = lean_array_push(v_snd_2029_, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_fst_2028_);
lean_ctor_set(v___x_2050_, 1, v_todo_2049_);
v_a_2037_ = v___x_2050_;
goto v___jp_2036_;
}
}
else
{
lean_object* v_cs_x27_2052_; lean_object* v___x_2054_; 
lean_dec(v_b_2044_);
lean_inc(v_a_2033_);
v_cs_x27_2052_ = l_Lean_PersistentArray_push___redArg(v_fst_2028_, v_a_2033_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v_snd_2029_);
lean_ctor_set(v___x_2026_, 0, v_cs_x27_2052_);
v___x_2054_ = v___x_2026_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_cs_x27_2052_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_snd_2029_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v_a_2037_ = v___x_2054_;
goto v___jp_2036_;
}
}
v___jp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_a_2037_);
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2039_ = v___x_2031_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2037_);
v___x_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
size_t v___x_2040_; size_t v___x_2041_; 
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2021_, v___x_2040_);
v_i_2021_ = v___x_2041_;
v_b_2022_ = v___x_2039_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2059_, lean_object* v_as_2060_, lean_object* v_sz_2061_, lean_object* v_i_2062_, lean_object* v_b_2063_){
_start:
{
size_t v_sz_boxed_2064_; size_t v_i_boxed_2065_; lean_object* v_res_2066_; 
v_sz_boxed_2064_ = lean_unbox_usize(v_sz_2061_);
lean_dec(v_sz_2061_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2059_, v_as_2060_, v_sz_boxed_2064_, v_i_boxed_2065_, v_b_2063_);
lean_dec_ref(v_as_2060_);
lean_dec(v_x_2059_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2067_, lean_object* v_as_2068_, size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_b_2071_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
if (v___x_2072_ == 0)
{
return v_b_2071_;
}
else
{
lean_object* v_snd_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2106_; 
v_snd_2073_ = lean_ctor_get(v_b_2071_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_b_2071_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_b_2071_, 0);
lean_dec(v_unused_2107_);
v___x_2075_ = v_b_2071_;
v_isShared_2076_ = v_isSharedCheck_2106_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2073_);
lean_dec(v_b_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2106_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_fst_2077_; lean_object* v_snd_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2105_; 
v_fst_2077_ = lean_ctor_get(v_snd_2073_, 0);
v_snd_2078_ = lean_ctor_get(v_snd_2073_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_snd_2073_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2080_ = v_snd_2073_;
v_isShared_2081_ = v_isSharedCheck_2105_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_snd_2078_);
lean_inc(v_fst_2077_);
lean_dec(v_snd_2073_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2105_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_a_2082_; lean_object* v_p_2083_; lean_object* v___x_2084_; lean_object* v_a_2086_; lean_object* v_b_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_a_2082_ = lean_array_uget_borrowed(v_as_2068_, v_i_2070_);
v_p_2083_ = lean_ctor_get(v_a_2082_, 0);
v___x_2084_ = lean_box(0);
v_b_2093_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2083_, v_x_2067_);
v___x_2094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2095_ = lean_int_dec_eq(v_b_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2097_; 
lean_inc(v_a_2082_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v_a_2082_);
lean_ctor_set(v___x_2075_, 0, v_b_2093_);
v___x_2097_ = v___x_2075_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_b_2093_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_a_2082_);
v___x_2097_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v_todo_2098_; lean_object* v___x_2099_; 
v_todo_2098_ = lean_array_push(v_snd_2078_, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_fst_2077_);
lean_ctor_set(v___x_2099_, 1, v_todo_2098_);
v_a_2086_ = v___x_2099_;
goto v___jp_2085_;
}
}
else
{
lean_object* v_cs_x27_2101_; lean_object* v___x_2103_; 
lean_dec(v_b_2093_);
lean_inc(v_a_2082_);
v_cs_x27_2101_ = l_Lean_PersistentArray_push___redArg(v_fst_2077_, v_a_2082_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v_snd_2078_);
lean_ctor_set(v___x_2075_, 0, v_cs_x27_2101_);
v___x_2103_ = v___x_2075_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_cs_x27_2101_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_snd_2078_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v_a_2086_ = v___x_2103_;
goto v___jp_2085_;
}
}
v___jp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v_a_2086_);
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2088_ = v___x_2080_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_a_2086_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2070_, v___x_2089_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2067_, v_as_2068_, v_sz_2069_, v___x_2090_, v___x_2088_);
return v___x_2091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2108_, lean_object* v_as_2109_, lean_object* v_sz_2110_, lean_object* v_i_2111_, lean_object* v_b_2112_){
_start:
{
size_t v_sz_boxed_2113_; size_t v_i_boxed_2114_; lean_object* v_res_2115_; 
v_sz_boxed_2113_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2108_, v_as_2109_, v_sz_boxed_2113_, v_i_boxed_2114_, v_b_2112_);
lean_dec_ref(v_as_2109_);
lean_dec(v_x_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2116_, lean_object* v_as_2117_, size_t v_sz_2118_, size_t v_i_2119_, lean_object* v_b_2120_){
_start:
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_usize_dec_lt(v_i_2119_, v_sz_2118_);
if (v___x_2121_ == 0)
{
return v_b_2120_;
}
else
{
lean_object* v_snd_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2155_; 
v_snd_2122_ = lean_ctor_get(v_b_2120_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_b_2120_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_b_2120_, 0);
lean_dec(v_unused_2156_);
v___x_2124_ = v_b_2120_;
v_isShared_2125_ = v_isSharedCheck_2155_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snd_2122_);
lean_dec(v_b_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2155_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_fst_2126_; lean_object* v_snd_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2154_; 
v_fst_2126_ = lean_ctor_get(v_snd_2122_, 0);
v_snd_2127_ = lean_ctor_get(v_snd_2122_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_snd_2122_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2129_ = v_snd_2122_;
v_isShared_2130_ = v_isSharedCheck_2154_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_snd_2127_);
lean_inc(v_fst_2126_);
lean_dec(v_snd_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2154_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_a_2131_; lean_object* v_p_2132_; lean_object* v___x_2133_; lean_object* v_a_2135_; lean_object* v_b_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_a_2131_ = lean_array_uget_borrowed(v_as_2117_, v_i_2119_);
v_p_2132_ = lean_ctor_get(v_a_2131_, 0);
v___x_2133_ = lean_box(0);
v_b_2142_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2132_, v_x_2116_);
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2144_ = lean_int_dec_eq(v_b_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2146_; 
lean_inc(v_a_2131_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_a_2131_);
lean_ctor_set(v___x_2124_, 0, v_b_2142_);
v___x_2146_ = v___x_2124_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_b_2142_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2131_);
v___x_2146_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v_todo_2147_; lean_object* v___x_2148_; 
v_todo_2147_ = lean_array_push(v_snd_2127_, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_fst_2126_);
lean_ctor_set(v___x_2148_, 1, v_todo_2147_);
v_a_2135_ = v___x_2148_;
goto v___jp_2134_;
}
}
else
{
lean_object* v_cs_x27_2150_; lean_object* v___x_2152_; 
lean_dec(v_b_2142_);
lean_inc(v_a_2131_);
v_cs_x27_2150_ = l_Lean_PersistentArray_push___redArg(v_fst_2126_, v_a_2131_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_snd_2127_);
lean_ctor_set(v___x_2124_, 0, v_cs_x27_2150_);
v___x_2152_ = v___x_2124_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_cs_x27_2150_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_snd_2127_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_a_2135_ = v___x_2152_;
goto v___jp_2134_;
}
}
v___jp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_a_2135_);
lean_ctor_set(v___x_2129_, 0, v___x_2133_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2135_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
size_t v___x_2138_; size_t v___x_2139_; 
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = lean_usize_add(v_i_2119_, v___x_2138_);
v_i_2119_ = v___x_2139_;
v_b_2120_ = v___x_2137_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2157_, lean_object* v_as_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_b_2161_){
_start:
{
size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2157_, v_as_2158_, v_sz_boxed_2162_, v_i_boxed_2163_, v_b_2161_);
lean_dec_ref(v_as_2158_);
lean_dec(v_x_2157_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2165_, lean_object* v_as_2166_, size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_b_2169_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2170_ == 0)
{
return v_b_2169_;
}
else
{
lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2204_; 
v_snd_2171_ = lean_ctor_get(v_b_2169_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_b_2169_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v_b_2169_, 0);
lean_dec(v_unused_2205_);
v___x_2173_ = v_b_2169_;
v_isShared_2174_ = v_isSharedCheck_2204_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_dec(v_b_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2204_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2203_; 
v_fst_2175_ = lean_ctor_get(v_snd_2171_, 0);
v_snd_2176_ = lean_ctor_get(v_snd_2171_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_snd_2171_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2178_ = v_snd_2171_;
v_isShared_2179_ = v_isSharedCheck_2203_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_inc(v_fst_2175_);
lean_dec(v_snd_2171_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2203_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_a_2180_; lean_object* v_p_2181_; lean_object* v___x_2182_; lean_object* v_a_2184_; lean_object* v_b_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v_a_2180_ = lean_array_uget_borrowed(v_as_2166_, v_i_2168_);
v_p_2181_ = lean_ctor_get(v_a_2180_, 0);
v___x_2182_ = lean_box(0);
v_b_2191_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2181_, v_x_2165_);
v___x_2192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2193_ = lean_int_dec_eq(v_b_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2195_; 
lean_inc(v_a_2180_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_a_2180_);
lean_ctor_set(v___x_2173_, 0, v_b_2191_);
v___x_2195_ = v___x_2173_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_b_2191_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2180_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v_todo_2196_; lean_object* v___x_2197_; 
v_todo_2196_ = lean_array_push(v_snd_2176_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_fst_2175_);
lean_ctor_set(v___x_2197_, 1, v_todo_2196_);
v_a_2184_ = v___x_2197_;
goto v___jp_2183_;
}
}
else
{
lean_object* v_cs_x27_2199_; lean_object* v___x_2201_; 
lean_dec(v_b_2191_);
lean_inc(v_a_2180_);
v_cs_x27_2199_ = l_Lean_PersistentArray_push___redArg(v_fst_2175_, v_a_2180_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_snd_2176_);
lean_ctor_set(v___x_2173_, 0, v_cs_x27_2199_);
v___x_2201_ = v___x_2173_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_cs_x27_2199_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_snd_2176_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v_a_2184_ = v___x_2201_;
goto v___jp_2183_;
}
}
v___jp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v_a_2184_);
lean_ctor_set(v___x_2178_, 0, v___x_2182_);
v___x_2186_ = v___x_2178_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_a_2184_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_add(v_i_2168_, v___x_2187_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2165_, v_as_2166_, v_sz_2167_, v___x_2188_, v___x_2186_);
return v___x_2189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2206_, lean_object* v_as_2207_, lean_object* v_sz_2208_, lean_object* v_i_2209_, lean_object* v_b_2210_){
_start:
{
size_t v_sz_boxed_2211_; size_t v_i_boxed_2212_; lean_object* v_res_2213_; 
v_sz_boxed_2211_ = lean_unbox_usize(v_sz_2208_);
lean_dec(v_sz_2208_);
v_i_boxed_2212_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2206_, v_as_2207_, v_sz_boxed_2211_, v_i_boxed_2212_, v_b_2210_);
lean_dec_ref(v_as_2207_);
lean_dec(v_x_2206_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2214_, lean_object* v_x_2215_, lean_object* v_n_2216_, lean_object* v_b_2217_){
_start:
{
if (lean_obj_tag(v_n_2216_) == 0)
{
lean_object* v_cs_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; size_t v_sz_2221_; size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v_fst_2224_; 
v_cs_2218_ = lean_ctor_get(v_n_2216_, 0);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v_b_2217_);
v_sz_2221_ = lean_array_size(v_cs_2218_);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2214_, v_x_2215_, v_cs_2218_, v_sz_2221_, v___x_2222_, v___x_2220_);
v_fst_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_fst_2224_);
if (lean_obj_tag(v_fst_2224_) == 0)
{
lean_object* v_snd_2225_; lean_object* v___x_2226_; 
v_snd_2225_ = lean_ctor_get(v___x_2223_, 1);
lean_inc(v_snd_2225_);
lean_dec_ref(v___x_2223_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_snd_2225_);
return v___x_2226_;
}
else
{
lean_object* v_val_2227_; 
lean_dec_ref(v___x_2223_);
v_val_2227_ = lean_ctor_get(v_fst_2224_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v_fst_2224_, 1);
return v_val_2227_;
}
}
else
{
lean_object* v_vs_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_2233_; lean_object* v_fst_2234_; 
v_vs_2228_ = lean_ctor_get(v_n_2216_, 0);
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_b_2217_);
v_sz_2231_ = lean_array_size(v_vs_2228_);
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2215_, v_vs_2228_, v_sz_2231_, v___x_2232_, v___x_2230_);
v_fst_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_fst_2234_);
if (lean_obj_tag(v_fst_2234_) == 0)
{
lean_object* v_snd_2235_; lean_object* v___x_2236_; 
v_snd_2235_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2233_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_snd_2235_);
return v___x_2236_;
}
else
{
lean_object* v_val_2237_; 
lean_dec_ref(v___x_2233_);
v_val_2237_ = lean_ctor_get(v_fst_2234_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v_fst_2234_, 1);
return v_val_2237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2238_, lean_object* v_x_2239_, lean_object* v_as_2240_, size_t v_sz_2241_, size_t v_i_2242_, lean_object* v_b_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_lt(v_i_2242_, v_sz_2241_);
if (v___x_2244_ == 0)
{
return v_b_2243_;
}
else
{
lean_object* v_snd_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2263_; 
v_snd_2245_ = lean_ctor_get(v_b_2243_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_b_2243_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; 
v_unused_2264_ = lean_ctor_get(v_b_2243_, 0);
lean_dec(v_unused_2264_);
v___x_2247_ = v_b_2243_;
v_isShared_2248_ = v_isSharedCheck_2263_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2245_);
lean_dec(v_b_2243_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2263_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_a_2249_; lean_object* v___x_2250_; 
v_a_2249_ = lean_array_uget_borrowed(v_as_2240_, v_i_2242_);
lean_inc(v_snd_2245_);
v___x_2250_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2238_, v_x_2239_, v_a_2249_, v_snd_2245_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2251_);
v___x_2253_ = v___x_2247_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_snd_2245_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec(v_snd_2245_);
v_a_2255_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2250_, 1);
v___x_2256_ = lean_box(0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v_a_2255_);
lean_ctor_set(v___x_2247_, 0, v___x_2256_);
v___x_2258_ = v___x_2247_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_a_2255_);
v___x_2258_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
size_t v___x_2259_; size_t v___x_2260_; 
v___x_2259_ = ((size_t)1ULL);
v___x_2260_ = lean_usize_add(v_i_2242_, v___x_2259_);
v_i_2242_ = v___x_2260_;
v_b_2243_ = v___x_2258_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2265_, lean_object* v_x_2266_, lean_object* v_as_2267_, lean_object* v_sz_2268_, lean_object* v_i_2269_, lean_object* v_b_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2268_);
lean_dec(v_sz_2268_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2265_, v_x_2266_, v_as_2267_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2270_);
lean_dec_ref(v_as_2267_);
lean_dec(v_x_2266_);
lean_dec_ref(v_init_2265_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2274_, lean_object* v_x_2275_, lean_object* v_n_2276_, lean_object* v_b_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2274_, v_x_2275_, v_n_2276_, v_b_2277_);
lean_dec_ref(v_n_2276_);
lean_dec(v_x_2275_);
lean_dec_ref(v_init_2274_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2279_, lean_object* v_t_2280_, lean_object* v_init_2281_){
_start:
{
lean_object* v_root_2282_; lean_object* v_tail_2283_; lean_object* v___x_2284_; 
v_root_2282_ = lean_ctor_get(v_t_2280_, 0);
v_tail_2283_ = lean_ctor_get(v_t_2280_, 1);
lean_inc_ref(v_init_2281_);
v___x_2284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2281_, v_x_2279_, v_root_2282_, v_init_2281_);
lean_dec_ref(v_init_2281_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
return v_a_2285_;
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; size_t v_sz_2289_; size_t v___x_2290_; lean_object* v___x_2291_; lean_object* v_fst_2292_; 
v_a_2286_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v_a_2286_);
v_sz_2289_ = lean_array_size(v_tail_2283_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2279_, v_tail_2283_, v_sz_2289_, v___x_2290_, v___x_2288_);
v_fst_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_fst_2292_);
if (lean_obj_tag(v_fst_2292_) == 0)
{
lean_object* v_snd_2293_; 
v_snd_2293_ = lean_ctor_get(v___x_2291_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___x_2291_);
return v_snd_2293_;
}
else
{
lean_object* v_val_2294_; 
lean_dec_ref(v___x_2291_);
v_val_2294_ = lean_ctor_get(v_fst_2292_, 0);
lean_inc(v_val_2294_);
lean_dec_ref_known(v_fst_2292_, 1);
return v_val_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2295_, lean_object* v_t_2296_, lean_object* v_init_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2295_, v_t_2296_, v_init_2297_);
lean_dec_ref(v_t_2296_);
lean_dec(v_x_2295_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_unsigned_to_nat(32u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_cs_x27_2307_; 
v___x_2302_ = ((size_t)5ULL);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = lean_unsigned_to_nat(32u);
v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
v___x_2306_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2307_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2307_, 0, v___x_2306_);
lean_ctor_set(v_cs_x27_2307_, 1, v___x_2305_);
lean_ctor_set(v_cs_x27_2307_, 2, v___x_2303_);
lean_ctor_set(v_cs_x27_2307_, 3, v___x_2303_);
lean_ctor_set_usize(v_cs_x27_2307_, 4, v___x_2302_);
return v_cs_x27_2307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2310_; lean_object* v_cs_x27_2311_; lean_object* v___x_2312_; 
v_todo_2310_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2311_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_cs_x27_2311_);
lean_ctor_set(v___x_2312_, 1, v_todo_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2313_, lean_object* v_cs_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_fst_2317_; lean_object* v_snd_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v___x_2315_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2316_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2313_, v_cs_2314_, v___x_2315_);
v_fst_2317_ = lean_ctor_get(v___x_2316_, 0);
v_snd_2318_ = lean_ctor_get(v___x_2316_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2316_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_snd_2318_);
lean_inc(v_fst_2317_);
lean_dec(v___x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_fst_2317_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_snd_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2326_, lean_object* v_cs_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2326_, v_cs_2327_);
lean_dec_ref(v_cs_2327_);
lean_dec(v_x_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2329_, lean_object* v_cs_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2329_, v_cs_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2332_, lean_object* v_cs_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2332_, v_cs_2333_);
lean_dec_ref(v_cs_2333_);
lean_dec(v_x_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2335_, lean_object* v_y_2336_, lean_object* v_fst_2337_, lean_object* v_s_2338_){
_start:
{
lean_object* v_structs_2339_; lean_object* v_typeIdOf_2340_; lean_object* v_exprToStructId_2341_; lean_object* v_exprToStructIdEntries_2342_; lean_object* v_forbiddenNatModules_2343_; lean_object* v_natStructs_2344_; lean_object* v_natTypeIdOf_2345_; lean_object* v_exprToNatStructId_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_structs_2339_ = lean_ctor_get(v_s_2338_, 0);
v_typeIdOf_2340_ = lean_ctor_get(v_s_2338_, 1);
v_exprToStructId_2341_ = lean_ctor_get(v_s_2338_, 2);
v_exprToStructIdEntries_2342_ = lean_ctor_get(v_s_2338_, 3);
v_forbiddenNatModules_2343_ = lean_ctor_get(v_s_2338_, 4);
v_natStructs_2344_ = lean_ctor_get(v_s_2338_, 5);
v_natTypeIdOf_2345_ = lean_ctor_get(v_s_2338_, 6);
v_exprToNatStructId_2346_ = lean_ctor_get(v_s_2338_, 7);
v___x_2347_ = lean_array_get_size(v_structs_2339_);
v___x_2348_ = lean_nat_dec_lt(v_a_2335_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_dec_ref(v_fst_2337_);
return v_s_2338_;
}
else
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2410_; 
lean_inc_ref(v_exprToNatStructId_2346_);
lean_inc_ref(v_natTypeIdOf_2345_);
lean_inc_ref(v_natStructs_2344_);
lean_inc_ref(v_forbiddenNatModules_2343_);
lean_inc_ref(v_exprToStructIdEntries_2342_);
lean_inc_ref(v_exprToStructId_2341_);
lean_inc_ref(v_typeIdOf_2340_);
lean_inc_ref(v_structs_2339_);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_s_2338_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2411_ = lean_ctor_get(v_s_2338_, 7);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_s_2338_, 6);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_s_2338_, 5);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_s_2338_, 4);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2338_, 3);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2338_, 2);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2338_, 1);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2338_, 0);
lean_dec(v_unused_2418_);
v___x_2350_ = v_s_2338_;
v_isShared_2351_ = v_isSharedCheck_2410_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v_s_2338_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2410_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_v_2352_; lean_object* v_id_2353_; lean_object* v_ringId_x3f_2354_; lean_object* v_type_2355_; lean_object* v_u_2356_; lean_object* v_intModuleInst_2357_; lean_object* v_leInst_x3f_2358_; lean_object* v_ltInst_x3f_2359_; lean_object* v_lawfulOrderLTInst_x3f_2360_; lean_object* v_isPreorderInst_x3f_2361_; lean_object* v_orderedAddInst_x3f_2362_; lean_object* v_isLinearInst_x3f_2363_; lean_object* v_noNatDivInst_x3f_2364_; lean_object* v_ringInst_x3f_2365_; lean_object* v_commRingInst_x3f_2366_; lean_object* v_orderedRingInst_x3f_2367_; lean_object* v_fieldInst_x3f_2368_; lean_object* v_charInst_x3f_2369_; lean_object* v_zero_2370_; lean_object* v_ofNatZero_2371_; lean_object* v_one_x3f_2372_; lean_object* v_leFn_x3f_2373_; lean_object* v_ltFn_x3f_2374_; lean_object* v_addFn_2375_; lean_object* v_zsmulFn_2376_; lean_object* v_nsmulFn_2377_; lean_object* v_zsmulFn_x3f_2378_; lean_object* v_nsmulFn_x3f_2379_; lean_object* v_homomulFn_x3f_2380_; lean_object* v_subFn_2381_; lean_object* v_negFn_2382_; lean_object* v_vars_2383_; lean_object* v_varMap_2384_; lean_object* v_lowers_2385_; lean_object* v_uppers_2386_; lean_object* v_diseqs_2387_; lean_object* v_assignment_2388_; uint8_t v_caseSplits_2389_; lean_object* v_conflict_x3f_2390_; lean_object* v_diseqSplits_2391_; lean_object* v_elimEqs_2392_; lean_object* v_elimStack_2393_; lean_object* v_occurs_2394_; lean_object* v_ignored_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2409_; 
v_v_2352_ = lean_array_fget(v_structs_2339_, v_a_2335_);
v_id_2353_ = lean_ctor_get(v_v_2352_, 0);
v_ringId_x3f_2354_ = lean_ctor_get(v_v_2352_, 1);
v_type_2355_ = lean_ctor_get(v_v_2352_, 2);
v_u_2356_ = lean_ctor_get(v_v_2352_, 3);
v_intModuleInst_2357_ = lean_ctor_get(v_v_2352_, 4);
v_leInst_x3f_2358_ = lean_ctor_get(v_v_2352_, 5);
v_ltInst_x3f_2359_ = lean_ctor_get(v_v_2352_, 6);
v_lawfulOrderLTInst_x3f_2360_ = lean_ctor_get(v_v_2352_, 7);
v_isPreorderInst_x3f_2361_ = lean_ctor_get(v_v_2352_, 8);
v_orderedAddInst_x3f_2362_ = lean_ctor_get(v_v_2352_, 9);
v_isLinearInst_x3f_2363_ = lean_ctor_get(v_v_2352_, 10);
v_noNatDivInst_x3f_2364_ = lean_ctor_get(v_v_2352_, 11);
v_ringInst_x3f_2365_ = lean_ctor_get(v_v_2352_, 12);
v_commRingInst_x3f_2366_ = lean_ctor_get(v_v_2352_, 13);
v_orderedRingInst_x3f_2367_ = lean_ctor_get(v_v_2352_, 14);
v_fieldInst_x3f_2368_ = lean_ctor_get(v_v_2352_, 15);
v_charInst_x3f_2369_ = lean_ctor_get(v_v_2352_, 16);
v_zero_2370_ = lean_ctor_get(v_v_2352_, 17);
v_ofNatZero_2371_ = lean_ctor_get(v_v_2352_, 18);
v_one_x3f_2372_ = lean_ctor_get(v_v_2352_, 19);
v_leFn_x3f_2373_ = lean_ctor_get(v_v_2352_, 20);
v_ltFn_x3f_2374_ = lean_ctor_get(v_v_2352_, 21);
v_addFn_2375_ = lean_ctor_get(v_v_2352_, 22);
v_zsmulFn_2376_ = lean_ctor_get(v_v_2352_, 23);
v_nsmulFn_2377_ = lean_ctor_get(v_v_2352_, 24);
v_zsmulFn_x3f_2378_ = lean_ctor_get(v_v_2352_, 25);
v_nsmulFn_x3f_2379_ = lean_ctor_get(v_v_2352_, 26);
v_homomulFn_x3f_2380_ = lean_ctor_get(v_v_2352_, 27);
v_subFn_2381_ = lean_ctor_get(v_v_2352_, 28);
v_negFn_2382_ = lean_ctor_get(v_v_2352_, 29);
v_vars_2383_ = lean_ctor_get(v_v_2352_, 30);
v_varMap_2384_ = lean_ctor_get(v_v_2352_, 31);
v_lowers_2385_ = lean_ctor_get(v_v_2352_, 32);
v_uppers_2386_ = lean_ctor_get(v_v_2352_, 33);
v_diseqs_2387_ = lean_ctor_get(v_v_2352_, 34);
v_assignment_2388_ = lean_ctor_get(v_v_2352_, 35);
v_caseSplits_2389_ = lean_ctor_get_uint8(v_v_2352_, sizeof(void*)*42);
v_conflict_x3f_2390_ = lean_ctor_get(v_v_2352_, 36);
v_diseqSplits_2391_ = lean_ctor_get(v_v_2352_, 37);
v_elimEqs_2392_ = lean_ctor_get(v_v_2352_, 38);
v_elimStack_2393_ = lean_ctor_get(v_v_2352_, 39);
v_occurs_2394_ = lean_ctor_get(v_v_2352_, 40);
v_ignored_2395_ = lean_ctor_get(v_v_2352_, 41);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_v_2352_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2397_ = v_v_2352_;
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_ignored_2395_);
lean_inc(v_occurs_2394_);
lean_inc(v_elimStack_2393_);
lean_inc(v_elimEqs_2392_);
lean_inc(v_diseqSplits_2391_);
lean_inc(v_conflict_x3f_2390_);
lean_inc(v_assignment_2388_);
lean_inc(v_diseqs_2387_);
lean_inc(v_uppers_2386_);
lean_inc(v_lowers_2385_);
lean_inc(v_varMap_2384_);
lean_inc(v_vars_2383_);
lean_inc(v_negFn_2382_);
lean_inc(v_subFn_2381_);
lean_inc(v_homomulFn_x3f_2380_);
lean_inc(v_nsmulFn_x3f_2379_);
lean_inc(v_zsmulFn_x3f_2378_);
lean_inc(v_nsmulFn_2377_);
lean_inc(v_zsmulFn_2376_);
lean_inc(v_addFn_2375_);
lean_inc(v_ltFn_x3f_2374_);
lean_inc(v_leFn_x3f_2373_);
lean_inc(v_one_x3f_2372_);
lean_inc(v_ofNatZero_2371_);
lean_inc(v_zero_2370_);
lean_inc(v_charInst_x3f_2369_);
lean_inc(v_fieldInst_x3f_2368_);
lean_inc(v_orderedRingInst_x3f_2367_);
lean_inc(v_commRingInst_x3f_2366_);
lean_inc(v_ringInst_x3f_2365_);
lean_inc(v_noNatDivInst_x3f_2364_);
lean_inc(v_isLinearInst_x3f_2363_);
lean_inc(v_orderedAddInst_x3f_2362_);
lean_inc(v_isPreorderInst_x3f_2361_);
lean_inc(v_lawfulOrderLTInst_x3f_2360_);
lean_inc(v_ltInst_x3f_2359_);
lean_inc(v_leInst_x3f_2358_);
lean_inc(v_intModuleInst_2357_);
lean_inc(v_u_2356_);
lean_inc(v_type_2355_);
lean_inc(v_ringId_x3f_2354_);
lean_inc(v_id_2353_);
lean_dec(v_v_2352_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_xs_x27_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2399_ = lean_box(0);
v_xs_x27_2400_ = lean_array_fset(v_structs_2339_, v_a_2335_, v___x_2399_);
v___x_2401_ = l_Lean_PersistentArray_set___redArg(v_lowers_2385_, v_y_2336_, v_fst_2337_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 32, v___x_2401_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_id_2353_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_ringId_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_type_2355_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v_u_2356_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_intModuleInst_2357_);
lean_ctor_set(v_reuseFailAlloc_2408_, 5, v_leInst_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2408_, 6, v_ltInst_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2408_, 7, v_lawfulOrderLTInst_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2408_, 8, v_isPreorderInst_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2408_, 9, v_orderedAddInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2408_, 10, v_isLinearInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2408_, 11, v_noNatDivInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2408_, 12, v_ringInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2408_, 13, v_commRingInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2408_, 14, v_orderedRingInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2408_, 15, v_fieldInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2408_, 16, v_charInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2408_, 17, v_zero_2370_);
lean_ctor_set(v_reuseFailAlloc_2408_, 18, v_ofNatZero_2371_);
lean_ctor_set(v_reuseFailAlloc_2408_, 19, v_one_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2408_, 20, v_leFn_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2408_, 21, v_ltFn_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2408_, 22, v_addFn_2375_);
lean_ctor_set(v_reuseFailAlloc_2408_, 23, v_zsmulFn_2376_);
lean_ctor_set(v_reuseFailAlloc_2408_, 24, v_nsmulFn_2377_);
lean_ctor_set(v_reuseFailAlloc_2408_, 25, v_zsmulFn_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2408_, 26, v_nsmulFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2408_, 27, v_homomulFn_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2408_, 28, v_subFn_2381_);
lean_ctor_set(v_reuseFailAlloc_2408_, 29, v_negFn_2382_);
lean_ctor_set(v_reuseFailAlloc_2408_, 30, v_vars_2383_);
lean_ctor_set(v_reuseFailAlloc_2408_, 31, v_varMap_2384_);
lean_ctor_set(v_reuseFailAlloc_2408_, 32, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2408_, 33, v_uppers_2386_);
lean_ctor_set(v_reuseFailAlloc_2408_, 34, v_diseqs_2387_);
lean_ctor_set(v_reuseFailAlloc_2408_, 35, v_assignment_2388_);
lean_ctor_set(v_reuseFailAlloc_2408_, 36, v_conflict_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2408_, 37, v_diseqSplits_2391_);
lean_ctor_set(v_reuseFailAlloc_2408_, 38, v_elimEqs_2392_);
lean_ctor_set(v_reuseFailAlloc_2408_, 39, v_elimStack_2393_);
lean_ctor_set(v_reuseFailAlloc_2408_, 40, v_occurs_2394_);
lean_ctor_set(v_reuseFailAlloc_2408_, 41, v_ignored_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2408_, sizeof(void*)*42, v_caseSplits_2389_);
v___x_2403_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = lean_array_fset(v_xs_x27_2400_, v_a_2335_, v___x_2403_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2404_);
v___x_2406_ = v___x_2350_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_typeIdOf_2340_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_exprToStructId_2341_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_exprToStructIdEntries_2342_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_forbiddenNatModules_2343_);
lean_ctor_set(v_reuseFailAlloc_2407_, 5, v_natStructs_2344_);
lean_ctor_set(v_reuseFailAlloc_2407_, 6, v_natTypeIdOf_2345_);
lean_ctor_set(v_reuseFailAlloc_2407_, 7, v_exprToNatStructId_2346_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2419_, lean_object* v_y_2420_, lean_object* v_fst_2421_, lean_object* v_s_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2419_, v_y_2420_, v_fst_2421_, v_s_2422_);
lean_dec(v_y_2420_);
lean_dec(v_a_2419_);
return v_res_2423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2425_, lean_object* v_x_2426_, lean_object* v_c_2427_, lean_object* v_y_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2442_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2476_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2476_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2476_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_unbox(v_a_2443_);
lean_dec(v_a_2443_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_del_object(v___x_2445_);
v___x_2448_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___y_2451_; lean_object* v_lowers_2459_; lean_object* v_size_2460_; uint8_t v___x_2461_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v_lowers_2459_ = lean_ctor_get(v_a_2449_, 32);
lean_inc_ref(v_lowers_2459_);
lean_dec(v_a_2449_);
v_size_2460_ = lean_ctor_get(v_lowers_2459_, 2);
v___x_2461_ = lean_nat_dec_lt(v_y_2428_, v_size_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref(v_lowers_2459_);
v___x_2462_ = l_outOfBounds___redArg(v___x_2441_);
v___y_2451_ = v___x_2462_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2441_, v_lowers_2459_, v_y_2428_);
lean_dec_ref(v_lowers_2459_);
v___y_2451_ = v___x_2463_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2452_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2426_, v___y_2451_);
lean_dec_ref(v___y_2451_);
v_fst_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_fst_2453_);
v_snd_2454_ = lean_ctor_get(v___x_2452_, 1);
lean_inc(v_snd_2454_);
lean_dec_ref(v___x_2452_);
lean_inc(v_a_2429_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2455_, 0, v_a_2429_);
lean_closure_set(v___f_2455_, 1, v_y_2428_);
lean_closure_set(v___f_2455_, 2, v_fst_2453_);
v___x_2456_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2456_, v___f_2455_, v_a_2430_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref_known(v___x_2457_, 1);
v___x_2458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2425_, v_x_2426_, v_c_2427_, v_snd_2454_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_snd_2454_);
return v___x_2458_;
}
else
{
lean_dec(v_snd_2454_);
lean_dec_ref(v_c_2427_);
lean_dec(v_x_2426_);
lean_dec(v_a_2425_);
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_y_2428_);
lean_dec_ref(v_c_2427_);
lean_dec(v_x_2426_);
lean_dec(v_a_2425_);
v_a_2464_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2448_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2448_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_y_2428_);
lean_dec_ref(v_c_2427_);
lean_dec(v_x_2426_);
lean_dec(v_a_2425_);
v___x_2472_ = lean_box(0);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2472_);
v___x_2474_ = v___x_2445_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
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
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_y_2428_);
lean_dec_ref(v_c_2427_);
lean_dec(v_x_2426_);
lean_dec(v_a_2425_);
v_a_2477_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2442_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2442_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2485_, lean_object* v_x_2486_, lean_object* v_c_2487_, lean_object* v_y_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2485_, v_x_2486_, v_c_2487_, v_y_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec(v_a_2489_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2502_, lean_object* v_y_2503_, lean_object* v_fst_2504_, lean_object* v_s_2505_){
_start:
{
lean_object* v_structs_2506_; lean_object* v_typeIdOf_2507_; lean_object* v_exprToStructId_2508_; lean_object* v_exprToStructIdEntries_2509_; lean_object* v_forbiddenNatModules_2510_; lean_object* v_natStructs_2511_; lean_object* v_natTypeIdOf_2512_; lean_object* v_exprToNatStructId_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_structs_2506_ = lean_ctor_get(v_s_2505_, 0);
v_typeIdOf_2507_ = lean_ctor_get(v_s_2505_, 1);
v_exprToStructId_2508_ = lean_ctor_get(v_s_2505_, 2);
v_exprToStructIdEntries_2509_ = lean_ctor_get(v_s_2505_, 3);
v_forbiddenNatModules_2510_ = lean_ctor_get(v_s_2505_, 4);
v_natStructs_2511_ = lean_ctor_get(v_s_2505_, 5);
v_natTypeIdOf_2512_ = lean_ctor_get(v_s_2505_, 6);
v_exprToNatStructId_2513_ = lean_ctor_get(v_s_2505_, 7);
v___x_2514_ = lean_array_get_size(v_structs_2506_);
v___x_2515_ = lean_nat_dec_lt(v_a_2502_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v_fst_2504_);
return v_s_2505_;
}
else
{
lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2577_; 
lean_inc_ref(v_exprToNatStructId_2513_);
lean_inc_ref(v_natTypeIdOf_2512_);
lean_inc_ref(v_natStructs_2511_);
lean_inc_ref(v_forbiddenNatModules_2510_);
lean_inc_ref(v_exprToStructIdEntries_2509_);
lean_inc_ref(v_exprToStructId_2508_);
lean_inc_ref(v_typeIdOf_2507_);
lean_inc_ref(v_structs_2506_);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_s_2505_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; lean_object* v_unused_2579_; lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2578_ = lean_ctor_get(v_s_2505_, 7);
lean_dec(v_unused_2578_);
v_unused_2579_ = lean_ctor_get(v_s_2505_, 6);
lean_dec(v_unused_2579_);
v_unused_2580_ = lean_ctor_get(v_s_2505_, 5);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_s_2505_, 4);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_s_2505_, 3);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_s_2505_, 2);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_s_2505_, 1);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2505_, 0);
lean_dec(v_unused_2585_);
v___x_2517_ = v_s_2505_;
v_isShared_2518_ = v_isSharedCheck_2577_;
goto v_resetjp_2516_;
}
else
{
lean_dec(v_s_2505_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2577_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_v_2519_; lean_object* v_id_2520_; lean_object* v_ringId_x3f_2521_; lean_object* v_type_2522_; lean_object* v_u_2523_; lean_object* v_intModuleInst_2524_; lean_object* v_leInst_x3f_2525_; lean_object* v_ltInst_x3f_2526_; lean_object* v_lawfulOrderLTInst_x3f_2527_; lean_object* v_isPreorderInst_x3f_2528_; lean_object* v_orderedAddInst_x3f_2529_; lean_object* v_isLinearInst_x3f_2530_; lean_object* v_noNatDivInst_x3f_2531_; lean_object* v_ringInst_x3f_2532_; lean_object* v_commRingInst_x3f_2533_; lean_object* v_orderedRingInst_x3f_2534_; lean_object* v_fieldInst_x3f_2535_; lean_object* v_charInst_x3f_2536_; lean_object* v_zero_2537_; lean_object* v_ofNatZero_2538_; lean_object* v_one_x3f_2539_; lean_object* v_leFn_x3f_2540_; lean_object* v_ltFn_x3f_2541_; lean_object* v_addFn_2542_; lean_object* v_zsmulFn_2543_; lean_object* v_nsmulFn_2544_; lean_object* v_zsmulFn_x3f_2545_; lean_object* v_nsmulFn_x3f_2546_; lean_object* v_homomulFn_x3f_2547_; lean_object* v_subFn_2548_; lean_object* v_negFn_2549_; lean_object* v_vars_2550_; lean_object* v_varMap_2551_; lean_object* v_lowers_2552_; lean_object* v_uppers_2553_; lean_object* v_diseqs_2554_; lean_object* v_assignment_2555_; uint8_t v_caseSplits_2556_; lean_object* v_conflict_x3f_2557_; lean_object* v_diseqSplits_2558_; lean_object* v_elimEqs_2559_; lean_object* v_elimStack_2560_; lean_object* v_occurs_2561_; lean_object* v_ignored_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2576_; 
v_v_2519_ = lean_array_fget(v_structs_2506_, v_a_2502_);
v_id_2520_ = lean_ctor_get(v_v_2519_, 0);
v_ringId_x3f_2521_ = lean_ctor_get(v_v_2519_, 1);
v_type_2522_ = lean_ctor_get(v_v_2519_, 2);
v_u_2523_ = lean_ctor_get(v_v_2519_, 3);
v_intModuleInst_2524_ = lean_ctor_get(v_v_2519_, 4);
v_leInst_x3f_2525_ = lean_ctor_get(v_v_2519_, 5);
v_ltInst_x3f_2526_ = lean_ctor_get(v_v_2519_, 6);
v_lawfulOrderLTInst_x3f_2527_ = lean_ctor_get(v_v_2519_, 7);
v_isPreorderInst_x3f_2528_ = lean_ctor_get(v_v_2519_, 8);
v_orderedAddInst_x3f_2529_ = lean_ctor_get(v_v_2519_, 9);
v_isLinearInst_x3f_2530_ = lean_ctor_get(v_v_2519_, 10);
v_noNatDivInst_x3f_2531_ = lean_ctor_get(v_v_2519_, 11);
v_ringInst_x3f_2532_ = lean_ctor_get(v_v_2519_, 12);
v_commRingInst_x3f_2533_ = lean_ctor_get(v_v_2519_, 13);
v_orderedRingInst_x3f_2534_ = lean_ctor_get(v_v_2519_, 14);
v_fieldInst_x3f_2535_ = lean_ctor_get(v_v_2519_, 15);
v_charInst_x3f_2536_ = lean_ctor_get(v_v_2519_, 16);
v_zero_2537_ = lean_ctor_get(v_v_2519_, 17);
v_ofNatZero_2538_ = lean_ctor_get(v_v_2519_, 18);
v_one_x3f_2539_ = lean_ctor_get(v_v_2519_, 19);
v_leFn_x3f_2540_ = lean_ctor_get(v_v_2519_, 20);
v_ltFn_x3f_2541_ = lean_ctor_get(v_v_2519_, 21);
v_addFn_2542_ = lean_ctor_get(v_v_2519_, 22);
v_zsmulFn_2543_ = lean_ctor_get(v_v_2519_, 23);
v_nsmulFn_2544_ = lean_ctor_get(v_v_2519_, 24);
v_zsmulFn_x3f_2545_ = lean_ctor_get(v_v_2519_, 25);
v_nsmulFn_x3f_2546_ = lean_ctor_get(v_v_2519_, 26);
v_homomulFn_x3f_2547_ = lean_ctor_get(v_v_2519_, 27);
v_subFn_2548_ = lean_ctor_get(v_v_2519_, 28);
v_negFn_2549_ = lean_ctor_get(v_v_2519_, 29);
v_vars_2550_ = lean_ctor_get(v_v_2519_, 30);
v_varMap_2551_ = lean_ctor_get(v_v_2519_, 31);
v_lowers_2552_ = lean_ctor_get(v_v_2519_, 32);
v_uppers_2553_ = lean_ctor_get(v_v_2519_, 33);
v_diseqs_2554_ = lean_ctor_get(v_v_2519_, 34);
v_assignment_2555_ = lean_ctor_get(v_v_2519_, 35);
v_caseSplits_2556_ = lean_ctor_get_uint8(v_v_2519_, sizeof(void*)*42);
v_conflict_x3f_2557_ = lean_ctor_get(v_v_2519_, 36);
v_diseqSplits_2558_ = lean_ctor_get(v_v_2519_, 37);
v_elimEqs_2559_ = lean_ctor_get(v_v_2519_, 38);
v_elimStack_2560_ = lean_ctor_get(v_v_2519_, 39);
v_occurs_2561_ = lean_ctor_get(v_v_2519_, 40);
v_ignored_2562_ = lean_ctor_get(v_v_2519_, 41);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_v_2519_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2564_ = v_v_2519_;
v_isShared_2565_ = v_isSharedCheck_2576_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_ignored_2562_);
lean_inc(v_occurs_2561_);
lean_inc(v_elimStack_2560_);
lean_inc(v_elimEqs_2559_);
lean_inc(v_diseqSplits_2558_);
lean_inc(v_conflict_x3f_2557_);
lean_inc(v_assignment_2555_);
lean_inc(v_diseqs_2554_);
lean_inc(v_uppers_2553_);
lean_inc(v_lowers_2552_);
lean_inc(v_varMap_2551_);
lean_inc(v_vars_2550_);
lean_inc(v_negFn_2549_);
lean_inc(v_subFn_2548_);
lean_inc(v_homomulFn_x3f_2547_);
lean_inc(v_nsmulFn_x3f_2546_);
lean_inc(v_zsmulFn_x3f_2545_);
lean_inc(v_nsmulFn_2544_);
lean_inc(v_zsmulFn_2543_);
lean_inc(v_addFn_2542_);
lean_inc(v_ltFn_x3f_2541_);
lean_inc(v_leFn_x3f_2540_);
lean_inc(v_one_x3f_2539_);
lean_inc(v_ofNatZero_2538_);
lean_inc(v_zero_2537_);
lean_inc(v_charInst_x3f_2536_);
lean_inc(v_fieldInst_x3f_2535_);
lean_inc(v_orderedRingInst_x3f_2534_);
lean_inc(v_commRingInst_x3f_2533_);
lean_inc(v_ringInst_x3f_2532_);
lean_inc(v_noNatDivInst_x3f_2531_);
lean_inc(v_isLinearInst_x3f_2530_);
lean_inc(v_orderedAddInst_x3f_2529_);
lean_inc(v_isPreorderInst_x3f_2528_);
lean_inc(v_lawfulOrderLTInst_x3f_2527_);
lean_inc(v_ltInst_x3f_2526_);
lean_inc(v_leInst_x3f_2525_);
lean_inc(v_intModuleInst_2524_);
lean_inc(v_u_2523_);
lean_inc(v_type_2522_);
lean_inc(v_ringId_x3f_2521_);
lean_inc(v_id_2520_);
lean_dec(v_v_2519_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2576_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v_xs_x27_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2566_ = lean_box(0);
v_xs_x27_2567_ = lean_array_fset(v_structs_2506_, v_a_2502_, v___x_2566_);
v___x_2568_ = l_Lean_PersistentArray_set___redArg(v_uppers_2553_, v_y_2503_, v_fst_2504_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 33, v___x_2568_);
v___x_2570_ = v___x_2564_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_id_2520_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_ringId_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_type_2522_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_u_2523_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_intModuleInst_2524_);
lean_ctor_set(v_reuseFailAlloc_2575_, 5, v_leInst_x3f_2525_);
lean_ctor_set(v_reuseFailAlloc_2575_, 6, v_ltInst_x3f_2526_);
lean_ctor_set(v_reuseFailAlloc_2575_, 7, v_lawfulOrderLTInst_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2575_, 8, v_isPreorderInst_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2575_, 9, v_orderedAddInst_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2575_, 10, v_isLinearInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2575_, 11, v_noNatDivInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2575_, 12, v_ringInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2575_, 13, v_commRingInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2575_, 14, v_orderedRingInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2575_, 15, v_fieldInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2575_, 16, v_charInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2575_, 17, v_zero_2537_);
lean_ctor_set(v_reuseFailAlloc_2575_, 18, v_ofNatZero_2538_);
lean_ctor_set(v_reuseFailAlloc_2575_, 19, v_one_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2575_, 20, v_leFn_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2575_, 21, v_ltFn_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2575_, 22, v_addFn_2542_);
lean_ctor_set(v_reuseFailAlloc_2575_, 23, v_zsmulFn_2543_);
lean_ctor_set(v_reuseFailAlloc_2575_, 24, v_nsmulFn_2544_);
lean_ctor_set(v_reuseFailAlloc_2575_, 25, v_zsmulFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2575_, 26, v_nsmulFn_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2575_, 27, v_homomulFn_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2575_, 28, v_subFn_2548_);
lean_ctor_set(v_reuseFailAlloc_2575_, 29, v_negFn_2549_);
lean_ctor_set(v_reuseFailAlloc_2575_, 30, v_vars_2550_);
lean_ctor_set(v_reuseFailAlloc_2575_, 31, v_varMap_2551_);
lean_ctor_set(v_reuseFailAlloc_2575_, 32, v_lowers_2552_);
lean_ctor_set(v_reuseFailAlloc_2575_, 33, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 34, v_diseqs_2554_);
lean_ctor_set(v_reuseFailAlloc_2575_, 35, v_assignment_2555_);
lean_ctor_set(v_reuseFailAlloc_2575_, 36, v_conflict_x3f_2557_);
lean_ctor_set(v_reuseFailAlloc_2575_, 37, v_diseqSplits_2558_);
lean_ctor_set(v_reuseFailAlloc_2575_, 38, v_elimEqs_2559_);
lean_ctor_set(v_reuseFailAlloc_2575_, 39, v_elimStack_2560_);
lean_ctor_set(v_reuseFailAlloc_2575_, 40, v_occurs_2561_);
lean_ctor_set(v_reuseFailAlloc_2575_, 41, v_ignored_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2575_, sizeof(void*)*42, v_caseSplits_2556_);
v___x_2570_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = lean_array_fset(v_xs_x27_2567_, v_a_2502_, v___x_2570_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2571_);
v___x_2573_ = v___x_2517_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_typeIdOf_2507_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_exprToStructId_2508_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_exprToStructIdEntries_2509_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_forbiddenNatModules_2510_);
lean_ctor_set(v_reuseFailAlloc_2574_, 5, v_natStructs_2511_);
lean_ctor_set(v_reuseFailAlloc_2574_, 6, v_natTypeIdOf_2512_);
lean_ctor_set(v_reuseFailAlloc_2574_, 7, v_exprToNatStructId_2513_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2586_, lean_object* v_y_2587_, lean_object* v_fst_2588_, lean_object* v_s_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2586_, v_y_2587_, v_fst_2588_, v_s_2589_);
lean_dec(v_y_2587_);
lean_dec(v_a_2586_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2591_, lean_object* v_x_2592_, lean_object* v_c_2593_, lean_object* v_y_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2608_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2642_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2642_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2642_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_unbox(v_a_2609_);
lean_dec(v_a_2609_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_del_object(v___x_2611_);
v___x_2614_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___y_2617_; lean_object* v_uppers_2625_; lean_object* v_size_2626_; uint8_t v___x_2627_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_uppers_2625_ = lean_ctor_get(v_a_2615_, 33);
lean_inc_ref(v_uppers_2625_);
lean_dec(v_a_2615_);
v_size_2626_ = lean_ctor_get(v_uppers_2625_, 2);
v___x_2627_ = lean_nat_dec_lt(v_y_2594_, v_size_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v_uppers_2625_);
v___x_2628_ = l_outOfBounds___redArg(v___x_2607_);
v___y_2617_ = v___x_2628_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2607_, v_uppers_2625_, v_y_2594_);
lean_dec_ref(v_uppers_2625_);
v___y_2617_ = v___x_2629_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2618_; lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2618_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2592_, v___y_2617_);
lean_dec_ref(v___y_2617_);
v_fst_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_fst_2619_);
v_snd_2620_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_snd_2620_);
lean_dec_ref(v___x_2618_);
lean_inc(v_a_2595_);
v___f_2621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2621_, 0, v_a_2595_);
lean_closure_set(v___f_2621_, 1, v_y_2594_);
lean_closure_set(v___f_2621_, 2, v_fst_2619_);
v___x_2622_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2623_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2622_, v___f_2621_, v_a_2596_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2623_, 1);
v___x_2624_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2591_, v_x_2592_, v_c_2593_, v_snd_2620_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_snd_2620_);
return v___x_2624_;
}
else
{
lean_dec(v_snd_2620_);
lean_dec_ref(v_c_2593_);
lean_dec(v_x_2592_);
lean_dec(v_a_2591_);
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_y_2594_);
lean_dec_ref(v_c_2593_);
lean_dec(v_x_2592_);
lean_dec(v_a_2591_);
v_a_2630_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2614_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2614_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v_y_2594_);
lean_dec_ref(v_c_2593_);
lean_dec(v_x_2592_);
lean_dec(v_a_2591_);
v___x_2638_ = lean_box(0);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2638_);
v___x_2640_ = v___x_2611_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
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
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_y_2594_);
lean_dec_ref(v_c_2593_);
lean_dec(v_x_2592_);
lean_dec(v_a_2591_);
v_a_2643_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2608_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2608_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2651_, lean_object* v_x_2652_, lean_object* v_c_2653_, lean_object* v_y_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2651_, v_x_2652_, v_c_2653_, v_y_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec(v_a_2655_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2668_, lean_object* v_a_2669_, lean_object* v_s_2670_){
_start:
{
lean_object* v_structs_2671_; lean_object* v_typeIdOf_2672_; lean_object* v_exprToStructId_2673_; lean_object* v_exprToStructIdEntries_2674_; lean_object* v_forbiddenNatModules_2675_; lean_object* v_natStructs_2676_; lean_object* v_natTypeIdOf_2677_; lean_object* v_exprToNatStructId_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_structs_2671_ = lean_ctor_get(v_s_2670_, 0);
v_typeIdOf_2672_ = lean_ctor_get(v_s_2670_, 1);
v_exprToStructId_2673_ = lean_ctor_get(v_s_2670_, 2);
v_exprToStructIdEntries_2674_ = lean_ctor_get(v_s_2670_, 3);
v_forbiddenNatModules_2675_ = lean_ctor_get(v_s_2670_, 4);
v_natStructs_2676_ = lean_ctor_get(v_s_2670_, 5);
v_natTypeIdOf_2677_ = lean_ctor_get(v_s_2670_, 6);
v_exprToNatStructId_2678_ = lean_ctor_get(v_s_2670_, 7);
v___x_2679_ = lean_array_get_size(v_structs_2671_);
v___x_2680_ = lean_nat_dec_lt(v___y_2668_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v_a_2669_);
return v_s_2670_;
}
else
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2742_; 
lean_inc_ref(v_exprToNatStructId_2678_);
lean_inc_ref(v_natTypeIdOf_2677_);
lean_inc_ref(v_natStructs_2676_);
lean_inc_ref(v_forbiddenNatModules_2675_);
lean_inc_ref(v_exprToStructIdEntries_2674_);
lean_inc_ref(v_exprToStructId_2673_);
lean_inc_ref(v_typeIdOf_2672_);
lean_inc_ref(v_structs_2671_);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_s_2670_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; lean_object* v_unused_2744_; lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; 
v_unused_2743_ = lean_ctor_get(v_s_2670_, 7);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_s_2670_, 6);
lean_dec(v_unused_2744_);
v_unused_2745_ = lean_ctor_get(v_s_2670_, 5);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_s_2670_, 4);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_s_2670_, 3);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2670_, 2);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2670_, 1);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2670_, 0);
lean_dec(v_unused_2750_);
v___x_2682_ = v_s_2670_;
v_isShared_2683_ = v_isSharedCheck_2742_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v_s_2670_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2742_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_v_2684_; lean_object* v_id_2685_; lean_object* v_ringId_x3f_2686_; lean_object* v_type_2687_; lean_object* v_u_2688_; lean_object* v_intModuleInst_2689_; lean_object* v_leInst_x3f_2690_; lean_object* v_ltInst_x3f_2691_; lean_object* v_lawfulOrderLTInst_x3f_2692_; lean_object* v_isPreorderInst_x3f_2693_; lean_object* v_orderedAddInst_x3f_2694_; lean_object* v_isLinearInst_x3f_2695_; lean_object* v_noNatDivInst_x3f_2696_; lean_object* v_ringInst_x3f_2697_; lean_object* v_commRingInst_x3f_2698_; lean_object* v_orderedRingInst_x3f_2699_; lean_object* v_fieldInst_x3f_2700_; lean_object* v_charInst_x3f_2701_; lean_object* v_zero_2702_; lean_object* v_ofNatZero_2703_; lean_object* v_one_x3f_2704_; lean_object* v_leFn_x3f_2705_; lean_object* v_ltFn_x3f_2706_; lean_object* v_addFn_2707_; lean_object* v_zsmulFn_2708_; lean_object* v_nsmulFn_2709_; lean_object* v_zsmulFn_x3f_2710_; lean_object* v_nsmulFn_x3f_2711_; lean_object* v_homomulFn_x3f_2712_; lean_object* v_subFn_2713_; lean_object* v_negFn_2714_; lean_object* v_vars_2715_; lean_object* v_varMap_2716_; lean_object* v_lowers_2717_; lean_object* v_uppers_2718_; lean_object* v_diseqs_2719_; lean_object* v_assignment_2720_; uint8_t v_caseSplits_2721_; lean_object* v_conflict_x3f_2722_; lean_object* v_diseqSplits_2723_; lean_object* v_elimEqs_2724_; lean_object* v_elimStack_2725_; lean_object* v_occurs_2726_; lean_object* v_ignored_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2741_; 
v_v_2684_ = lean_array_fget(v_structs_2671_, v___y_2668_);
v_id_2685_ = lean_ctor_get(v_v_2684_, 0);
v_ringId_x3f_2686_ = lean_ctor_get(v_v_2684_, 1);
v_type_2687_ = lean_ctor_get(v_v_2684_, 2);
v_u_2688_ = lean_ctor_get(v_v_2684_, 3);
v_intModuleInst_2689_ = lean_ctor_get(v_v_2684_, 4);
v_leInst_x3f_2690_ = lean_ctor_get(v_v_2684_, 5);
v_ltInst_x3f_2691_ = lean_ctor_get(v_v_2684_, 6);
v_lawfulOrderLTInst_x3f_2692_ = lean_ctor_get(v_v_2684_, 7);
v_isPreorderInst_x3f_2693_ = lean_ctor_get(v_v_2684_, 8);
v_orderedAddInst_x3f_2694_ = lean_ctor_get(v_v_2684_, 9);
v_isLinearInst_x3f_2695_ = lean_ctor_get(v_v_2684_, 10);
v_noNatDivInst_x3f_2696_ = lean_ctor_get(v_v_2684_, 11);
v_ringInst_x3f_2697_ = lean_ctor_get(v_v_2684_, 12);
v_commRingInst_x3f_2698_ = lean_ctor_get(v_v_2684_, 13);
v_orderedRingInst_x3f_2699_ = lean_ctor_get(v_v_2684_, 14);
v_fieldInst_x3f_2700_ = lean_ctor_get(v_v_2684_, 15);
v_charInst_x3f_2701_ = lean_ctor_get(v_v_2684_, 16);
v_zero_2702_ = lean_ctor_get(v_v_2684_, 17);
v_ofNatZero_2703_ = lean_ctor_get(v_v_2684_, 18);
v_one_x3f_2704_ = lean_ctor_get(v_v_2684_, 19);
v_leFn_x3f_2705_ = lean_ctor_get(v_v_2684_, 20);
v_ltFn_x3f_2706_ = lean_ctor_get(v_v_2684_, 21);
v_addFn_2707_ = lean_ctor_get(v_v_2684_, 22);
v_zsmulFn_2708_ = lean_ctor_get(v_v_2684_, 23);
v_nsmulFn_2709_ = lean_ctor_get(v_v_2684_, 24);
v_zsmulFn_x3f_2710_ = lean_ctor_get(v_v_2684_, 25);
v_nsmulFn_x3f_2711_ = lean_ctor_get(v_v_2684_, 26);
v_homomulFn_x3f_2712_ = lean_ctor_get(v_v_2684_, 27);
v_subFn_2713_ = lean_ctor_get(v_v_2684_, 28);
v_negFn_2714_ = lean_ctor_get(v_v_2684_, 29);
v_vars_2715_ = lean_ctor_get(v_v_2684_, 30);
v_varMap_2716_ = lean_ctor_get(v_v_2684_, 31);
v_lowers_2717_ = lean_ctor_get(v_v_2684_, 32);
v_uppers_2718_ = lean_ctor_get(v_v_2684_, 33);
v_diseqs_2719_ = lean_ctor_get(v_v_2684_, 34);
v_assignment_2720_ = lean_ctor_get(v_v_2684_, 35);
v_caseSplits_2721_ = lean_ctor_get_uint8(v_v_2684_, sizeof(void*)*42);
v_conflict_x3f_2722_ = lean_ctor_get(v_v_2684_, 36);
v_diseqSplits_2723_ = lean_ctor_get(v_v_2684_, 37);
v_elimEqs_2724_ = lean_ctor_get(v_v_2684_, 38);
v_elimStack_2725_ = lean_ctor_get(v_v_2684_, 39);
v_occurs_2726_ = lean_ctor_get(v_v_2684_, 40);
v_ignored_2727_ = lean_ctor_get(v_v_2684_, 41);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_v_2684_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2729_ = v_v_2684_;
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_ignored_2727_);
lean_inc(v_occurs_2726_);
lean_inc(v_elimStack_2725_);
lean_inc(v_elimEqs_2724_);
lean_inc(v_diseqSplits_2723_);
lean_inc(v_conflict_x3f_2722_);
lean_inc(v_assignment_2720_);
lean_inc(v_diseqs_2719_);
lean_inc(v_uppers_2718_);
lean_inc(v_lowers_2717_);
lean_inc(v_varMap_2716_);
lean_inc(v_vars_2715_);
lean_inc(v_negFn_2714_);
lean_inc(v_subFn_2713_);
lean_inc(v_homomulFn_x3f_2712_);
lean_inc(v_nsmulFn_x3f_2711_);
lean_inc(v_zsmulFn_x3f_2710_);
lean_inc(v_nsmulFn_2709_);
lean_inc(v_zsmulFn_2708_);
lean_inc(v_addFn_2707_);
lean_inc(v_ltFn_x3f_2706_);
lean_inc(v_leFn_x3f_2705_);
lean_inc(v_one_x3f_2704_);
lean_inc(v_ofNatZero_2703_);
lean_inc(v_zero_2702_);
lean_inc(v_charInst_x3f_2701_);
lean_inc(v_fieldInst_x3f_2700_);
lean_inc(v_orderedRingInst_x3f_2699_);
lean_inc(v_commRingInst_x3f_2698_);
lean_inc(v_ringInst_x3f_2697_);
lean_inc(v_noNatDivInst_x3f_2696_);
lean_inc(v_isLinearInst_x3f_2695_);
lean_inc(v_orderedAddInst_x3f_2694_);
lean_inc(v_isPreorderInst_x3f_2693_);
lean_inc(v_lawfulOrderLTInst_x3f_2692_);
lean_inc(v_ltInst_x3f_2691_);
lean_inc(v_leInst_x3f_2690_);
lean_inc(v_intModuleInst_2689_);
lean_inc(v_u_2688_);
lean_inc(v_type_2687_);
lean_inc(v_ringId_x3f_2686_);
lean_inc(v_id_2685_);
lean_dec(v_v_2684_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v_xs_x27_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2731_ = lean_box(0);
v_xs_x27_2732_ = lean_array_fset(v_structs_2671_, v___y_2668_, v___x_2731_);
v___x_2733_ = l_Lean_PersistentArray_push___redArg(v_ignored_2727_, v_a_2669_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 41, v___x_2733_);
v___x_2735_ = v___x_2729_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_id_2685_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_ringId_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_type_2687_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v_u_2688_);
lean_ctor_set(v_reuseFailAlloc_2740_, 4, v_intModuleInst_2689_);
lean_ctor_set(v_reuseFailAlloc_2740_, 5, v_leInst_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2740_, 6, v_ltInst_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2740_, 7, v_lawfulOrderLTInst_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2740_, 8, v_isPreorderInst_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2740_, 9, v_orderedAddInst_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2740_, 10, v_isLinearInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2740_, 11, v_noNatDivInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2740_, 12, v_ringInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2740_, 13, v_commRingInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2740_, 14, v_orderedRingInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2740_, 15, v_fieldInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2740_, 16, v_charInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2740_, 17, v_zero_2702_);
lean_ctor_set(v_reuseFailAlloc_2740_, 18, v_ofNatZero_2703_);
lean_ctor_set(v_reuseFailAlloc_2740_, 19, v_one_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2740_, 20, v_leFn_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2740_, 21, v_ltFn_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2740_, 22, v_addFn_2707_);
lean_ctor_set(v_reuseFailAlloc_2740_, 23, v_zsmulFn_2708_);
lean_ctor_set(v_reuseFailAlloc_2740_, 24, v_nsmulFn_2709_);
lean_ctor_set(v_reuseFailAlloc_2740_, 25, v_zsmulFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2740_, 26, v_nsmulFn_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2740_, 27, v_homomulFn_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2740_, 28, v_subFn_2713_);
lean_ctor_set(v_reuseFailAlloc_2740_, 29, v_negFn_2714_);
lean_ctor_set(v_reuseFailAlloc_2740_, 30, v_vars_2715_);
lean_ctor_set(v_reuseFailAlloc_2740_, 31, v_varMap_2716_);
lean_ctor_set(v_reuseFailAlloc_2740_, 32, v_lowers_2717_);
lean_ctor_set(v_reuseFailAlloc_2740_, 33, v_uppers_2718_);
lean_ctor_set(v_reuseFailAlloc_2740_, 34, v_diseqs_2719_);
lean_ctor_set(v_reuseFailAlloc_2740_, 35, v_assignment_2720_);
lean_ctor_set(v_reuseFailAlloc_2740_, 36, v_conflict_x3f_2722_);
lean_ctor_set(v_reuseFailAlloc_2740_, 37, v_diseqSplits_2723_);
lean_ctor_set(v_reuseFailAlloc_2740_, 38, v_elimEqs_2724_);
lean_ctor_set(v_reuseFailAlloc_2740_, 39, v_elimStack_2725_);
lean_ctor_set(v_reuseFailAlloc_2740_, 40, v_occurs_2726_);
lean_ctor_set(v_reuseFailAlloc_2740_, 41, v___x_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*42, v_caseSplits_2721_);
v___x_2735_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_array_fset(v_xs_x27_2732_, v___y_2668_, v___x_2735_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2736_);
v___x_2738_ = v___x_2682_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_typeIdOf_2672_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_exprToStructId_2673_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_exprToStructIdEntries_2674_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v_forbiddenNatModules_2675_);
lean_ctor_set(v_reuseFailAlloc_2739_, 5, v_natStructs_2676_);
lean_ctor_set(v_reuseFailAlloc_2739_, 6, v_natTypeIdOf_2677_);
lean_ctor_set(v_reuseFailAlloc_2739_, 7, v_exprToNatStructId_2678_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2751_, lean_object* v_a_2752_, lean_object* v_s_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2751_, v_a_2752_, v_s_2753_);
lean_dec(v___y_2751_);
return v_res_2754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_cls_2762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2764_ = l_Lean_Name_append(v___x_2763_, v_cls_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_toCold_2803_; lean_object* v_options_2804_; uint8_t v_hasTrace_2805_; 
v_toCold_2803_ = lean_ctor_get(v_a_2775_, 0);
v_options_2804_ = lean_ctor_get(v_toCold_2803_, 2);
v_hasTrace_2805_ = lean_ctor_get_uint8(v_options_2804_, sizeof(void*)*1);
if (v_hasTrace_2805_ == 0)
{
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v_inheritedTraceOptions_2806_; lean_object* v_cls_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_inheritedTraceOptions_2806_ = lean_ctor_get(v_toCold_2803_, 11);
v_cls_2807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2806_, v_options_2804_, v___x_2808_);
if (v___x_2809_ == 0)
{
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l_Lean_MessageData_ofExpr(v_a_2811_);
v___x_2813_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2807_, v___x_2812_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_dec_ref_known(v___x_2813_, 1);
v___y_2779_ = v_a_2766_;
v___y_2780_ = v_a_2767_;
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
return v___x_2813_;
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
v_a_2814_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2810_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2810_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
v___jp_2778_:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2765_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
lean_inc(v___y_2779_);
v___f_2792_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2792_, 0, v___y_2779_);
lean_closure_set(v___f_2792_, 1, v_a_2791_);
v___x_2793_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2794_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2793_, v___f_2792_, v___y_2780_);
return v___x_2794_;
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2790_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2790_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_c_2822_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_p_2849_; lean_object* v_toCold_2850_; lean_object* v_currRecDepth_2851_; lean_object* v_ref_2852_; uint16_t v_optionFlags_2853_; uint8_t v_suppressElabErrors_2854_; uint8_t v_isRecordingDeps_2855_; lean_object* v_maxRecDepth_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_p_2849_ = lean_ctor_get(v_c_u2082_2836_, 0);
v_toCold_2850_ = lean_ctor_get(v_a_2846_, 0);
lean_inc_ref(v_toCold_2850_);
v_currRecDepth_2851_ = lean_ctor_get(v_a_2846_, 1);
lean_inc(v_currRecDepth_2851_);
v_ref_2852_ = lean_ctor_get(v_a_2846_, 2);
lean_inc(v_ref_2852_);
v_optionFlags_2853_ = lean_ctor_get_uint16(v_a_2846_, sizeof(void*)*3);
v_suppressElabErrors_2854_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2855_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2846_);
v_maxRecDepth_2907_ = lean_ctor_get(v_toCold_2850_, 3);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_nat_dec_eq(v_maxRecDepth_2907_, v___x_2908_);
if (v___x_2909_ == 0)
{
uint8_t v___x_2910_; 
v___x_2910_ = lean_nat_dec_eq(v_currRecDepth_2851_, v_maxRecDepth_2907_);
if (v___x_2910_ == 0)
{
goto v___jp_2856_;
}
else
{
lean_object* v___x_2911_; 
lean_dec(v_currRecDepth_2851_);
lean_dec_ref(v_toCold_2850_);
lean_dec_ref(v_c_u2082_2836_);
v___x_2911_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2852_);
return v___x_2911_;
}
}
else
{
goto v___jp_2856_;
}
v___jp_2856_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_2858_ = lean_nat_add(v_currRecDepth_2851_, v___x_2857_);
lean_dec(v_currRecDepth_2851_);
v___x_2859_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2859_, 0, v_toCold_2850_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
lean_ctor_set(v___x_2859_, 2, v_ref_2852_);
lean_ctor_set_uint16(v___x_2859_, sizeof(void*)*3, v_optionFlags_2853_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*3 + 2, v_suppressElabErrors_2854_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*3 + 3, v_isRecordingDeps_2855_);
v___x_2860_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2849_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v___x_2859_, v_a_2847_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2898_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2898_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2898_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
if (lean_obj_tag(v_a_2861_) == 1)
{
lean_object* v_val_2865_; lean_object* v_snd_2866_; lean_object* v_snd_2867_; lean_object* v_fst_2868_; lean_object* v_fst_2869_; lean_object* v_p_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_del_object(v___x_2863_);
v_val_2865_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v_a_2861_, 1);
v_snd_2866_ = lean_ctor_get(v_val_2865_, 1);
lean_inc(v_snd_2866_);
v_snd_2867_ = lean_ctor_get(v_snd_2866_, 1);
lean_inc(v_snd_2867_);
v_fst_2868_ = lean_ctor_get(v_val_2865_, 0);
lean_inc(v_fst_2868_);
lean_dec(v_val_2865_);
v_fst_2869_ = lean_ctor_get(v_snd_2866_, 0);
lean_inc(v_fst_2869_);
lean_dec(v_snd_2866_);
v_p_2870_ = lean_ctor_get(v_snd_2867_, 0);
v___x_2871_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2870_, v_fst_2869_);
lean_inc_ref(v_c_u2082_2836_);
v___x_2872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2871_, v_fst_2869_, v_snd_2867_, v_fst_2868_, v_c_u2082_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v___x_2859_, v_a_2847_);
lean_dec(v_fst_2869_);
lean_dec(v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
if (lean_obj_tag(v_a_2873_) == 1)
{
lean_object* v_val_2874_; 
lean_dec_ref(v_c_u2082_2836_);
v_val_2874_ = lean_ctor_get(v_a_2873_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_a_2873_, 1);
v_c_u2082_2836_ = v_val_2874_;
v_a_2846_ = v___x_2859_;
goto _start;
}
else
{
lean_object* v___x_2876_; 
lean_dec(v_a_2873_);
v___x_2876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v___x_2859_, v_a_2847_);
lean_dec_ref_known(v___x_2859_, 3);
lean_dec_ref(v_c_u2082_2836_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2884_; 
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2876_, 0);
lean_dec(v_unused_2885_);
v___x_2878_ = v___x_2876_;
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v___x_2876_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_box(0);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2880_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2876_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2876_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2859_, 3);
lean_dec_ref(v_c_u2082_2836_);
return v___x_2872_;
}
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec(v_a_2861_);
lean_dec_ref_known(v___x_2859_, 3);
v___x_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_c_u2082_2836_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2894_);
v___x_2896_ = v___x_2863_;
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
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref_known(v___x_2859_, 3);
lean_dec_ref(v_c_u2082_2836_);
v_a_2899_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2860_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2860_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec(v_a_2913_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2926_, lean_object* v_x_2927_, size_t v_x_2928_, size_t v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
lean_object* v_cs_2930_; size_t v_j_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_cs_2930_ = lean_ctor_get(v_x_2927_, 0);
v_j_2931_ = lean_usize_shift_right(v_x_2928_, v_x_2929_);
v___x_2932_ = lean_usize_to_nat(v_j_2931_);
v___x_2933_ = lean_array_get_size(v_cs_2930_);
v___x_2934_ = lean_nat_dec_lt(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_dec(v___x_2932_);
lean_dec_ref(v_val_2926_);
return v_x_2927_;
}
else
{
lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2952_; 
lean_inc_ref(v_cs_2930_);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_x_2927_, 0);
lean_dec(v_unused_2953_);
v___x_2936_ = v_x_2927_;
v_isShared_2937_ = v_isSharedCheck_2952_;
goto v_resetjp_2935_;
}
else
{
lean_dec(v_x_2927_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2952_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
size_t v___x_2938_; size_t v___x_2939_; size_t v___x_2940_; size_t v_i_2941_; size_t v___x_2942_; size_t v_shift_2943_; lean_object* v_v_2944_; lean_object* v___x_2945_; lean_object* v_xs_x27_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_shift_left(v___x_2938_, v_x_2929_);
v___x_2940_ = lean_usize_sub(v___x_2939_, v___x_2938_);
v_i_2941_ = lean_usize_land(v_x_2928_, v___x_2940_);
v___x_2942_ = ((size_t)5ULL);
v_shift_2943_ = lean_usize_sub(v_x_2929_, v___x_2942_);
v_v_2944_ = lean_array_fget(v_cs_2930_, v___x_2932_);
v___x_2945_ = lean_box(0);
v_xs_x27_2946_ = lean_array_fset(v_cs_2930_, v___x_2932_, v___x_2945_);
v___x_2947_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2926_, v_v_2944_, v_i_2941_, v_shift_2943_);
v___x_2948_ = lean_array_fset(v_xs_x27_2946_, v___x_2932_, v___x_2947_);
lean_dec(v___x_2932_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v___x_2948_);
v___x_2950_ = v___x_2936_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_vs_2954_ = lean_ctor_get(v_x_2927_, 0);
v___x_2955_ = lean_usize_to_nat(v_x_2928_);
v___x_2956_ = lean_array_get_size(v_vs_2954_);
v___x_2957_ = lean_nat_dec_lt(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_dec(v___x_2955_);
lean_dec_ref(v_val_2926_);
return v_x_2927_;
}
else
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2969_; 
lean_inc_ref(v_vs_2954_);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_x_2927_, 0);
lean_dec(v_unused_2970_);
v___x_2959_ = v_x_2927_;
v_isShared_2960_ = v_isSharedCheck_2969_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v_x_2927_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2969_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_v_2961_; lean_object* v___x_2962_; lean_object* v_xs_x27_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v_v_2961_ = lean_array_fget(v_vs_2954_, v___x_2955_);
v___x_2962_ = lean_box(0);
v_xs_x27_2963_ = lean_array_fset(v_vs_2954_, v___x_2955_, v___x_2962_);
v___x_2964_ = l_Lean_PersistentArray_push___redArg(v_v_2961_, v_val_2926_);
v___x_2965_ = lean_array_fset(v_xs_x27_2963_, v___x_2955_, v___x_2964_);
lean_dec(v___x_2955_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2965_);
v___x_2967_ = v___x_2959_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
size_t v_x_41338__boxed_2975_; size_t v_x_41339__boxed_2976_; lean_object* v_res_2977_; 
v_x_41338__boxed_2975_ = lean_unbox_usize(v_x_2973_);
lean_dec(v_x_2973_);
v_x_41339__boxed_2976_ = lean_unbox_usize(v_x_2974_);
lean_dec(v_x_2974_);
v_res_2977_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2971_, v_x_2972_, v_x_41338__boxed_2975_, v_x_41339__boxed_2976_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2978_, lean_object* v_t_2979_, lean_object* v_i_2980_){
_start:
{
lean_object* v_root_2981_; lean_object* v_tail_2982_; lean_object* v_size_2983_; size_t v_shift_2984_; lean_object* v_tailOff_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3009_; 
v_root_2981_ = lean_ctor_get(v_t_2979_, 0);
v_tail_2982_ = lean_ctor_get(v_t_2979_, 1);
v_size_2983_ = lean_ctor_get(v_t_2979_, 2);
v_shift_2984_ = lean_ctor_get_usize(v_t_2979_, 4);
v_tailOff_2985_ = lean_ctor_get(v_t_2979_, 3);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_t_2979_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2987_ = v_t_2979_;
v_isShared_2988_ = v_isSharedCheck_3009_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_tailOff_2985_);
lean_inc(v_size_2983_);
lean_inc(v_tail_2982_);
lean_inc(v_root_2981_);
lean_dec(v_t_2979_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3009_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_nat_dec_le(v_tailOff_2985_, v_i_2980_);
if (v___x_2989_ == 0)
{
size_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = lean_usize_of_nat(v_i_2980_);
v___x_2991_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2978_, v_root_2981_, v___x_2990_, v_shift_2984_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2991_);
v___x_2993_ = v___x_2987_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_tail_2982_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_size_2983_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_tailOff_2985_);
lean_ctor_set_usize(v_reuseFailAlloc_2994_, 4, v_shift_2984_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_nat_sub(v_i_2980_, v_tailOff_2985_);
v___x_2996_ = lean_array_get_size(v_tail_2982_);
v___x_2997_ = lean_nat_dec_lt(v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2999_; 
lean_dec(v___x_2995_);
lean_dec_ref(v_val_2978_);
if (v_isShared_2988_ == 0)
{
v___x_2999_ = v___x_2987_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_root_2981_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_tail_2982_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_size_2983_);
lean_ctor_set(v_reuseFailAlloc_3000_, 3, v_tailOff_2985_);
lean_ctor_set_usize(v_reuseFailAlloc_3000_, 4, v_shift_2984_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
else
{
lean_object* v_v_3001_; lean_object* v___x_3002_; lean_object* v_xs_x27_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v_v_3001_ = lean_array_fget(v_tail_2982_, v___x_2995_);
v___x_3002_ = lean_box(0);
v_xs_x27_3003_ = lean_array_fset(v_tail_2982_, v___x_2995_, v___x_3002_);
v___x_3004_ = l_Lean_PersistentArray_push___redArg(v_v_3001_, v_val_2978_);
v___x_3005_ = lean_array_fset(v_xs_x27_3003_, v___x_2995_, v___x_3004_);
lean_dec(v___x_2995_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v___x_3005_);
v___x_3007_ = v___x_2987_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_root_2981_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_size_2983_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_tailOff_2985_);
lean_ctor_set_usize(v_reuseFailAlloc_3008_, 4, v_shift_2984_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3010_, lean_object* v_t_3011_, lean_object* v_i_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3010_, v_t_3011_, v_i_3012_);
lean_dec(v_i_3012_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3014_, lean_object* v_val_3015_, lean_object* v_v_3016_, lean_object* v_s_3017_){
_start:
{
lean_object* v_structs_3018_; lean_object* v_typeIdOf_3019_; lean_object* v_exprToStructId_3020_; lean_object* v_exprToStructIdEntries_3021_; lean_object* v_forbiddenNatModules_3022_; lean_object* v_natStructs_3023_; lean_object* v_natTypeIdOf_3024_; lean_object* v_exprToNatStructId_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v_structs_3018_ = lean_ctor_get(v_s_3017_, 0);
v_typeIdOf_3019_ = lean_ctor_get(v_s_3017_, 1);
v_exprToStructId_3020_ = lean_ctor_get(v_s_3017_, 2);
v_exprToStructIdEntries_3021_ = lean_ctor_get(v_s_3017_, 3);
v_forbiddenNatModules_3022_ = lean_ctor_get(v_s_3017_, 4);
v_natStructs_3023_ = lean_ctor_get(v_s_3017_, 5);
v_natTypeIdOf_3024_ = lean_ctor_get(v_s_3017_, 6);
v_exprToNatStructId_3025_ = lean_ctor_get(v_s_3017_, 7);
v___x_3026_ = lean_array_get_size(v_structs_3018_);
v___x_3027_ = lean_nat_dec_lt(v___y_3014_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_dec_ref(v_val_3015_);
return v_s_3017_;
}
else
{
lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3089_; 
lean_inc_ref(v_exprToNatStructId_3025_);
lean_inc_ref(v_natTypeIdOf_3024_);
lean_inc_ref(v_natStructs_3023_);
lean_inc_ref(v_forbiddenNatModules_3022_);
lean_inc_ref(v_exprToStructIdEntries_3021_);
lean_inc_ref(v_exprToStructId_3020_);
lean_inc_ref(v_typeIdOf_3019_);
lean_inc_ref(v_structs_3018_);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_s_3017_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; lean_object* v_unused_3091_; lean_object* v_unused_3092_; lean_object* v_unused_3093_; lean_object* v_unused_3094_; lean_object* v_unused_3095_; lean_object* v_unused_3096_; lean_object* v_unused_3097_; 
v_unused_3090_ = lean_ctor_get(v_s_3017_, 7);
lean_dec(v_unused_3090_);
v_unused_3091_ = lean_ctor_get(v_s_3017_, 6);
lean_dec(v_unused_3091_);
v_unused_3092_ = lean_ctor_get(v_s_3017_, 5);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_s_3017_, 4);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_s_3017_, 3);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_s_3017_, 2);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_s_3017_, 1);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_s_3017_, 0);
lean_dec(v_unused_3097_);
v___x_3029_ = v_s_3017_;
v_isShared_3030_ = v_isSharedCheck_3089_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v_s_3017_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3089_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v_v_3031_; lean_object* v_id_3032_; lean_object* v_ringId_x3f_3033_; lean_object* v_type_3034_; lean_object* v_u_3035_; lean_object* v_intModuleInst_3036_; lean_object* v_leInst_x3f_3037_; lean_object* v_ltInst_x3f_3038_; lean_object* v_lawfulOrderLTInst_x3f_3039_; lean_object* v_isPreorderInst_x3f_3040_; lean_object* v_orderedAddInst_x3f_3041_; lean_object* v_isLinearInst_x3f_3042_; lean_object* v_noNatDivInst_x3f_3043_; lean_object* v_ringInst_x3f_3044_; lean_object* v_commRingInst_x3f_3045_; lean_object* v_orderedRingInst_x3f_3046_; lean_object* v_fieldInst_x3f_3047_; lean_object* v_charInst_x3f_3048_; lean_object* v_zero_3049_; lean_object* v_ofNatZero_3050_; lean_object* v_one_x3f_3051_; lean_object* v_leFn_x3f_3052_; lean_object* v_ltFn_x3f_3053_; lean_object* v_addFn_3054_; lean_object* v_zsmulFn_3055_; lean_object* v_nsmulFn_3056_; lean_object* v_zsmulFn_x3f_3057_; lean_object* v_nsmulFn_x3f_3058_; lean_object* v_homomulFn_x3f_3059_; lean_object* v_subFn_3060_; lean_object* v_negFn_3061_; lean_object* v_vars_3062_; lean_object* v_varMap_3063_; lean_object* v_lowers_3064_; lean_object* v_uppers_3065_; lean_object* v_diseqs_3066_; lean_object* v_assignment_3067_; uint8_t v_caseSplits_3068_; lean_object* v_conflict_x3f_3069_; lean_object* v_diseqSplits_3070_; lean_object* v_elimEqs_3071_; lean_object* v_elimStack_3072_; lean_object* v_occurs_3073_; lean_object* v_ignored_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3088_; 
v_v_3031_ = lean_array_fget(v_structs_3018_, v___y_3014_);
v_id_3032_ = lean_ctor_get(v_v_3031_, 0);
v_ringId_x3f_3033_ = lean_ctor_get(v_v_3031_, 1);
v_type_3034_ = lean_ctor_get(v_v_3031_, 2);
v_u_3035_ = lean_ctor_get(v_v_3031_, 3);
v_intModuleInst_3036_ = lean_ctor_get(v_v_3031_, 4);
v_leInst_x3f_3037_ = lean_ctor_get(v_v_3031_, 5);
v_ltInst_x3f_3038_ = lean_ctor_get(v_v_3031_, 6);
v_lawfulOrderLTInst_x3f_3039_ = lean_ctor_get(v_v_3031_, 7);
v_isPreorderInst_x3f_3040_ = lean_ctor_get(v_v_3031_, 8);
v_orderedAddInst_x3f_3041_ = lean_ctor_get(v_v_3031_, 9);
v_isLinearInst_x3f_3042_ = lean_ctor_get(v_v_3031_, 10);
v_noNatDivInst_x3f_3043_ = lean_ctor_get(v_v_3031_, 11);
v_ringInst_x3f_3044_ = lean_ctor_get(v_v_3031_, 12);
v_commRingInst_x3f_3045_ = lean_ctor_get(v_v_3031_, 13);
v_orderedRingInst_x3f_3046_ = lean_ctor_get(v_v_3031_, 14);
v_fieldInst_x3f_3047_ = lean_ctor_get(v_v_3031_, 15);
v_charInst_x3f_3048_ = lean_ctor_get(v_v_3031_, 16);
v_zero_3049_ = lean_ctor_get(v_v_3031_, 17);
v_ofNatZero_3050_ = lean_ctor_get(v_v_3031_, 18);
v_one_x3f_3051_ = lean_ctor_get(v_v_3031_, 19);
v_leFn_x3f_3052_ = lean_ctor_get(v_v_3031_, 20);
v_ltFn_x3f_3053_ = lean_ctor_get(v_v_3031_, 21);
v_addFn_3054_ = lean_ctor_get(v_v_3031_, 22);
v_zsmulFn_3055_ = lean_ctor_get(v_v_3031_, 23);
v_nsmulFn_3056_ = lean_ctor_get(v_v_3031_, 24);
v_zsmulFn_x3f_3057_ = lean_ctor_get(v_v_3031_, 25);
v_nsmulFn_x3f_3058_ = lean_ctor_get(v_v_3031_, 26);
v_homomulFn_x3f_3059_ = lean_ctor_get(v_v_3031_, 27);
v_subFn_3060_ = lean_ctor_get(v_v_3031_, 28);
v_negFn_3061_ = lean_ctor_get(v_v_3031_, 29);
v_vars_3062_ = lean_ctor_get(v_v_3031_, 30);
v_varMap_3063_ = lean_ctor_get(v_v_3031_, 31);
v_lowers_3064_ = lean_ctor_get(v_v_3031_, 32);
v_uppers_3065_ = lean_ctor_get(v_v_3031_, 33);
v_diseqs_3066_ = lean_ctor_get(v_v_3031_, 34);
v_assignment_3067_ = lean_ctor_get(v_v_3031_, 35);
v_caseSplits_3068_ = lean_ctor_get_uint8(v_v_3031_, sizeof(void*)*42);
v_conflict_x3f_3069_ = lean_ctor_get(v_v_3031_, 36);
v_diseqSplits_3070_ = lean_ctor_get(v_v_3031_, 37);
v_elimEqs_3071_ = lean_ctor_get(v_v_3031_, 38);
v_elimStack_3072_ = lean_ctor_get(v_v_3031_, 39);
v_occurs_3073_ = lean_ctor_get(v_v_3031_, 40);
v_ignored_3074_ = lean_ctor_get(v_v_3031_, 41);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_v_3031_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3076_ = v_v_3031_;
v_isShared_3077_ = v_isSharedCheck_3088_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_ignored_3074_);
lean_inc(v_occurs_3073_);
lean_inc(v_elimStack_3072_);
lean_inc(v_elimEqs_3071_);
lean_inc(v_diseqSplits_3070_);
lean_inc(v_conflict_x3f_3069_);
lean_inc(v_assignment_3067_);
lean_inc(v_diseqs_3066_);
lean_inc(v_uppers_3065_);
lean_inc(v_lowers_3064_);
lean_inc(v_varMap_3063_);
lean_inc(v_vars_3062_);
lean_inc(v_negFn_3061_);
lean_inc(v_subFn_3060_);
lean_inc(v_homomulFn_x3f_3059_);
lean_inc(v_nsmulFn_x3f_3058_);
lean_inc(v_zsmulFn_x3f_3057_);
lean_inc(v_nsmulFn_3056_);
lean_inc(v_zsmulFn_3055_);
lean_inc(v_addFn_3054_);
lean_inc(v_ltFn_x3f_3053_);
lean_inc(v_leFn_x3f_3052_);
lean_inc(v_one_x3f_3051_);
lean_inc(v_ofNatZero_3050_);
lean_inc(v_zero_3049_);
lean_inc(v_charInst_x3f_3048_);
lean_inc(v_fieldInst_x3f_3047_);
lean_inc(v_orderedRingInst_x3f_3046_);
lean_inc(v_commRingInst_x3f_3045_);
lean_inc(v_ringInst_x3f_3044_);
lean_inc(v_noNatDivInst_x3f_3043_);
lean_inc(v_isLinearInst_x3f_3042_);
lean_inc(v_orderedAddInst_x3f_3041_);
lean_inc(v_isPreorderInst_x3f_3040_);
lean_inc(v_lawfulOrderLTInst_x3f_3039_);
lean_inc(v_ltInst_x3f_3038_);
lean_inc(v_leInst_x3f_3037_);
lean_inc(v_intModuleInst_3036_);
lean_inc(v_u_3035_);
lean_inc(v_type_3034_);
lean_inc(v_ringId_x3f_3033_);
lean_inc(v_id_3032_);
lean_dec(v_v_3031_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3088_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v_xs_x27_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3078_ = lean_box(0);
v_xs_x27_3079_ = lean_array_fset(v_structs_3018_, v___y_3014_, v___x_3078_);
v___x_3080_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3015_, v_diseqs_3066_, v_v_3016_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 34, v___x_3080_);
v___x_3082_ = v___x_3076_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_id_3032_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_ringId_x3f_3033_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_type_3034_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_u_3035_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_intModuleInst_3036_);
lean_ctor_set(v_reuseFailAlloc_3087_, 5, v_leInst_x3f_3037_);
lean_ctor_set(v_reuseFailAlloc_3087_, 6, v_ltInst_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3087_, 7, v_lawfulOrderLTInst_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3087_, 8, v_isPreorderInst_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3087_, 9, v_orderedAddInst_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3087_, 10, v_isLinearInst_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3087_, 11, v_noNatDivInst_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3087_, 12, v_ringInst_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3087_, 13, v_commRingInst_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3087_, 14, v_orderedRingInst_x3f_3046_);
lean_ctor_set(v_reuseFailAlloc_3087_, 15, v_fieldInst_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3087_, 16, v_charInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3087_, 17, v_zero_3049_);
lean_ctor_set(v_reuseFailAlloc_3087_, 18, v_ofNatZero_3050_);
lean_ctor_set(v_reuseFailAlloc_3087_, 19, v_one_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3087_, 20, v_leFn_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3087_, 21, v_ltFn_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3087_, 22, v_addFn_3054_);
lean_ctor_set(v_reuseFailAlloc_3087_, 23, v_zsmulFn_3055_);
lean_ctor_set(v_reuseFailAlloc_3087_, 24, v_nsmulFn_3056_);
lean_ctor_set(v_reuseFailAlloc_3087_, 25, v_zsmulFn_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3087_, 26, v_nsmulFn_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3087_, 27, v_homomulFn_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3087_, 28, v_subFn_3060_);
lean_ctor_set(v_reuseFailAlloc_3087_, 29, v_negFn_3061_);
lean_ctor_set(v_reuseFailAlloc_3087_, 30, v_vars_3062_);
lean_ctor_set(v_reuseFailAlloc_3087_, 31, v_varMap_3063_);
lean_ctor_set(v_reuseFailAlloc_3087_, 32, v_lowers_3064_);
lean_ctor_set(v_reuseFailAlloc_3087_, 33, v_uppers_3065_);
lean_ctor_set(v_reuseFailAlloc_3087_, 34, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3087_, 35, v_assignment_3067_);
lean_ctor_set(v_reuseFailAlloc_3087_, 36, v_conflict_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3087_, 37, v_diseqSplits_3070_);
lean_ctor_set(v_reuseFailAlloc_3087_, 38, v_elimEqs_3071_);
lean_ctor_set(v_reuseFailAlloc_3087_, 39, v_elimStack_3072_);
lean_ctor_set(v_reuseFailAlloc_3087_, 40, v_occurs_3073_);
lean_ctor_set(v_reuseFailAlloc_3087_, 41, v_ignored_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3087_, sizeof(void*)*42, v_caseSplits_3068_);
v___x_3082_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = lean_array_fset(v_xs_x27_3079_, v___y_3014_, v___x_3082_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3083_);
v___x_3085_ = v___x_3029_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_typeIdOf_3019_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_exprToStructId_3020_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_exprToStructIdEntries_3021_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_forbiddenNatModules_3022_);
lean_ctor_set(v_reuseFailAlloc_3086_, 5, v_natStructs_3023_);
lean_ctor_set(v_reuseFailAlloc_3086_, 6, v_natTypeIdOf_3024_);
lean_ctor_set(v_reuseFailAlloc_3086_, 7, v_exprToNatStructId_3025_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3098_, lean_object* v_val_3099_, lean_object* v_v_3100_, lean_object* v_s_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3098_, v_val_3099_, v_v_3100_, v_s_3101_);
lean_dec(v_v_3100_);
lean_dec(v___y_3098_);
return v_res_3102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3110_ = l_Lean_Name_append(v___x_3109_, v___x_3108_);
return v___x_3110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3119_ = l_Lean_Name_append(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_cls_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3126_ = l_Lean_Name_append(v___x_3125_, v_cls_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v_toCold_3198_; lean_object* v_options_3199_; lean_object* v_inheritedTraceOptions_3200_; uint8_t v_hasTrace_3201_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; 
v_toCold_3198_ = lean_ctor_get(v_a_3137_, 0);
v_options_3199_ = lean_ctor_get(v_toCold_3198_, 2);
v_inheritedTraceOptions_3200_ = lean_ctor_get(v_toCold_3198_, 11);
v_hasTrace_3201_ = lean_ctor_get_uint8(v_options_3199_, sizeof(void*)*1);
if (v_hasTrace_3201_ == 0)
{
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
goto v___jp_3202_;
}
else
{
lean_object* v_cls_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v_cls_3274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3200_, v_options_3199_, v___x_3275_);
if (v___x_3276_ == 0)
{
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
goto v___jp_3202_;
}
else
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = l_Lean_MessageData_ofExpr(v_a_3278_);
v___x_3280_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3274_, v___x_3279_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_dec_ref_known(v___x_3280_, 1);
v___y_3203_ = v_a_3128_;
v___y_3204_ = v_a_3129_;
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
goto v___jp_3202_;
}
else
{
lean_dec_ref(v_c_3127_);
return v___x_3280_;
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_c_3127_);
v_a_3281_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3277_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3277_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___f_3157_; lean_object* v___x_3158_; 
lean_inc(v___y_3146_);
v___f_3157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3157_, 0, v___y_3146_);
lean_closure_set(v___f_3157_, 1, v___y_3141_);
lean_closure_set(v___f_3157_, 2, v___y_3142_);
v___x_3158_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3143_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref_known(v___x_3158_, 1);
v___x_3159_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3160_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3159_, v___f_3157_, v___y_3147_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref_known(v___x_3160_, 1);
v___x_3161_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3144_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3174_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
uint8_t v___x_3166_; uint8_t v___x_3167_; uint8_t v___x_3168_; 
v___x_3166_ = 0;
v___x_3167_ = lean_unbox(v_a_3162_);
lean_dec(v_a_3162_);
v___x_3168_ = l_Lean_instBEqLBool_beq(v___x_3167_, v___x_3166_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
lean_dec(v___y_3145_);
v___x_3169_ = lean_box(0);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3169_);
v___x_3171_ = v___x_3164_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
else
{
lean_object* v___x_3173_; 
lean_del_object(v___x_3164_);
v___x_3173_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3173_;
}
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec(v___y_3145_);
v_a_3175_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3161_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3161_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v___x_3160_;
}
}
else
{
lean_dec_ref(v___f_3157_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v___x_3158_;
}
}
v___jp_3183_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3184_);
v___x_3197_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3196_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3197_;
}
v___jp_3202_:
{
lean_object* v___x_3214_; 
lean_inc_ref(v___y_3212_);
v___x_3214_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3127_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3265_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3265_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3265_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
if (lean_obj_tag(v_a_3215_) == 1)
{
lean_object* v_val_3219_; lean_object* v_p_3220_; 
lean_del_object(v___x_3217_);
v_val_3219_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_val_3219_);
lean_dec_ref_known(v_a_3215_, 1);
v_p_3220_ = lean_ctor_get(v_val_3219_, 0);
if (lean_obj_tag(v_p_3220_) == 0)
{
lean_object* v_toCold_3221_; lean_object* v_options_3222_; uint8_t v_hasTrace_3223_; 
v_toCold_3221_ = lean_ctor_get(v___y_3212_, 0);
v_options_3222_ = lean_ctor_get(v_toCold_3221_, 2);
v_hasTrace_3223_ = lean_ctor_get_uint8(v_options_3222_, sizeof(void*)*1);
if (v_hasTrace_3223_ == 0)
{
v___y_3184_ = v_val_3219_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
goto v___jp_3183_;
}
else
{
lean_object* v_inheritedTraceOptions_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v_inheritedTraceOptions_3224_ = lean_ctor_get(v_toCold_3221_, 11);
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3227_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3224_, v_options_3222_, v___x_3226_);
if (v___x_3227_ == 0)
{
v___y_3184_ = v_val_3219_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3219_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_MessageData_ofExpr(v_a_3229_);
v___x_3231_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3225_, v___x_3230_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec_ref_known(v___x_3231_, 1);
v___y_3184_ = v_val_3219_;
v___y_3185_ = v___y_3203_;
v___y_3186_ = v___y_3204_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
goto v___jp_3183_;
}
else
{
lean_dec(v_val_3219_);
return v___x_3231_;
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v_val_3219_);
v_a_3232_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3228_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3228_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3240_; lean_object* v_options_3241_; uint8_t v_hasTrace_3242_; 
lean_inc_ref(v_p_3220_);
v_toCold_3240_ = lean_ctor_get(v___y_3212_, 0);
v_options_3241_ = lean_ctor_get(v_toCold_3240_, 2);
v_hasTrace_3242_ = lean_ctor_get_uint8(v_options_3241_, sizeof(void*)*1);
if (v_hasTrace_3242_ == 0)
{
lean_object* v_v_3243_; 
v_v_3243_ = lean_ctor_get(v_p_3220_, 1);
lean_inc_n(v_v_3243_, 2);
lean_inc(v_val_3219_);
v___y_3141_ = v_val_3219_;
v___y_3142_ = v_v_3243_;
v___y_3143_ = v_p_3220_;
v___y_3144_ = v_val_3219_;
v___y_3145_ = v_v_3243_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
goto v___jp_3140_;
}
else
{
lean_object* v_v_3244_; lean_object* v_inheritedTraceOptions_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v_v_3244_ = lean_ctor_get(v_p_3220_, 1);
lean_inc(v_v_3244_);
v_inheritedTraceOptions_3245_ = lean_ctor_get(v_toCold_3240_, 11);
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3245_, v_options_3241_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_inc(v_v_3244_);
lean_inc(v_val_3219_);
v___y_3141_ = v_val_3219_;
v___y_3142_ = v_v_3244_;
v___y_3143_ = v_p_3220_;
v___y_3144_ = v_val_3219_;
v___y_3145_ = v_v_3244_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3219_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3251_ = l_Lean_MessageData_ofExpr(v_a_3250_);
v___x_3252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3246_, v___x_3251_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_dec_ref_known(v___x_3252_, 1);
lean_inc(v_v_3244_);
lean_inc(v_val_3219_);
v___y_3141_ = v_val_3219_;
v___y_3142_ = v_v_3244_;
v___y_3143_ = v_p_3220_;
v___y_3144_ = v_val_3219_;
v___y_3145_ = v_v_3244_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___y_3204_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
goto v___jp_3140_;
}
else
{
lean_dec(v_v_3244_);
lean_dec_ref_known(v_p_3220_, 3);
lean_dec(v_val_3219_);
return v___x_3252_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_v_3244_);
lean_dec_ref_known(v_p_3220_, 3);
lean_dec(v_val_3219_);
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
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
lean_dec(v_a_3215_);
v___x_3261_ = lean_box(0);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3261_);
v___x_3263_ = v___x_3217_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
v_a_3266_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3214_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3214_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec(v_a_3290_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3303_, lean_object* v_as_3304_, size_t v_sz_3305_, size_t v_i_3306_, lean_object* v_b_3307_){
_start:
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_usize_dec_lt(v_i_3306_, v_sz_3305_);
if (v___x_3308_ == 0)
{
return v_b_3307_;
}
else
{
lean_object* v_snd_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3350_; 
v_snd_3309_ = lean_ctor_get(v_b_3307_, 1);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_b_3307_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v_b_3307_, 0);
lean_dec(v_unused_3351_);
v___x_3311_ = v_b_3307_;
v_isShared_3312_ = v_isSharedCheck_3350_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_snd_3309_);
lean_dec(v_b_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3350_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3349_; 
v_fst_3313_ = lean_ctor_get(v_snd_3309_, 0);
v_snd_3314_ = lean_ctor_get(v_snd_3309_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_snd_3309_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3316_ = v_snd_3309_;
v_isShared_3317_ = v_isSharedCheck_3349_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_snd_3314_);
lean_inc(v_fst_3313_);
lean_dec(v_snd_3309_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3349_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v_a_3318_; lean_object* v_p_3319_; lean_object* v___x_3320_; lean_object* v_a_3322_; lean_object* v_b_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v_a_3318_ = lean_array_uget(v_as_3304_, v_i_3306_);
v_p_3319_ = lean_ctor_get(v_a_3318_, 0);
v___x_3320_ = lean_box(0);
v_b_3329_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3319_, v_x_3303_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3331_ = lean_int_dec_eq(v_b_3329_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3333_; 
lean_inc(v_a_3318_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v_a_3318_);
lean_ctor_set(v___x_3311_, 0, v_b_3329_);
v___x_3333_ = v___x_3311_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_b_3329_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_a_3318_);
v___x_3333_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; lean_object* v_unused_3343_; 
v_unused_3342_ = lean_ctor_get(v_a_3318_, 1);
lean_dec(v_unused_3342_);
v_unused_3343_ = lean_ctor_get(v_a_3318_, 0);
lean_dec(v_unused_3343_);
v___x_3335_ = v_a_3318_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v_a_3318_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_todo_3337_; lean_object* v___x_3339_; 
v_todo_3337_ = lean_array_push(v_snd_3314_, v___x_3333_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 1, v_todo_3337_);
lean_ctor_set(v___x_3335_, 0, v_fst_3313_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fst_3313_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_todo_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
v_a_3322_ = v___x_3339_;
goto v___jp_3321_;
}
}
}
}
else
{
lean_object* v_cs_x27_3345_; lean_object* v___x_3347_; 
lean_dec(v_b_3329_);
v_cs_x27_3345_ = l_Lean_PersistentArray_push___redArg(v_fst_3313_, v_a_3318_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v_snd_3314_);
lean_ctor_set(v___x_3311_, 0, v_cs_x27_3345_);
v___x_3347_ = v___x_3311_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_cs_x27_3345_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_snd_3314_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
v_a_3322_ = v___x_3347_;
goto v___jp_3321_;
}
}
v___jp_3321_:
{
lean_object* v___x_3324_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 1, v_a_3322_);
lean_ctor_set(v___x_3316_, 0, v___x_3320_);
v___x_3324_ = v___x_3316_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_a_3322_);
v___x_3324_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
size_t v___x_3325_; size_t v___x_3326_; 
v___x_3325_ = ((size_t)1ULL);
v___x_3326_ = lean_usize_add(v_i_3306_, v___x_3325_);
v_i_3306_ = v___x_3326_;
v_b_3307_ = v___x_3324_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3352_, lean_object* v_as_3353_, lean_object* v_sz_3354_, lean_object* v_i_3355_, lean_object* v_b_3356_){
_start:
{
size_t v_sz_boxed_3357_; size_t v_i_boxed_3358_; lean_object* v_res_3359_; 
v_sz_boxed_3357_ = lean_unbox_usize(v_sz_3354_);
lean_dec(v_sz_3354_);
v_i_boxed_3358_ = lean_unbox_usize(v_i_3355_);
lean_dec(v_i_3355_);
v_res_3359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3352_, v_as_3353_, v_sz_boxed_3357_, v_i_boxed_3358_, v_b_3356_);
lean_dec_ref(v_as_3353_);
lean_dec(v_x_3352_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3360_, lean_object* v_as_3361_, size_t v_sz_3362_, size_t v_i_3363_, lean_object* v_b_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3363_, v_sz_3362_);
if (v___x_3365_ == 0)
{
return v_b_3364_;
}
else
{
lean_object* v_snd_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3407_; 
v_snd_3366_ = lean_ctor_get(v_b_3364_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_b_3364_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v_b_3364_, 0);
lean_dec(v_unused_3408_);
v___x_3368_ = v_b_3364_;
v_isShared_3369_ = v_isSharedCheck_3407_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_snd_3366_);
lean_dec(v_b_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3407_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3406_; 
v_fst_3370_ = lean_ctor_get(v_snd_3366_, 0);
v_snd_3371_ = lean_ctor_get(v_snd_3366_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_snd_3366_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3373_ = v_snd_3366_;
v_isShared_3374_ = v_isSharedCheck_3406_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3370_);
lean_dec(v_snd_3366_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3406_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_a_3375_; lean_object* v_p_3376_; lean_object* v___x_3377_; lean_object* v_a_3379_; lean_object* v_b_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v_a_3375_ = lean_array_uget(v_as_3361_, v_i_3363_);
v_p_3376_ = lean_ctor_get(v_a_3375_, 0);
v___x_3377_ = lean_box(0);
v_b_3386_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3376_, v_x_3360_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3388_ = lean_int_dec_eq(v_b_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3390_; 
lean_inc(v_a_3375_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v_a_3375_);
lean_ctor_set(v___x_3368_, 0, v_b_3386_);
v___x_3390_ = v___x_3368_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_b_3386_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_a_3375_);
v___x_3390_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3398_; 
v_isSharedCheck_3398_ = !lean_is_exclusive(v_a_3375_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3399_ = lean_ctor_get(v_a_3375_, 1);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_a_3375_, 0);
lean_dec(v_unused_3400_);
v___x_3392_ = v_a_3375_;
v_isShared_3393_ = v_isSharedCheck_3398_;
goto v_resetjp_3391_;
}
else
{
lean_dec(v_a_3375_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3398_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_todo_3394_; lean_object* v___x_3396_; 
v_todo_3394_ = lean_array_push(v_snd_3371_, v___x_3390_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v_todo_3394_);
lean_ctor_set(v___x_3392_, 0, v_fst_3370_);
v___x_3396_ = v___x_3392_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_fst_3370_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_todo_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
v_a_3379_ = v___x_3396_;
goto v___jp_3378_;
}
}
}
}
else
{
lean_object* v_cs_x27_3402_; lean_object* v___x_3404_; 
lean_dec(v_b_3386_);
v_cs_x27_3402_ = l_Lean_PersistentArray_push___redArg(v_fst_3370_, v_a_3375_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v_snd_3371_);
lean_ctor_set(v___x_3368_, 0, v_cs_x27_3402_);
v___x_3404_ = v___x_3368_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_cs_x27_3402_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_snd_3371_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
v_a_3379_ = v___x_3404_;
goto v___jp_3378_;
}
}
v___jp_3378_:
{
lean_object* v___x_3381_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v_a_3379_);
lean_ctor_set(v___x_3373_, 0, v___x_3377_);
v___x_3381_ = v___x_3373_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_a_3379_);
v___x_3381_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = ((size_t)1ULL);
v___x_3383_ = lean_usize_add(v_i_3363_, v___x_3382_);
v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3360_, v_as_3361_, v_sz_3362_, v___x_3383_, v___x_3381_);
return v___x_3384_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3409_, lean_object* v_as_3410_, lean_object* v_sz_3411_, lean_object* v_i_3412_, lean_object* v_b_3413_){
_start:
{
size_t v_sz_boxed_3414_; size_t v_i_boxed_3415_; lean_object* v_res_3416_; 
v_sz_boxed_3414_ = lean_unbox_usize(v_sz_3411_);
lean_dec(v_sz_3411_);
v_i_boxed_3415_ = lean_unbox_usize(v_i_3412_);
lean_dec(v_i_3412_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3409_, v_as_3410_, v_sz_boxed_3414_, v_i_boxed_3415_, v_b_3413_);
lean_dec_ref(v_as_3410_);
lean_dec(v_x_3409_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3417_, lean_object* v_as_3418_, size_t v_sz_3419_, size_t v_i_3420_, lean_object* v_b_3421_){
_start:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
if (v___x_3422_ == 0)
{
return v_b_3421_;
}
else
{
lean_object* v_snd_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3464_; 
v_snd_3423_ = lean_ctor_get(v_b_3421_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_b_3421_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v_b_3421_, 0);
lean_dec(v_unused_3465_);
v___x_3425_ = v_b_3421_;
v_isShared_3426_ = v_isSharedCheck_3464_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_snd_3423_);
lean_dec(v_b_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3464_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3463_; 
v_fst_3427_ = lean_ctor_get(v_snd_3423_, 0);
v_snd_3428_ = lean_ctor_get(v_snd_3423_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_snd_3423_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3430_ = v_snd_3423_;
v_isShared_3431_ = v_isSharedCheck_3463_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_inc(v_fst_3427_);
lean_dec(v_snd_3423_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3463_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_a_3432_; lean_object* v_p_3433_; lean_object* v___x_3434_; lean_object* v_a_3436_; lean_object* v_b_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_a_3432_ = lean_array_uget(v_as_3418_, v_i_3420_);
v_p_3433_ = lean_ctor_get(v_a_3432_, 0);
v___x_3434_ = lean_box(0);
v_b_3443_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3433_, v_x_3417_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3445_ = lean_int_dec_eq(v_b_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3447_; 
lean_inc(v_a_3432_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v_a_3432_);
lean_ctor_set(v___x_3425_, 0, v_b_3443_);
v___x_3447_ = v___x_3425_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_b_3443_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_a_3432_);
v___x_3447_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_isSharedCheck_3455_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3456_ = lean_ctor_get(v_a_3432_, 1);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_a_3432_, 0);
lean_dec(v_unused_3457_);
v___x_3449_ = v_a_3432_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v_a_3432_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_todo_3451_; lean_object* v___x_3453_; 
v_todo_3451_ = lean_array_push(v_snd_3428_, v___x_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v_todo_3451_);
lean_ctor_set(v___x_3449_, 0, v_fst_3427_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3427_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_todo_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
v_a_3436_ = v___x_3453_;
goto v___jp_3435_;
}
}
}
}
else
{
lean_object* v_cs_x27_3459_; lean_object* v___x_3461_; 
lean_dec(v_b_3443_);
v_cs_x27_3459_ = l_Lean_PersistentArray_push___redArg(v_fst_3427_, v_a_3432_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v_snd_3428_);
lean_ctor_set(v___x_3425_, 0, v_cs_x27_3459_);
v___x_3461_ = v___x_3425_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_cs_x27_3459_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_snd_3428_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v_a_3436_ = v___x_3461_;
goto v___jp_3435_;
}
}
v___jp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_a_3436_);
lean_ctor_set(v___x_3430_, 0, v___x_3434_);
v___x_3438_ = v___x_3430_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_a_3436_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
size_t v___x_3439_; size_t v___x_3440_; 
v___x_3439_ = ((size_t)1ULL);
v___x_3440_ = lean_usize_add(v_i_3420_, v___x_3439_);
v_i_3420_ = v___x_3440_;
v_b_3421_ = v___x_3438_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3466_, lean_object* v_as_3467_, lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_b_3470_){
_start:
{
size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3466_, v_as_3467_, v_sz_boxed_3471_, v_i_boxed_3472_, v_b_3470_);
lean_dec_ref(v_as_3467_);
lean_dec(v_x_3466_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3474_, lean_object* v_as_3475_, size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3479_ == 0)
{
return v_b_3478_;
}
else
{
lean_object* v_snd_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3521_; 
v_snd_3480_ = lean_ctor_get(v_b_3478_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_b_3478_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v_b_3478_, 0);
lean_dec(v_unused_3522_);
v___x_3482_ = v_b_3478_;
v_isShared_3483_ = v_isSharedCheck_3521_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3480_);
lean_dec(v_b_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3521_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3520_; 
v_fst_3484_ = lean_ctor_get(v_snd_3480_, 0);
v_snd_3485_ = lean_ctor_get(v_snd_3480_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_snd_3480_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3487_ = v_snd_3480_;
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_snd_3485_);
lean_inc(v_fst_3484_);
lean_dec(v_snd_3480_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_a_3489_; lean_object* v_p_3490_; lean_object* v___x_3491_; lean_object* v_a_3493_; lean_object* v_b_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_a_3489_ = lean_array_uget(v_as_3475_, v_i_3477_);
v_p_3490_ = lean_ctor_get(v_a_3489_, 0);
v___x_3491_ = lean_box(0);
v_b_3500_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3490_, v_x_3474_);
v___x_3501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3502_ = lean_int_dec_eq(v_b_3500_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3504_; 
lean_inc(v_a_3489_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v_a_3489_);
lean_ctor_set(v___x_3482_, 0, v_b_3500_);
v___x_3504_ = v___x_3482_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_b_3500_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_a_3489_);
v___x_3504_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
v_isSharedCheck_3512_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; lean_object* v_unused_3514_; 
v_unused_3513_ = lean_ctor_get(v_a_3489_, 1);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_a_3489_, 0);
lean_dec(v_unused_3514_);
v___x_3506_ = v_a_3489_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_a_3489_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_todo_3508_; lean_object* v___x_3510_; 
v_todo_3508_ = lean_array_push(v_snd_3485_, v___x_3504_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_todo_3508_);
lean_ctor_set(v___x_3506_, 0, v_fst_3484_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_todo_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
v_a_3493_ = v___x_3510_;
goto v___jp_3492_;
}
}
}
}
else
{
lean_object* v_cs_x27_3516_; lean_object* v___x_3518_; 
lean_dec(v_b_3500_);
v_cs_x27_3516_ = l_Lean_PersistentArray_push___redArg(v_fst_3484_, v_a_3489_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v_snd_3485_);
lean_ctor_set(v___x_3482_, 0, v_cs_x27_3516_);
v___x_3518_ = v___x_3482_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_cs_x27_3516_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_snd_3485_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
v_a_3493_ = v___x_3518_;
goto v___jp_3492_;
}
}
v___jp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v_a_3493_);
lean_ctor_set(v___x_3487_, 0, v___x_3491_);
v___x_3495_ = v___x_3487_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_a_3493_);
v___x_3495_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
size_t v___x_3496_; size_t v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3477_, v___x_3496_);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3474_, v_as_3475_, v_sz_3476_, v___x_3497_, v___x_3495_);
return v___x_3498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3523_, lean_object* v_as_3524_, lean_object* v_sz_3525_, lean_object* v_i_3526_, lean_object* v_b_3527_){
_start:
{
size_t v_sz_boxed_3528_; size_t v_i_boxed_3529_; lean_object* v_res_3530_; 
v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3525_);
lean_dec(v_sz_3525_);
v_i_boxed_3529_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3523_, v_as_3524_, v_sz_boxed_3528_, v_i_boxed_3529_, v_b_3527_);
lean_dec_ref(v_as_3524_);
lean_dec(v_x_3523_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3531_, lean_object* v_x_3532_, lean_object* v_n_3533_, lean_object* v_b_3534_){
_start:
{
if (lean_obj_tag(v_n_3533_) == 0)
{
lean_object* v_cs_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; size_t v_sz_3538_; size_t v___x_3539_; lean_object* v___x_3540_; lean_object* v_fst_3541_; 
v_cs_3535_ = lean_ctor_get(v_n_3533_, 0);
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_b_3534_);
v_sz_3538_ = lean_array_size(v_cs_3535_);
v___x_3539_ = ((size_t)0ULL);
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3531_, v_x_3532_, v_cs_3535_, v_sz_3538_, v___x_3539_, v___x_3537_);
v_fst_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_fst_3541_);
if (lean_obj_tag(v_fst_3541_) == 0)
{
lean_object* v_snd_3542_; lean_object* v___x_3543_; 
v_snd_3542_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_snd_3542_);
lean_dec_ref(v___x_3540_);
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v_snd_3542_);
return v___x_3543_;
}
else
{
lean_object* v_val_3544_; 
lean_dec_ref(v___x_3540_);
v_val_3544_ = lean_ctor_get(v_fst_3541_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v_fst_3541_, 1);
return v_val_3544_;
}
}
else
{
lean_object* v_vs_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; size_t v_sz_3548_; size_t v___x_3549_; lean_object* v___x_3550_; lean_object* v_fst_3551_; 
v_vs_3545_ = lean_ctor_get(v_n_3533_, 0);
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v_b_3534_);
v_sz_3548_ = lean_array_size(v_vs_3545_);
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3532_, v_vs_3545_, v_sz_3548_, v___x_3549_, v___x_3547_);
v_fst_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_fst_3551_);
if (lean_obj_tag(v_fst_3551_) == 0)
{
lean_object* v_snd_3552_; lean_object* v___x_3553_; 
v_snd_3552_ = lean_ctor_get(v___x_3550_, 1);
lean_inc(v_snd_3552_);
lean_dec_ref(v___x_3550_);
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_snd_3552_);
return v___x_3553_;
}
else
{
lean_object* v_val_3554_; 
lean_dec_ref(v___x_3550_);
v_val_3554_ = lean_ctor_get(v_fst_3551_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_fst_3551_, 1);
return v_val_3554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3555_, lean_object* v_x_3556_, lean_object* v_as_3557_, size_t v_sz_3558_, size_t v_i_3559_, lean_object* v_b_3560_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_usize_dec_lt(v_i_3559_, v_sz_3558_);
if (v___x_3561_ == 0)
{
return v_b_3560_;
}
else
{
lean_object* v_snd_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3580_; 
v_snd_3562_ = lean_ctor_get(v_b_3560_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_b_3560_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_b_3560_, 0);
lean_dec(v_unused_3581_);
v___x_3564_ = v_b_3560_;
v_isShared_3565_ = v_isSharedCheck_3580_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_snd_3562_);
lean_dec(v_b_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3580_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_a_3566_; lean_object* v___x_3567_; 
v_a_3566_ = lean_array_uget_borrowed(v_as_3557_, v_i_3559_);
lean_inc(v_snd_3562_);
v___x_3567_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3555_, v_x_3556_, v_a_3566_, v_snd_3562_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3568_);
v___x_3570_ = v___x_3564_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_snd_3562_);
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
lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_dec(v_snd_3562_);
v_a_3572_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3573_ = lean_box(0);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v_a_3572_);
lean_ctor_set(v___x_3564_, 0, v___x_3573_);
v___x_3575_ = v___x_3564_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_a_3572_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
size_t v___x_3576_; size_t v___x_3577_; 
v___x_3576_ = ((size_t)1ULL);
v___x_3577_ = lean_usize_add(v_i_3559_, v___x_3576_);
v_i_3559_ = v___x_3577_;
v_b_3560_ = v___x_3575_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3582_, lean_object* v_x_3583_, lean_object* v_as_3584_, lean_object* v_sz_3585_, lean_object* v_i_3586_, lean_object* v_b_3587_){
_start:
{
size_t v_sz_boxed_3588_; size_t v_i_boxed_3589_; lean_object* v_res_3590_; 
v_sz_boxed_3588_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v_i_boxed_3589_ = lean_unbox_usize(v_i_3586_);
lean_dec(v_i_3586_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3582_, v_x_3583_, v_as_3584_, v_sz_boxed_3588_, v_i_boxed_3589_, v_b_3587_);
lean_dec_ref(v_as_3584_);
lean_dec(v_x_3583_);
lean_dec_ref(v_init_3582_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3591_, lean_object* v_x_3592_, lean_object* v_n_3593_, lean_object* v_b_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3591_, v_x_3592_, v_n_3593_, v_b_3594_);
lean_dec_ref(v_n_3593_);
lean_dec(v_x_3592_);
lean_dec_ref(v_init_3591_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3596_, lean_object* v_t_3597_, lean_object* v_init_3598_){
_start:
{
lean_object* v_root_3599_; lean_object* v_tail_3600_; lean_object* v___x_3601_; 
v_root_3599_ = lean_ctor_get(v_t_3597_, 0);
v_tail_3600_ = lean_ctor_get(v_t_3597_, 1);
lean_inc_ref(v_init_3598_);
v___x_3601_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3598_, v_x_3596_, v_root_3599_, v_init_3598_);
lean_dec_ref(v_init_3598_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
return v_a_3602_;
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; size_t v_sz_3606_; size_t v___x_3607_; lean_object* v___x_3608_; lean_object* v_fst_3609_; 
v_a_3603_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3601_, 1);
v___x_3604_ = lean_box(0);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
lean_ctor_set(v___x_3605_, 1, v_a_3603_);
v_sz_3606_ = lean_array_size(v_tail_3600_);
v___x_3607_ = ((size_t)0ULL);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3596_, v_tail_3600_, v_sz_3606_, v___x_3607_, v___x_3605_);
v_fst_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_fst_3609_);
if (lean_obj_tag(v_fst_3609_) == 0)
{
lean_object* v_snd_3610_; 
v_snd_3610_ = lean_ctor_get(v___x_3608_, 1);
lean_inc(v_snd_3610_);
lean_dec_ref(v___x_3608_);
return v_snd_3610_;
}
else
{
lean_object* v_val_3611_; 
lean_dec_ref(v___x_3608_);
v_val_3611_ = lean_ctor_get(v_fst_3609_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_fst_3609_, 1);
return v_val_3611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3612_, lean_object* v_t_3613_, lean_object* v_init_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3612_, v_t_3613_, v_init_3614_);
lean_dec_ref(v_t_3613_);
lean_dec(v_x_3612_);
return v_res_3615_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_unsigned_to_nat(32u);
v___x_3617_ = lean_mk_empty_array_with_capacity(v___x_3616_);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v_cs_x27_3624_; 
v___x_3619_ = ((size_t)5ULL);
v___x_3620_ = lean_unsigned_to_nat(0u);
v___x_3621_ = lean_unsigned_to_nat(32u);
v___x_3622_ = lean_mk_empty_array_with_capacity(v___x_3621_);
v___x_3623_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3624_, 0, v___x_3623_);
lean_ctor_set(v_cs_x27_3624_, 1, v___x_3622_);
lean_ctor_set(v_cs_x27_3624_, 2, v___x_3620_);
lean_ctor_set(v_cs_x27_3624_, 3, v___x_3620_);
lean_ctor_set_usize(v_cs_x27_3624_, 4, v___x_3619_);
return v_cs_x27_3624_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3627_; lean_object* v_cs_x27_3628_; lean_object* v___x_3629_; 
v_todo_3627_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3628_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v_cs_x27_3628_);
lean_ctor_set(v___x_3629_, 1, v_todo_3627_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3630_, lean_object* v_cs_3631_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_fst_3634_; lean_object* v_snd_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v___x_3632_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3633_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3630_, v_cs_3631_, v___x_3632_);
v_fst_3634_ = lean_ctor_get(v___x_3633_, 0);
v_snd_3635_ = lean_ctor_get(v___x_3633_, 1);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3633_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3635_);
lean_inc(v_fst_3634_);
lean_dec(v___x_3633_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_fst_3634_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_snd_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3643_, lean_object* v_cs_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3643_, v_cs_3644_);
lean_dec_ref(v_cs_3644_);
lean_dec(v_x_3643_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3646_, lean_object* v_cs_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3646_, v_cs_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3649_, lean_object* v_cs_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3649_, v_cs_3650_);
lean_dec_ref(v_cs_3650_);
lean_dec(v_x_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3652_, lean_object* v_y_3653_, lean_object* v_fst_3654_, lean_object* v_s_3655_){
_start:
{
lean_object* v_structs_3656_; lean_object* v_typeIdOf_3657_; lean_object* v_exprToStructId_3658_; lean_object* v_exprToStructIdEntries_3659_; lean_object* v_forbiddenNatModules_3660_; lean_object* v_natStructs_3661_; lean_object* v_natTypeIdOf_3662_; lean_object* v_exprToNatStructId_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v_structs_3656_ = lean_ctor_get(v_s_3655_, 0);
v_typeIdOf_3657_ = lean_ctor_get(v_s_3655_, 1);
v_exprToStructId_3658_ = lean_ctor_get(v_s_3655_, 2);
v_exprToStructIdEntries_3659_ = lean_ctor_get(v_s_3655_, 3);
v_forbiddenNatModules_3660_ = lean_ctor_get(v_s_3655_, 4);
v_natStructs_3661_ = lean_ctor_get(v_s_3655_, 5);
v_natTypeIdOf_3662_ = lean_ctor_get(v_s_3655_, 6);
v_exprToNatStructId_3663_ = lean_ctor_get(v_s_3655_, 7);
v___x_3664_ = lean_array_get_size(v_structs_3656_);
v___x_3665_ = lean_nat_dec_lt(v_a_3652_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_dec_ref(v_fst_3654_);
return v_s_3655_;
}
else
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3727_; 
lean_inc_ref(v_exprToNatStructId_3663_);
lean_inc_ref(v_natTypeIdOf_3662_);
lean_inc_ref(v_natStructs_3661_);
lean_inc_ref(v_forbiddenNatModules_3660_);
lean_inc_ref(v_exprToStructIdEntries_3659_);
lean_inc_ref(v_exprToStructId_3658_);
lean_inc_ref(v_typeIdOf_3657_);
lean_inc_ref(v_structs_3656_);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_s_3655_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; 
v_unused_3728_ = lean_ctor_get(v_s_3655_, 7);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_s_3655_, 6);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_s_3655_, 5);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_s_3655_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_s_3655_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_s_3655_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_s_3655_, 1);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_s_3655_, 0);
lean_dec(v_unused_3735_);
v___x_3667_ = v_s_3655_;
v_isShared_3668_ = v_isSharedCheck_3727_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v_s_3655_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3727_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_v_3669_; lean_object* v_id_3670_; lean_object* v_ringId_x3f_3671_; lean_object* v_type_3672_; lean_object* v_u_3673_; lean_object* v_intModuleInst_3674_; lean_object* v_leInst_x3f_3675_; lean_object* v_ltInst_x3f_3676_; lean_object* v_lawfulOrderLTInst_x3f_3677_; lean_object* v_isPreorderInst_x3f_3678_; lean_object* v_orderedAddInst_x3f_3679_; lean_object* v_isLinearInst_x3f_3680_; lean_object* v_noNatDivInst_x3f_3681_; lean_object* v_ringInst_x3f_3682_; lean_object* v_commRingInst_x3f_3683_; lean_object* v_orderedRingInst_x3f_3684_; lean_object* v_fieldInst_x3f_3685_; lean_object* v_charInst_x3f_3686_; lean_object* v_zero_3687_; lean_object* v_ofNatZero_3688_; lean_object* v_one_x3f_3689_; lean_object* v_leFn_x3f_3690_; lean_object* v_ltFn_x3f_3691_; lean_object* v_addFn_3692_; lean_object* v_zsmulFn_3693_; lean_object* v_nsmulFn_3694_; lean_object* v_zsmulFn_x3f_3695_; lean_object* v_nsmulFn_x3f_3696_; lean_object* v_homomulFn_x3f_3697_; lean_object* v_subFn_3698_; lean_object* v_negFn_3699_; lean_object* v_vars_3700_; lean_object* v_varMap_3701_; lean_object* v_lowers_3702_; lean_object* v_uppers_3703_; lean_object* v_diseqs_3704_; lean_object* v_assignment_3705_; uint8_t v_caseSplits_3706_; lean_object* v_conflict_x3f_3707_; lean_object* v_diseqSplits_3708_; lean_object* v_elimEqs_3709_; lean_object* v_elimStack_3710_; lean_object* v_occurs_3711_; lean_object* v_ignored_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3726_; 
v_v_3669_ = lean_array_fget(v_structs_3656_, v_a_3652_);
v_id_3670_ = lean_ctor_get(v_v_3669_, 0);
v_ringId_x3f_3671_ = lean_ctor_get(v_v_3669_, 1);
v_type_3672_ = lean_ctor_get(v_v_3669_, 2);
v_u_3673_ = lean_ctor_get(v_v_3669_, 3);
v_intModuleInst_3674_ = lean_ctor_get(v_v_3669_, 4);
v_leInst_x3f_3675_ = lean_ctor_get(v_v_3669_, 5);
v_ltInst_x3f_3676_ = lean_ctor_get(v_v_3669_, 6);
v_lawfulOrderLTInst_x3f_3677_ = lean_ctor_get(v_v_3669_, 7);
v_isPreorderInst_x3f_3678_ = lean_ctor_get(v_v_3669_, 8);
v_orderedAddInst_x3f_3679_ = lean_ctor_get(v_v_3669_, 9);
v_isLinearInst_x3f_3680_ = lean_ctor_get(v_v_3669_, 10);
v_noNatDivInst_x3f_3681_ = lean_ctor_get(v_v_3669_, 11);
v_ringInst_x3f_3682_ = lean_ctor_get(v_v_3669_, 12);
v_commRingInst_x3f_3683_ = lean_ctor_get(v_v_3669_, 13);
v_orderedRingInst_x3f_3684_ = lean_ctor_get(v_v_3669_, 14);
v_fieldInst_x3f_3685_ = lean_ctor_get(v_v_3669_, 15);
v_charInst_x3f_3686_ = lean_ctor_get(v_v_3669_, 16);
v_zero_3687_ = lean_ctor_get(v_v_3669_, 17);
v_ofNatZero_3688_ = lean_ctor_get(v_v_3669_, 18);
v_one_x3f_3689_ = lean_ctor_get(v_v_3669_, 19);
v_leFn_x3f_3690_ = lean_ctor_get(v_v_3669_, 20);
v_ltFn_x3f_3691_ = lean_ctor_get(v_v_3669_, 21);
v_addFn_3692_ = lean_ctor_get(v_v_3669_, 22);
v_zsmulFn_3693_ = lean_ctor_get(v_v_3669_, 23);
v_nsmulFn_3694_ = lean_ctor_get(v_v_3669_, 24);
v_zsmulFn_x3f_3695_ = lean_ctor_get(v_v_3669_, 25);
v_nsmulFn_x3f_3696_ = lean_ctor_get(v_v_3669_, 26);
v_homomulFn_x3f_3697_ = lean_ctor_get(v_v_3669_, 27);
v_subFn_3698_ = lean_ctor_get(v_v_3669_, 28);
v_negFn_3699_ = lean_ctor_get(v_v_3669_, 29);
v_vars_3700_ = lean_ctor_get(v_v_3669_, 30);
v_varMap_3701_ = lean_ctor_get(v_v_3669_, 31);
v_lowers_3702_ = lean_ctor_get(v_v_3669_, 32);
v_uppers_3703_ = lean_ctor_get(v_v_3669_, 33);
v_diseqs_3704_ = lean_ctor_get(v_v_3669_, 34);
v_assignment_3705_ = lean_ctor_get(v_v_3669_, 35);
v_caseSplits_3706_ = lean_ctor_get_uint8(v_v_3669_, sizeof(void*)*42);
v_conflict_x3f_3707_ = lean_ctor_get(v_v_3669_, 36);
v_diseqSplits_3708_ = lean_ctor_get(v_v_3669_, 37);
v_elimEqs_3709_ = lean_ctor_get(v_v_3669_, 38);
v_elimStack_3710_ = lean_ctor_get(v_v_3669_, 39);
v_occurs_3711_ = lean_ctor_get(v_v_3669_, 40);
v_ignored_3712_ = lean_ctor_get(v_v_3669_, 41);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_v_3669_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3714_ = v_v_3669_;
v_isShared_3715_ = v_isSharedCheck_3726_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_ignored_3712_);
lean_inc(v_occurs_3711_);
lean_inc(v_elimStack_3710_);
lean_inc(v_elimEqs_3709_);
lean_inc(v_diseqSplits_3708_);
lean_inc(v_conflict_x3f_3707_);
lean_inc(v_assignment_3705_);
lean_inc(v_diseqs_3704_);
lean_inc(v_uppers_3703_);
lean_inc(v_lowers_3702_);
lean_inc(v_varMap_3701_);
lean_inc(v_vars_3700_);
lean_inc(v_negFn_3699_);
lean_inc(v_subFn_3698_);
lean_inc(v_homomulFn_x3f_3697_);
lean_inc(v_nsmulFn_x3f_3696_);
lean_inc(v_zsmulFn_x3f_3695_);
lean_inc(v_nsmulFn_3694_);
lean_inc(v_zsmulFn_3693_);
lean_inc(v_addFn_3692_);
lean_inc(v_ltFn_x3f_3691_);
lean_inc(v_leFn_x3f_3690_);
lean_inc(v_one_x3f_3689_);
lean_inc(v_ofNatZero_3688_);
lean_inc(v_zero_3687_);
lean_inc(v_charInst_x3f_3686_);
lean_inc(v_fieldInst_x3f_3685_);
lean_inc(v_orderedRingInst_x3f_3684_);
lean_inc(v_commRingInst_x3f_3683_);
lean_inc(v_ringInst_x3f_3682_);
lean_inc(v_noNatDivInst_x3f_3681_);
lean_inc(v_isLinearInst_x3f_3680_);
lean_inc(v_orderedAddInst_x3f_3679_);
lean_inc(v_isPreorderInst_x3f_3678_);
lean_inc(v_lawfulOrderLTInst_x3f_3677_);
lean_inc(v_ltInst_x3f_3676_);
lean_inc(v_leInst_x3f_3675_);
lean_inc(v_intModuleInst_3674_);
lean_inc(v_u_3673_);
lean_inc(v_type_3672_);
lean_inc(v_ringId_x3f_3671_);
lean_inc(v_id_3670_);
lean_dec(v_v_3669_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3726_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v_xs_x27_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3716_ = lean_box(0);
v_xs_x27_3717_ = lean_array_fset(v_structs_3656_, v_a_3652_, v___x_3716_);
v___x_3718_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3704_, v_y_3653_, v_fst_3654_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 34, v___x_3718_);
v___x_3720_ = v___x_3714_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_id_3670_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_ringId_x3f_3671_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_type_3672_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_u_3673_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_intModuleInst_3674_);
lean_ctor_set(v_reuseFailAlloc_3725_, 5, v_leInst_x3f_3675_);
lean_ctor_set(v_reuseFailAlloc_3725_, 6, v_ltInst_x3f_3676_);
lean_ctor_set(v_reuseFailAlloc_3725_, 7, v_lawfulOrderLTInst_x3f_3677_);
lean_ctor_set(v_reuseFailAlloc_3725_, 8, v_isPreorderInst_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3725_, 9, v_orderedAddInst_x3f_3679_);
lean_ctor_set(v_reuseFailAlloc_3725_, 10, v_isLinearInst_x3f_3680_);
lean_ctor_set(v_reuseFailAlloc_3725_, 11, v_noNatDivInst_x3f_3681_);
lean_ctor_set(v_reuseFailAlloc_3725_, 12, v_ringInst_x3f_3682_);
lean_ctor_set(v_reuseFailAlloc_3725_, 13, v_commRingInst_x3f_3683_);
lean_ctor_set(v_reuseFailAlloc_3725_, 14, v_orderedRingInst_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3725_, 15, v_fieldInst_x3f_3685_);
lean_ctor_set(v_reuseFailAlloc_3725_, 16, v_charInst_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3725_, 17, v_zero_3687_);
lean_ctor_set(v_reuseFailAlloc_3725_, 18, v_ofNatZero_3688_);
lean_ctor_set(v_reuseFailAlloc_3725_, 19, v_one_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3725_, 20, v_leFn_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3725_, 21, v_ltFn_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3725_, 22, v_addFn_3692_);
lean_ctor_set(v_reuseFailAlloc_3725_, 23, v_zsmulFn_3693_);
lean_ctor_set(v_reuseFailAlloc_3725_, 24, v_nsmulFn_3694_);
lean_ctor_set(v_reuseFailAlloc_3725_, 25, v_zsmulFn_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3725_, 26, v_nsmulFn_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3725_, 27, v_homomulFn_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3725_, 28, v_subFn_3698_);
lean_ctor_set(v_reuseFailAlloc_3725_, 29, v_negFn_3699_);
lean_ctor_set(v_reuseFailAlloc_3725_, 30, v_vars_3700_);
lean_ctor_set(v_reuseFailAlloc_3725_, 31, v_varMap_3701_);
lean_ctor_set(v_reuseFailAlloc_3725_, 32, v_lowers_3702_);
lean_ctor_set(v_reuseFailAlloc_3725_, 33, v_uppers_3703_);
lean_ctor_set(v_reuseFailAlloc_3725_, 34, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3725_, 35, v_assignment_3705_);
lean_ctor_set(v_reuseFailAlloc_3725_, 36, v_conflict_x3f_3707_);
lean_ctor_set(v_reuseFailAlloc_3725_, 37, v_diseqSplits_3708_);
lean_ctor_set(v_reuseFailAlloc_3725_, 38, v_elimEqs_3709_);
lean_ctor_set(v_reuseFailAlloc_3725_, 39, v_elimStack_3710_);
lean_ctor_set(v_reuseFailAlloc_3725_, 40, v_occurs_3711_);
lean_ctor_set(v_reuseFailAlloc_3725_, 41, v_ignored_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*42, v_caseSplits_3706_);
v___x_3720_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_array_fset(v_xs_x27_3717_, v_a_3652_, v___x_3720_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3721_);
v___x_3723_ = v___x_3667_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_typeIdOf_3657_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_exprToStructId_3658_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_exprToStructIdEntries_3659_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_forbiddenNatModules_3660_);
lean_ctor_set(v_reuseFailAlloc_3724_, 5, v_natStructs_3661_);
lean_ctor_set(v_reuseFailAlloc_3724_, 6, v_natTypeIdOf_3662_);
lean_ctor_set(v_reuseFailAlloc_3724_, 7, v_exprToNatStructId_3663_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3736_, lean_object* v_y_3737_, lean_object* v_fst_3738_, lean_object* v_s_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3736_, v_y_3737_, v_fst_3738_, v_s_3739_);
lean_dec(v_y_3737_);
lean_dec(v_a_3736_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3741_, lean_object* v_x_3742_, lean_object* v_c_3743_, lean_object* v_as_3744_, size_t v_sz_3745_, size_t v_i_3746_, lean_object* v_b_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_a_3761_; uint8_t v___x_3765_; 
v___x_3765_ = lean_usize_dec_lt(v_i_3746_, v_sz_3745_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
lean_dec_ref(v_c_3743_);
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_b_3747_);
return v___x_3766_;
}
else
{
lean_object* v_a_3767_; lean_object* v_fst_3768_; lean_object* v_snd_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_dec_ref(v_b_3747_);
v_a_3767_ = lean_array_uget_borrowed(v_as_3744_, v_i_3746_);
v_fst_3768_ = lean_ctor_get(v_a_3767_, 0);
v_snd_3769_ = lean_ctor_get(v_a_3767_, 1);
v___x_3770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_3769_);
lean_inc(v_fst_3768_);
lean_inc_ref(v_c_3743_);
v___x_3771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3741_, v_x_3742_, v_c_3743_, v_fst_3768_, v_snd_3769_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
if (lean_obj_tag(v_a_3772_) == 1)
{
lean_object* v_val_3773_; lean_object* v___x_3774_; 
v_val_3773_ = lean_ctor_get(v_a_3772_, 0);
lean_inc(v_val_3773_);
lean_dec_ref_known(v_a_3772_, 1);
v___x_3774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3773_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref_known(v___x_3774_, 1);
v___x_3775_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3785_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3785_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3785_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_unbox(v_a_3776_);
lean_dec(v_a_3776_);
if (v___x_3780_ == 0)
{
lean_del_object(v___x_3778_);
v_a_3761_ = v___x_3770_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
lean_dec_ref(v_c_3743_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3781_);
v___x_3783_ = v___x_3778_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_c_3743_);
v_a_3786_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3775_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3775_);
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
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_c_3743_);
v_a_3794_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3774_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3774_);
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
lean_object* v___x_3802_; 
lean_dec(v_a_3772_);
v___x_3802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3769_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_dec_ref_known(v___x_3802_, 1);
v_a_3761_ = v___x_3770_;
goto v___jp_3760_;
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_c_3743_);
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
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
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_c_3743_);
v_a_3811_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3771_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3771_);
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
v___jp_3760_:
{
size_t v___x_3762_; size_t v___x_3763_; 
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_add(v_i_3746_, v___x_3762_);
lean_inc_ref(v_a_3761_);
v_i_3746_ = v___x_3763_;
v_b_3747_ = v_a_3761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3819_ = _args[0];
lean_object* v_x_3820_ = _args[1];
lean_object* v_c_3821_ = _args[2];
lean_object* v_as_3822_ = _args[3];
lean_object* v_sz_3823_ = _args[4];
lean_object* v_i_3824_ = _args[5];
lean_object* v_b_3825_ = _args[6];
lean_object* v___y_3826_ = _args[7];
lean_object* v___y_3827_ = _args[8];
lean_object* v___y_3828_ = _args[9];
lean_object* v___y_3829_ = _args[10];
lean_object* v___y_3830_ = _args[11];
lean_object* v___y_3831_ = _args[12];
lean_object* v___y_3832_ = _args[13];
lean_object* v___y_3833_ = _args[14];
lean_object* v___y_3834_ = _args[15];
lean_object* v___y_3835_ = _args[16];
lean_object* v___y_3836_ = _args[17];
lean_object* v___y_3837_ = _args[18];
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3823_);
lean_dec(v_sz_3823_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3824_);
lean_dec(v_i_3824_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3819_, v_x_3820_, v_c_3821_, v_as_3822_, v_sz_boxed_3838_, v_i_boxed_3839_, v_b_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v_as_3822_);
lean_dec(v_x_3820_);
lean_dec(v_a_3819_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3841_, lean_object* v_x_3842_, lean_object* v_c_3843_, lean_object* v_y_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3858_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3917_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3917_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3917_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_unbox(v_a_3859_);
lean_dec(v_a_3859_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; 
lean_del_object(v___x_3861_);
v___x_3864_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___y_3867_; lean_object* v_diseqs_3900_; lean_object* v_size_3901_; uint8_t v___x_3902_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v_diseqs_3900_ = lean_ctor_get(v_a_3865_, 34);
lean_inc_ref(v_diseqs_3900_);
lean_dec(v_a_3865_);
v_size_3901_ = lean_ctor_get(v_diseqs_3900_, 2);
v___x_3902_ = lean_nat_dec_lt(v_y_3844_, v_size_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v_diseqs_3900_);
v___x_3903_ = l_outOfBounds___redArg(v___x_3857_);
v___y_3867_ = v___x_3903_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3857_, v_diseqs_3900_, v_y_3844_);
lean_dec_ref(v_diseqs_3900_);
v___y_3867_ = v___x_3904_;
goto v___jp_3866_;
}
v___jp_3866_:
{
lean_object* v___x_3868_; lean_object* v_fst_3869_; lean_object* v_snd_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3868_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3842_, v___y_3867_);
lean_dec_ref(v___y_3867_);
v_fst_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_fst_3869_);
v_snd_3870_ = lean_ctor_get(v___x_3868_, 1);
lean_inc(v_snd_3870_);
lean_dec_ref(v___x_3868_);
lean_inc(v_a_3845_);
v___f_3871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3871_, 0, v_a_3845_);
lean_closure_set(v___f_3871_, 1, v_y_3844_);
lean_closure_set(v___f_3871_, 2, v_fst_3869_);
v___x_3872_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3873_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3872_, v___f_3871_, v_a_3846_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; size_t v_sz_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
lean_dec_ref_known(v___x_3873_, 1);
v___x_3874_ = lean_box(0);
v___x_3875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3876_ = lean_array_size(v_snd_3870_);
v___x_3877_ = ((size_t)0ULL);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3841_, v_x_3842_, v_c_3843_, v_snd_3870_, v_sz_3876_, v___x_3877_, v___x_3875_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_snd_3870_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3891_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3891_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3891_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_fst_3883_; 
v_fst_3883_ = lean_ctor_get(v_a_3879_, 0);
lean_inc(v_fst_3883_);
lean_dec(v_a_3879_);
if (lean_obj_tag(v_fst_3883_) == 0)
{
lean_object* v___x_3885_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3874_);
v___x_3885_ = v___x_3881_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3874_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
else
{
lean_object* v_val_3887_; lean_object* v___x_3889_; 
v_val_3887_ = lean_ctor_get(v_fst_3883_, 0);
lean_inc(v_val_3887_);
lean_dec_ref_known(v_fst_3883_, 1);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v_val_3887_);
v___x_3889_ = v___x_3881_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_val_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_a_3892_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3878_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3878_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
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
lean_dec(v_snd_3870_);
lean_dec_ref(v_c_3843_);
return v___x_3873_;
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_y_3844_);
lean_dec_ref(v_c_3843_);
v_a_3905_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3864_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3864_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_y_3844_);
lean_dec_ref(v_c_3843_);
v___x_3913_ = lean_box(0);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3913_);
v___x_3915_ = v___x_3861_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
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
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_y_3844_);
lean_dec_ref(v_c_3843_);
v_a_3918_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3858_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3858_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3926_, lean_object* v_x_3927_, lean_object* v_c_3928_, lean_object* v_y_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3926_, v_x_3927_, v_c_3928_, v_y_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec(v_x_3927_);
lean_dec(v_a_3926_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3943_, lean_object* v_x_3944_, lean_object* v_c_3945_, lean_object* v_y_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v___x_3959_; 
lean_inc(v_y_3946_);
lean_inc_ref(v_c_3945_);
lean_inc(v_x_3944_);
lean_inc(v_a_3943_);
v___x_3959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3943_, v_x_3944_, v_c_3945_, v_y_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref_known(v___x_3959_, 1);
lean_inc(v_y_3946_);
lean_inc_ref(v_c_3945_);
lean_inc(v_x_3944_);
lean_inc(v_a_3943_);
v___x_3960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3943_, v_x_3944_, v_c_3945_, v_y_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec_ref_known(v___x_3960_, 1);
v___x_3961_ = lean_nat_to_int(v_a_3943_);
v___x_3962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3961_, v_x_3944_, v_c_3945_, v_y_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
lean_dec(v_x_3944_);
lean_dec(v___x_3961_);
return v___x_3962_;
}
else
{
lean_dec(v_y_3946_);
lean_dec_ref(v_c_3945_);
lean_dec(v_x_3944_);
lean_dec(v_a_3943_);
return v___x_3960_;
}
}
else
{
lean_dec(v_y_3946_);
lean_dec_ref(v_c_3945_);
lean_dec(v_x_3944_);
lean_dec(v_a_3943_);
return v___x_3959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3963_, lean_object* v_x_3964_, lean_object* v_c_3965_, lean_object* v_y_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3963_, v_x_3964_, v_c_3965_, v_y_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec(v_a_3967_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3980_, lean_object* v_x_3981_, lean_object* v_s_3982_){
_start:
{
lean_object* v_structs_3983_; lean_object* v_typeIdOf_3984_; lean_object* v_exprToStructId_3985_; lean_object* v_exprToStructIdEntries_3986_; lean_object* v_forbiddenNatModules_3987_; lean_object* v_natStructs_3988_; lean_object* v_natTypeIdOf_3989_; lean_object* v_exprToNatStructId_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_structs_3983_ = lean_ctor_get(v_s_3982_, 0);
v_typeIdOf_3984_ = lean_ctor_get(v_s_3982_, 1);
v_exprToStructId_3985_ = lean_ctor_get(v_s_3982_, 2);
v_exprToStructIdEntries_3986_ = lean_ctor_get(v_s_3982_, 3);
v_forbiddenNatModules_3987_ = lean_ctor_get(v_s_3982_, 4);
v_natStructs_3988_ = lean_ctor_get(v_s_3982_, 5);
v_natTypeIdOf_3989_ = lean_ctor_get(v_s_3982_, 6);
v_exprToNatStructId_3990_ = lean_ctor_get(v_s_3982_, 7);
v___x_3991_ = lean_array_get_size(v_structs_3983_);
v___x_3992_ = lean_nat_dec_lt(v_a_3980_, v___x_3991_);
if (v___x_3992_ == 0)
{
return v_s_3982_;
}
else
{
lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4055_; 
lean_inc_ref(v_exprToNatStructId_3990_);
lean_inc_ref(v_natTypeIdOf_3989_);
lean_inc_ref(v_natStructs_3988_);
lean_inc_ref(v_forbiddenNatModules_3987_);
lean_inc_ref(v_exprToStructIdEntries_3986_);
lean_inc_ref(v_exprToStructId_3985_);
lean_inc_ref(v_typeIdOf_3984_);
lean_inc_ref(v_structs_3983_);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_s_3982_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; lean_object* v_unused_4057_; lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; lean_object* v_unused_4063_; 
v_unused_4056_ = lean_ctor_get(v_s_3982_, 7);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_s_3982_, 6);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_s_3982_, 5);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_s_3982_, 4);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_s_3982_, 3);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_s_3982_, 2);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_s_3982_, 1);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_s_3982_, 0);
lean_dec(v_unused_4063_);
v___x_3994_ = v_s_3982_;
v_isShared_3995_ = v_isSharedCheck_4055_;
goto v_resetjp_3993_;
}
else
{
lean_dec(v_s_3982_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4055_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v_v_3996_; lean_object* v_id_3997_; lean_object* v_ringId_x3f_3998_; lean_object* v_type_3999_; lean_object* v_u_4000_; lean_object* v_intModuleInst_4001_; lean_object* v_leInst_x3f_4002_; lean_object* v_ltInst_x3f_4003_; lean_object* v_lawfulOrderLTInst_x3f_4004_; lean_object* v_isPreorderInst_x3f_4005_; lean_object* v_orderedAddInst_x3f_4006_; lean_object* v_isLinearInst_x3f_4007_; lean_object* v_noNatDivInst_x3f_4008_; lean_object* v_ringInst_x3f_4009_; lean_object* v_commRingInst_x3f_4010_; lean_object* v_orderedRingInst_x3f_4011_; lean_object* v_fieldInst_x3f_4012_; lean_object* v_charInst_x3f_4013_; lean_object* v_zero_4014_; lean_object* v_ofNatZero_4015_; lean_object* v_one_x3f_4016_; lean_object* v_leFn_x3f_4017_; lean_object* v_ltFn_x3f_4018_; lean_object* v_addFn_4019_; lean_object* v_zsmulFn_4020_; lean_object* v_nsmulFn_4021_; lean_object* v_zsmulFn_x3f_4022_; lean_object* v_nsmulFn_x3f_4023_; lean_object* v_homomulFn_x3f_4024_; lean_object* v_subFn_4025_; lean_object* v_negFn_4026_; lean_object* v_vars_4027_; lean_object* v_varMap_4028_; lean_object* v_lowers_4029_; lean_object* v_uppers_4030_; lean_object* v_diseqs_4031_; lean_object* v_assignment_4032_; uint8_t v_caseSplits_4033_; lean_object* v_conflict_x3f_4034_; lean_object* v_diseqSplits_4035_; lean_object* v_elimEqs_4036_; lean_object* v_elimStack_4037_; lean_object* v_occurs_4038_; lean_object* v_ignored_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4054_; 
v_v_3996_ = lean_array_fget(v_structs_3983_, v_a_3980_);
v_id_3997_ = lean_ctor_get(v_v_3996_, 0);
v_ringId_x3f_3998_ = lean_ctor_get(v_v_3996_, 1);
v_type_3999_ = lean_ctor_get(v_v_3996_, 2);
v_u_4000_ = lean_ctor_get(v_v_3996_, 3);
v_intModuleInst_4001_ = lean_ctor_get(v_v_3996_, 4);
v_leInst_x3f_4002_ = lean_ctor_get(v_v_3996_, 5);
v_ltInst_x3f_4003_ = lean_ctor_get(v_v_3996_, 6);
v_lawfulOrderLTInst_x3f_4004_ = lean_ctor_get(v_v_3996_, 7);
v_isPreorderInst_x3f_4005_ = lean_ctor_get(v_v_3996_, 8);
v_orderedAddInst_x3f_4006_ = lean_ctor_get(v_v_3996_, 9);
v_isLinearInst_x3f_4007_ = lean_ctor_get(v_v_3996_, 10);
v_noNatDivInst_x3f_4008_ = lean_ctor_get(v_v_3996_, 11);
v_ringInst_x3f_4009_ = lean_ctor_get(v_v_3996_, 12);
v_commRingInst_x3f_4010_ = lean_ctor_get(v_v_3996_, 13);
v_orderedRingInst_x3f_4011_ = lean_ctor_get(v_v_3996_, 14);
v_fieldInst_x3f_4012_ = lean_ctor_get(v_v_3996_, 15);
v_charInst_x3f_4013_ = lean_ctor_get(v_v_3996_, 16);
v_zero_4014_ = lean_ctor_get(v_v_3996_, 17);
v_ofNatZero_4015_ = lean_ctor_get(v_v_3996_, 18);
v_one_x3f_4016_ = lean_ctor_get(v_v_3996_, 19);
v_leFn_x3f_4017_ = lean_ctor_get(v_v_3996_, 20);
v_ltFn_x3f_4018_ = lean_ctor_get(v_v_3996_, 21);
v_addFn_4019_ = lean_ctor_get(v_v_3996_, 22);
v_zsmulFn_4020_ = lean_ctor_get(v_v_3996_, 23);
v_nsmulFn_4021_ = lean_ctor_get(v_v_3996_, 24);
v_zsmulFn_x3f_4022_ = lean_ctor_get(v_v_3996_, 25);
v_nsmulFn_x3f_4023_ = lean_ctor_get(v_v_3996_, 26);
v_homomulFn_x3f_4024_ = lean_ctor_get(v_v_3996_, 27);
v_subFn_4025_ = lean_ctor_get(v_v_3996_, 28);
v_negFn_4026_ = lean_ctor_get(v_v_3996_, 29);
v_vars_4027_ = lean_ctor_get(v_v_3996_, 30);
v_varMap_4028_ = lean_ctor_get(v_v_3996_, 31);
v_lowers_4029_ = lean_ctor_get(v_v_3996_, 32);
v_uppers_4030_ = lean_ctor_get(v_v_3996_, 33);
v_diseqs_4031_ = lean_ctor_get(v_v_3996_, 34);
v_assignment_4032_ = lean_ctor_get(v_v_3996_, 35);
v_caseSplits_4033_ = lean_ctor_get_uint8(v_v_3996_, sizeof(void*)*42);
v_conflict_x3f_4034_ = lean_ctor_get(v_v_3996_, 36);
v_diseqSplits_4035_ = lean_ctor_get(v_v_3996_, 37);
v_elimEqs_4036_ = lean_ctor_get(v_v_3996_, 38);
v_elimStack_4037_ = lean_ctor_get(v_v_3996_, 39);
v_occurs_4038_ = lean_ctor_get(v_v_3996_, 40);
v_ignored_4039_ = lean_ctor_get(v_v_3996_, 41);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_v_3996_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4041_ = v_v_3996_;
v_isShared_4042_ = v_isSharedCheck_4054_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_ignored_4039_);
lean_inc(v_occurs_4038_);
lean_inc(v_elimStack_4037_);
lean_inc(v_elimEqs_4036_);
lean_inc(v_diseqSplits_4035_);
lean_inc(v_conflict_x3f_4034_);
lean_inc(v_assignment_4032_);
lean_inc(v_diseqs_4031_);
lean_inc(v_uppers_4030_);
lean_inc(v_lowers_4029_);
lean_inc(v_varMap_4028_);
lean_inc(v_vars_4027_);
lean_inc(v_negFn_4026_);
lean_inc(v_subFn_4025_);
lean_inc(v_homomulFn_x3f_4024_);
lean_inc(v_nsmulFn_x3f_4023_);
lean_inc(v_zsmulFn_x3f_4022_);
lean_inc(v_nsmulFn_4021_);
lean_inc(v_zsmulFn_4020_);
lean_inc(v_addFn_4019_);
lean_inc(v_ltFn_x3f_4018_);
lean_inc(v_leFn_x3f_4017_);
lean_inc(v_one_x3f_4016_);
lean_inc(v_ofNatZero_4015_);
lean_inc(v_zero_4014_);
lean_inc(v_charInst_x3f_4013_);
lean_inc(v_fieldInst_x3f_4012_);
lean_inc(v_orderedRingInst_x3f_4011_);
lean_inc(v_commRingInst_x3f_4010_);
lean_inc(v_ringInst_x3f_4009_);
lean_inc(v_noNatDivInst_x3f_4008_);
lean_inc(v_isLinearInst_x3f_4007_);
lean_inc(v_orderedAddInst_x3f_4006_);
lean_inc(v_isPreorderInst_x3f_4005_);
lean_inc(v_lawfulOrderLTInst_x3f_4004_);
lean_inc(v_ltInst_x3f_4003_);
lean_inc(v_leInst_x3f_4002_);
lean_inc(v_intModuleInst_4001_);
lean_inc(v_u_4000_);
lean_inc(v_type_3999_);
lean_inc(v_ringId_x3f_3998_);
lean_inc(v_id_3997_);
lean_dec(v_v_3996_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4054_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; lean_object* v_xs_x27_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4043_ = lean_box(0);
v_xs_x27_4044_ = lean_array_fset(v_structs_3983_, v_a_3980_, v___x_4043_);
v___x_4045_ = lean_box(1);
v___x_4046_ = l_Lean_PersistentArray_set___redArg(v_occurs_4038_, v_x_3981_, v___x_4045_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 40, v___x_4046_);
v___x_4048_ = v___x_4041_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_id_3997_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_ringId_x3f_3998_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_type_3999_);
lean_ctor_set(v_reuseFailAlloc_4053_, 3, v_u_4000_);
lean_ctor_set(v_reuseFailAlloc_4053_, 4, v_intModuleInst_4001_);
lean_ctor_set(v_reuseFailAlloc_4053_, 5, v_leInst_x3f_4002_);
lean_ctor_set(v_reuseFailAlloc_4053_, 6, v_ltInst_x3f_4003_);
lean_ctor_set(v_reuseFailAlloc_4053_, 7, v_lawfulOrderLTInst_x3f_4004_);
lean_ctor_set(v_reuseFailAlloc_4053_, 8, v_isPreorderInst_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4053_, 9, v_orderedAddInst_x3f_4006_);
lean_ctor_set(v_reuseFailAlloc_4053_, 10, v_isLinearInst_x3f_4007_);
lean_ctor_set(v_reuseFailAlloc_4053_, 11, v_noNatDivInst_x3f_4008_);
lean_ctor_set(v_reuseFailAlloc_4053_, 12, v_ringInst_x3f_4009_);
lean_ctor_set(v_reuseFailAlloc_4053_, 13, v_commRingInst_x3f_4010_);
lean_ctor_set(v_reuseFailAlloc_4053_, 14, v_orderedRingInst_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4053_, 15, v_fieldInst_x3f_4012_);
lean_ctor_set(v_reuseFailAlloc_4053_, 16, v_charInst_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4053_, 17, v_zero_4014_);
lean_ctor_set(v_reuseFailAlloc_4053_, 18, v_ofNatZero_4015_);
lean_ctor_set(v_reuseFailAlloc_4053_, 19, v_one_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4053_, 20, v_leFn_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4053_, 21, v_ltFn_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4053_, 22, v_addFn_4019_);
lean_ctor_set(v_reuseFailAlloc_4053_, 23, v_zsmulFn_4020_);
lean_ctor_set(v_reuseFailAlloc_4053_, 24, v_nsmulFn_4021_);
lean_ctor_set(v_reuseFailAlloc_4053_, 25, v_zsmulFn_x3f_4022_);
lean_ctor_set(v_reuseFailAlloc_4053_, 26, v_nsmulFn_x3f_4023_);
lean_ctor_set(v_reuseFailAlloc_4053_, 27, v_homomulFn_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4053_, 28, v_subFn_4025_);
lean_ctor_set(v_reuseFailAlloc_4053_, 29, v_negFn_4026_);
lean_ctor_set(v_reuseFailAlloc_4053_, 30, v_vars_4027_);
lean_ctor_set(v_reuseFailAlloc_4053_, 31, v_varMap_4028_);
lean_ctor_set(v_reuseFailAlloc_4053_, 32, v_lowers_4029_);
lean_ctor_set(v_reuseFailAlloc_4053_, 33, v_uppers_4030_);
lean_ctor_set(v_reuseFailAlloc_4053_, 34, v_diseqs_4031_);
lean_ctor_set(v_reuseFailAlloc_4053_, 35, v_assignment_4032_);
lean_ctor_set(v_reuseFailAlloc_4053_, 36, v_conflict_x3f_4034_);
lean_ctor_set(v_reuseFailAlloc_4053_, 37, v_diseqSplits_4035_);
lean_ctor_set(v_reuseFailAlloc_4053_, 38, v_elimEqs_4036_);
lean_ctor_set(v_reuseFailAlloc_4053_, 39, v_elimStack_4037_);
lean_ctor_set(v_reuseFailAlloc_4053_, 40, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4053_, 41, v_ignored_4039_);
lean_ctor_set_uint8(v_reuseFailAlloc_4053_, sizeof(void*)*42, v_caseSplits_4033_);
v___x_4048_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = lean_array_fset(v_xs_x27_4044_, v_a_3980_, v___x_4048_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 0, v___x_4049_);
v___x_4051_ = v___x_3994_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_typeIdOf_3984_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_exprToStructId_3985_);
lean_ctor_set(v_reuseFailAlloc_4052_, 3, v_exprToStructIdEntries_3986_);
lean_ctor_set(v_reuseFailAlloc_4052_, 4, v_forbiddenNatModules_3987_);
lean_ctor_set(v_reuseFailAlloc_4052_, 5, v_natStructs_3988_);
lean_ctor_set(v_reuseFailAlloc_4052_, 6, v_natTypeIdOf_3989_);
lean_ctor_set(v_reuseFailAlloc_4052_, 7, v_exprToNatStructId_3990_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4064_, lean_object* v_x_4065_, lean_object* v_s_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4064_, v_x_4065_, v_s_4066_);
lean_dec(v_x_4065_);
lean_dec(v_a_4064_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4068_, lean_object* v_x_4069_, lean_object* v_c_4070_, lean_object* v_init_4071_, lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
if (lean_obj_tag(v_x_4072_) == 0)
{
lean_object* v_k_4085_; lean_object* v_l_4086_; lean_object* v_r_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_k_4085_ = lean_ctor_get(v_x_4072_, 1);
lean_inc(v_k_4085_);
v_l_4086_ = lean_ctor_get(v_x_4072_, 3);
lean_inc(v_l_4086_);
v_r_4087_ = lean_ctor_get(v_x_4072_, 4);
lean_inc(v_r_4087_);
lean_dec_ref_known(v_x_4072_, 5);
v___x_4088_ = lean_box(0);
lean_inc_ref(v_c_4070_);
lean_inc(v_x_4069_);
lean_inc(v_a_4068_);
v___x_4089_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4068_, v_x_4069_, v_c_4070_, v_init_4071_, v_l_4086_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref_known(v___x_4089_, 1);
lean_inc_ref(v_c_4070_);
lean_inc(v_x_4069_);
lean_inc(v_a_4068_);
v___x_4090_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4068_, v_x_4069_, v_c_4070_, v_k_4085_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_dec_ref_known(v___x_4090_, 1);
v_init_4071_ = v___x_4088_;
v_x_4072_ = v_r_4087_;
goto _start;
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_r_4087_);
lean_dec_ref(v_c_4070_);
lean_dec(v_x_4069_);
lean_dec(v_a_4068_);
v_a_4092_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4090_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4090_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_dec(v_r_4087_);
lean_dec(v_k_4085_);
lean_dec_ref(v_c_4070_);
lean_dec(v_x_4069_);
lean_dec(v_a_4068_);
return v___x_4089_;
}
}
else
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec_ref(v_c_4070_);
lean_dec(v_x_4069_);
lean_dec(v_a_4068_);
v___x_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4100_, 0, v_init_4071_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
return v___x_4101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4102_ = _args[0];
lean_object* v_x_4103_ = _args[1];
lean_object* v_c_4104_ = _args[2];
lean_object* v_init_4105_ = _args[3];
lean_object* v_x_4106_ = _args[4];
lean_object* v___y_4107_ = _args[5];
lean_object* v___y_4108_ = _args[6];
lean_object* v___y_4109_ = _args[7];
lean_object* v___y_4110_ = _args[8];
lean_object* v___y_4111_ = _args[9];
lean_object* v___y_4112_ = _args[10];
lean_object* v___y_4113_ = _args[11];
lean_object* v___y_4114_ = _args[12];
lean_object* v___y_4115_ = _args[13];
lean_object* v___y_4116_ = _args[14];
lean_object* v___y_4117_ = _args[15];
lean_object* v___y_4118_ = _args[16];
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4102_, v_x_4103_, v_c_4104_, v_init_4105_, v_x_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec(v___y_4107_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4120_, lean_object* v_x_4121_, lean_object* v_c_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v___f_4135_; lean_object* v___x_4136_; 
lean_inc(v_x_4121_);
lean_inc(v_a_4123_);
v___f_4135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4135_, 0, v_a_4123_);
lean_closure_set(v___f_4135_, 1, v_x_4121_);
v___x_4136_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___y_4139_; lean_object* v_occurs_4161_; lean_object* v_size_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v_occurs_4161_ = lean_ctor_get(v_a_4137_, 40);
lean_inc_ref(v_occurs_4161_);
lean_dec(v_a_4137_);
v_size_4162_ = lean_ctor_get(v_occurs_4161_, 2);
v___x_4163_ = lean_box(1);
v___x_4164_ = lean_nat_dec_lt(v_x_4121_, v_size_4162_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
lean_dec_ref(v_occurs_4161_);
v___x_4165_ = l_outOfBounds___redArg(v___x_4163_);
v___y_4139_ = v___x_4165_;
goto v___jp_4138_;
}
else
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4163_, v_occurs_4161_, v_x_4121_);
lean_dec_ref(v_occurs_4161_);
v___y_4139_ = v___x_4166_;
goto v___jp_4138_;
}
v___jp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4141_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4140_, v___f_4135_, v_a_4124_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4142_; 
lean_dec_ref_known(v___x_4141_, 1);
lean_inc_ref(v_c_4122_);
lean_inc_n(v_x_4121_, 2);
lean_inc(v_a_4120_);
v___x_4142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4120_, v_x_4121_, v_c_4122_, v_x_4121_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref_known(v___x_4142_, 1);
v___x_4143_ = lean_box(0);
v___x_4144_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4120_, v_x_4121_, v_c_4122_, v___x_4143_, v___y_4139_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v___x_4144_, 0);
lean_dec(v_unused_4152_);
v___x_4146_ = v___x_4144_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_dec(v___x_4144_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4143_);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4143_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
v_a_4153_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4144_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4144_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
lean_dec(v___y_4139_);
lean_dec_ref(v_c_4122_);
lean_dec(v_x_4121_);
lean_dec(v_a_4120_);
return v___x_4142_;
}
}
else
{
lean_dec(v___y_4139_);
lean_dec_ref(v_c_4122_);
lean_dec(v_x_4121_);
lean_dec(v_a_4120_);
return v___x_4141_;
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v___f_4135_);
lean_dec_ref(v_c_4122_);
lean_dec(v_x_4121_);
lean_dec(v_a_4120_);
v_a_4167_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4136_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4136_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4175_, lean_object* v_x_4176_, lean_object* v_c_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4175_, v_x_4176_, v_c_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec(v_a_4178_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_p_4208_; 
v_p_4208_ = lean_ctor_get(v_c_4191_, 0);
if (lean_obj_tag(v_p_4208_) == 1)
{
lean_object* v_k_4209_; lean_object* v_v_4210_; lean_object* v_p_4211_; lean_object* v_y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v_k_4209_ = lean_ctor_get(v_p_4208_, 0);
v_v_4210_ = lean_ctor_get(v_p_4208_, 1);
v_p_4211_ = lean_ctor_get(v_p_4208_, 2);
v___x_4262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4264_ = lean_int_dec_eq(v_k_4209_, v___x_4263_);
if (v___x_4264_ == 0)
{
uint8_t v___x_4265_; 
v___x_4265_ = lean_int_dec_eq(v_k_4209_, v___x_4262_);
if (v___x_4265_ == 0)
{
goto v___jp_4204_;
}
else
{
if (lean_obj_tag(v_p_4211_) == 1)
{
lean_object* v_k_4266_; lean_object* v_v_4267_; lean_object* v_p_4268_; uint8_t v___x_4269_; 
v_k_4266_ = lean_ctor_get(v_p_4211_, 0);
v_v_4267_ = lean_ctor_get(v_p_4211_, 1);
v_p_4268_ = lean_ctor_get(v_p_4211_, 2);
v___x_4269_ = lean_int_dec_eq(v_k_4266_, v___x_4263_);
if (v___x_4269_ == 0)
{
goto v___jp_4204_;
}
else
{
if (lean_obj_tag(v_p_4268_) == 0)
{
v_y_4213_ = v_v_4267_;
v___y_4214_ = v_a_4192_;
v___y_4215_ = v_a_4193_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
v___y_4222_ = v_a_4200_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
goto v___jp_4212_;
}
else
{
goto v___jp_4204_;
}
}
}
else
{
goto v___jp_4204_;
}
}
}
else
{
if (lean_obj_tag(v_p_4211_) == 1)
{
lean_object* v_k_4270_; lean_object* v_v_4271_; lean_object* v_p_4272_; uint8_t v___x_4273_; 
v_k_4270_ = lean_ctor_get(v_p_4211_, 0);
v_v_4271_ = lean_ctor_get(v_p_4211_, 1);
v_p_4272_ = lean_ctor_get(v_p_4211_, 2);
v___x_4273_ = lean_int_dec_eq(v_k_4270_, v___x_4262_);
if (v___x_4273_ == 0)
{
goto v___jp_4204_;
}
else
{
if (lean_obj_tag(v_p_4272_) == 0)
{
v_y_4213_ = v_v_4271_;
v___y_4214_ = v_a_4192_;
v___y_4215_ = v_a_4193_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
v___y_4222_ = v_a_4200_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
goto v___jp_4212_;
}
else
{
goto v___jp_4204_;
}
}
}
else
{
goto v___jp_4204_;
}
}
v___jp_4212_:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4210_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4226_, v_a_4228_, v___y_4215_);
lean_dec(v_a_4228_);
lean_dec(v_a_4226_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4245_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4245_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4245_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_unbox(v_a_4230_);
lean_dec(v_a_4230_);
if (v___x_4234_ == 0)
{
uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4235_ = 1;
v___x_4236_ = lean_box(v___x_4235_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4236_);
v___x_4238_ = v___x_4232_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
else
{
uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4240_ = 0;
v___x_4241_ = lean_box(v___x_4240_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4241_);
v___x_4243_ = v___x_4232_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
return v___x_4229_;
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec(v_a_4226_);
v_a_4246_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4227_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4227_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
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
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
v_a_4254_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4225_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4225_);
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
}
else
{
goto v___jp_4204_;
}
v___jp_4204_:
{
uint8_t v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = 0;
v___x_4206_ = lean_box(v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_c_4274_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4288_){
_start:
{
lean_object* v_p_4290_; 
v_p_4290_ = lean_ctor_get(v_c_4288_, 0);
if (lean_obj_tag(v_p_4290_) == 1)
{
lean_object* v_k_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v_k_4291_ = lean_ctor_get(v_p_4290_, 0);
v___x_4292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4293_ = lean_int_dec_lt(v_k_4291_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4294_, 0, v_c_4288_);
return v___x_4294_;
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4290_);
v___x_4296_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4290_, v___x_4295_);
v___x_4297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4297_, 0, v_c_4288_);
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
}
else
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v_c_4288_);
return v___x_4300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4301_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4304_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec(v_a_4319_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4332_, lean_object* v_snd_4333_, lean_object* v_fst_4334_, lean_object* v_s_4335_){
_start:
{
lean_object* v_structs_4336_; lean_object* v_typeIdOf_4337_; lean_object* v_exprToStructId_4338_; lean_object* v_exprToStructIdEntries_4339_; lean_object* v_forbiddenNatModules_4340_; lean_object* v_natStructs_4341_; lean_object* v_natTypeIdOf_4342_; lean_object* v_exprToNatStructId_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_structs_4336_ = lean_ctor_get(v_s_4335_, 0);
v_typeIdOf_4337_ = lean_ctor_get(v_s_4335_, 1);
v_exprToStructId_4338_ = lean_ctor_get(v_s_4335_, 2);
v_exprToStructIdEntries_4339_ = lean_ctor_get(v_s_4335_, 3);
v_forbiddenNatModules_4340_ = lean_ctor_get(v_s_4335_, 4);
v_natStructs_4341_ = lean_ctor_get(v_s_4335_, 5);
v_natTypeIdOf_4342_ = lean_ctor_get(v_s_4335_, 6);
v_exprToNatStructId_4343_ = lean_ctor_get(v_s_4335_, 7);
v___x_4344_ = lean_array_get_size(v_structs_4336_);
v___x_4345_ = lean_nat_dec_lt(v___y_4332_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec(v_fst_4334_);
lean_dec_ref(v_snd_4333_);
return v_s_4335_;
}
else
{
lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4409_; 
lean_inc_ref(v_exprToNatStructId_4343_);
lean_inc_ref(v_natTypeIdOf_4342_);
lean_inc_ref(v_natStructs_4341_);
lean_inc_ref(v_forbiddenNatModules_4340_);
lean_inc_ref(v_exprToStructIdEntries_4339_);
lean_inc_ref(v_exprToStructId_4338_);
lean_inc_ref(v_typeIdOf_4337_);
lean_inc_ref(v_structs_4336_);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_s_4335_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; lean_object* v_unused_4411_; lean_object* v_unused_4412_; lean_object* v_unused_4413_; lean_object* v_unused_4414_; lean_object* v_unused_4415_; lean_object* v_unused_4416_; lean_object* v_unused_4417_; 
v_unused_4410_ = lean_ctor_get(v_s_4335_, 7);
lean_dec(v_unused_4410_);
v_unused_4411_ = lean_ctor_get(v_s_4335_, 6);
lean_dec(v_unused_4411_);
v_unused_4412_ = lean_ctor_get(v_s_4335_, 5);
lean_dec(v_unused_4412_);
v_unused_4413_ = lean_ctor_get(v_s_4335_, 4);
lean_dec(v_unused_4413_);
v_unused_4414_ = lean_ctor_get(v_s_4335_, 3);
lean_dec(v_unused_4414_);
v_unused_4415_ = lean_ctor_get(v_s_4335_, 2);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v_s_4335_, 1);
lean_dec(v_unused_4416_);
v_unused_4417_ = lean_ctor_get(v_s_4335_, 0);
lean_dec(v_unused_4417_);
v___x_4347_ = v_s_4335_;
v_isShared_4348_ = v_isSharedCheck_4409_;
goto v_resetjp_4346_;
}
else
{
lean_dec(v_s_4335_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4409_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_v_4349_; lean_object* v_id_4350_; lean_object* v_ringId_x3f_4351_; lean_object* v_type_4352_; lean_object* v_u_4353_; lean_object* v_intModuleInst_4354_; lean_object* v_leInst_x3f_4355_; lean_object* v_ltInst_x3f_4356_; lean_object* v_lawfulOrderLTInst_x3f_4357_; lean_object* v_isPreorderInst_x3f_4358_; lean_object* v_orderedAddInst_x3f_4359_; lean_object* v_isLinearInst_x3f_4360_; lean_object* v_noNatDivInst_x3f_4361_; lean_object* v_ringInst_x3f_4362_; lean_object* v_commRingInst_x3f_4363_; lean_object* v_orderedRingInst_x3f_4364_; lean_object* v_fieldInst_x3f_4365_; lean_object* v_charInst_x3f_4366_; lean_object* v_zero_4367_; lean_object* v_ofNatZero_4368_; lean_object* v_one_x3f_4369_; lean_object* v_leFn_x3f_4370_; lean_object* v_ltFn_x3f_4371_; lean_object* v_addFn_4372_; lean_object* v_zsmulFn_4373_; lean_object* v_nsmulFn_4374_; lean_object* v_zsmulFn_x3f_4375_; lean_object* v_nsmulFn_x3f_4376_; lean_object* v_homomulFn_x3f_4377_; lean_object* v_subFn_4378_; lean_object* v_negFn_4379_; lean_object* v_vars_4380_; lean_object* v_varMap_4381_; lean_object* v_lowers_4382_; lean_object* v_uppers_4383_; lean_object* v_diseqs_4384_; lean_object* v_assignment_4385_; uint8_t v_caseSplits_4386_; lean_object* v_conflict_x3f_4387_; lean_object* v_diseqSplits_4388_; lean_object* v_elimEqs_4389_; lean_object* v_elimStack_4390_; lean_object* v_occurs_4391_; lean_object* v_ignored_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4408_; 
v_v_4349_ = lean_array_fget(v_structs_4336_, v___y_4332_);
v_id_4350_ = lean_ctor_get(v_v_4349_, 0);
v_ringId_x3f_4351_ = lean_ctor_get(v_v_4349_, 1);
v_type_4352_ = lean_ctor_get(v_v_4349_, 2);
v_u_4353_ = lean_ctor_get(v_v_4349_, 3);
v_intModuleInst_4354_ = lean_ctor_get(v_v_4349_, 4);
v_leInst_x3f_4355_ = lean_ctor_get(v_v_4349_, 5);
v_ltInst_x3f_4356_ = lean_ctor_get(v_v_4349_, 6);
v_lawfulOrderLTInst_x3f_4357_ = lean_ctor_get(v_v_4349_, 7);
v_isPreorderInst_x3f_4358_ = lean_ctor_get(v_v_4349_, 8);
v_orderedAddInst_x3f_4359_ = lean_ctor_get(v_v_4349_, 9);
v_isLinearInst_x3f_4360_ = lean_ctor_get(v_v_4349_, 10);
v_noNatDivInst_x3f_4361_ = lean_ctor_get(v_v_4349_, 11);
v_ringInst_x3f_4362_ = lean_ctor_get(v_v_4349_, 12);
v_commRingInst_x3f_4363_ = lean_ctor_get(v_v_4349_, 13);
v_orderedRingInst_x3f_4364_ = lean_ctor_get(v_v_4349_, 14);
v_fieldInst_x3f_4365_ = lean_ctor_get(v_v_4349_, 15);
v_charInst_x3f_4366_ = lean_ctor_get(v_v_4349_, 16);
v_zero_4367_ = lean_ctor_get(v_v_4349_, 17);
v_ofNatZero_4368_ = lean_ctor_get(v_v_4349_, 18);
v_one_x3f_4369_ = lean_ctor_get(v_v_4349_, 19);
v_leFn_x3f_4370_ = lean_ctor_get(v_v_4349_, 20);
v_ltFn_x3f_4371_ = lean_ctor_get(v_v_4349_, 21);
v_addFn_4372_ = lean_ctor_get(v_v_4349_, 22);
v_zsmulFn_4373_ = lean_ctor_get(v_v_4349_, 23);
v_nsmulFn_4374_ = lean_ctor_get(v_v_4349_, 24);
v_zsmulFn_x3f_4375_ = lean_ctor_get(v_v_4349_, 25);
v_nsmulFn_x3f_4376_ = lean_ctor_get(v_v_4349_, 26);
v_homomulFn_x3f_4377_ = lean_ctor_get(v_v_4349_, 27);
v_subFn_4378_ = lean_ctor_get(v_v_4349_, 28);
v_negFn_4379_ = lean_ctor_get(v_v_4349_, 29);
v_vars_4380_ = lean_ctor_get(v_v_4349_, 30);
v_varMap_4381_ = lean_ctor_get(v_v_4349_, 31);
v_lowers_4382_ = lean_ctor_get(v_v_4349_, 32);
v_uppers_4383_ = lean_ctor_get(v_v_4349_, 33);
v_diseqs_4384_ = lean_ctor_get(v_v_4349_, 34);
v_assignment_4385_ = lean_ctor_get(v_v_4349_, 35);
v_caseSplits_4386_ = lean_ctor_get_uint8(v_v_4349_, sizeof(void*)*42);
v_conflict_x3f_4387_ = lean_ctor_get(v_v_4349_, 36);
v_diseqSplits_4388_ = lean_ctor_get(v_v_4349_, 37);
v_elimEqs_4389_ = lean_ctor_get(v_v_4349_, 38);
v_elimStack_4390_ = lean_ctor_get(v_v_4349_, 39);
v_occurs_4391_ = lean_ctor_get(v_v_4349_, 40);
v_ignored_4392_ = lean_ctor_get(v_v_4349_, 41);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_v_4349_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4394_ = v_v_4349_;
v_isShared_4395_ = v_isSharedCheck_4408_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_ignored_4392_);
lean_inc(v_occurs_4391_);
lean_inc(v_elimStack_4390_);
lean_inc(v_elimEqs_4389_);
lean_inc(v_diseqSplits_4388_);
lean_inc(v_conflict_x3f_4387_);
lean_inc(v_assignment_4385_);
lean_inc(v_diseqs_4384_);
lean_inc(v_uppers_4383_);
lean_inc(v_lowers_4382_);
lean_inc(v_varMap_4381_);
lean_inc(v_vars_4380_);
lean_inc(v_negFn_4379_);
lean_inc(v_subFn_4378_);
lean_inc(v_homomulFn_x3f_4377_);
lean_inc(v_nsmulFn_x3f_4376_);
lean_inc(v_zsmulFn_x3f_4375_);
lean_inc(v_nsmulFn_4374_);
lean_inc(v_zsmulFn_4373_);
lean_inc(v_addFn_4372_);
lean_inc(v_ltFn_x3f_4371_);
lean_inc(v_leFn_x3f_4370_);
lean_inc(v_one_x3f_4369_);
lean_inc(v_ofNatZero_4368_);
lean_inc(v_zero_4367_);
lean_inc(v_charInst_x3f_4366_);
lean_inc(v_fieldInst_x3f_4365_);
lean_inc(v_orderedRingInst_x3f_4364_);
lean_inc(v_commRingInst_x3f_4363_);
lean_inc(v_ringInst_x3f_4362_);
lean_inc(v_noNatDivInst_x3f_4361_);
lean_inc(v_isLinearInst_x3f_4360_);
lean_inc(v_orderedAddInst_x3f_4359_);
lean_inc(v_isPreorderInst_x3f_4358_);
lean_inc(v_lawfulOrderLTInst_x3f_4357_);
lean_inc(v_ltInst_x3f_4356_);
lean_inc(v_leInst_x3f_4355_);
lean_inc(v_intModuleInst_4354_);
lean_inc(v_u_4353_);
lean_inc(v_type_4352_);
lean_inc(v_ringId_x3f_4351_);
lean_inc(v_id_4350_);
lean_dec(v_v_4349_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4408_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v_xs_x27_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4396_ = lean_box(0);
v_xs_x27_4397_ = lean_array_fset(v_structs_4336_, v___y_4332_, v___x_4396_);
v___x_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_snd_4333_);
v___x_4399_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4389_, v_fst_4334_, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4400_, 0, v_fst_4334_);
lean_ctor_set(v___x_4400_, 1, v_elimStack_4390_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 39, v___x_4400_);
lean_ctor_set(v___x_4394_, 38, v___x_4399_);
v___x_4402_ = v___x_4394_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_id_4350_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_ringId_x3f_4351_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_type_4352_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_u_4353_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_intModuleInst_4354_);
lean_ctor_set(v_reuseFailAlloc_4407_, 5, v_leInst_x3f_4355_);
lean_ctor_set(v_reuseFailAlloc_4407_, 6, v_ltInst_x3f_4356_);
lean_ctor_set(v_reuseFailAlloc_4407_, 7, v_lawfulOrderLTInst_x3f_4357_);
lean_ctor_set(v_reuseFailAlloc_4407_, 8, v_isPreorderInst_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4407_, 9, v_orderedAddInst_x3f_4359_);
lean_ctor_set(v_reuseFailAlloc_4407_, 10, v_isLinearInst_x3f_4360_);
lean_ctor_set(v_reuseFailAlloc_4407_, 11, v_noNatDivInst_x3f_4361_);
lean_ctor_set(v_reuseFailAlloc_4407_, 12, v_ringInst_x3f_4362_);
lean_ctor_set(v_reuseFailAlloc_4407_, 13, v_commRingInst_x3f_4363_);
lean_ctor_set(v_reuseFailAlloc_4407_, 14, v_orderedRingInst_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4407_, 15, v_fieldInst_x3f_4365_);
lean_ctor_set(v_reuseFailAlloc_4407_, 16, v_charInst_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4407_, 17, v_zero_4367_);
lean_ctor_set(v_reuseFailAlloc_4407_, 18, v_ofNatZero_4368_);
lean_ctor_set(v_reuseFailAlloc_4407_, 19, v_one_x3f_4369_);
lean_ctor_set(v_reuseFailAlloc_4407_, 20, v_leFn_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4407_, 21, v_ltFn_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4407_, 22, v_addFn_4372_);
lean_ctor_set(v_reuseFailAlloc_4407_, 23, v_zsmulFn_4373_);
lean_ctor_set(v_reuseFailAlloc_4407_, 24, v_nsmulFn_4374_);
lean_ctor_set(v_reuseFailAlloc_4407_, 25, v_zsmulFn_x3f_4375_);
lean_ctor_set(v_reuseFailAlloc_4407_, 26, v_nsmulFn_x3f_4376_);
lean_ctor_set(v_reuseFailAlloc_4407_, 27, v_homomulFn_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4407_, 28, v_subFn_4378_);
lean_ctor_set(v_reuseFailAlloc_4407_, 29, v_negFn_4379_);
lean_ctor_set(v_reuseFailAlloc_4407_, 30, v_vars_4380_);
lean_ctor_set(v_reuseFailAlloc_4407_, 31, v_varMap_4381_);
lean_ctor_set(v_reuseFailAlloc_4407_, 32, v_lowers_4382_);
lean_ctor_set(v_reuseFailAlloc_4407_, 33, v_uppers_4383_);
lean_ctor_set(v_reuseFailAlloc_4407_, 34, v_diseqs_4384_);
lean_ctor_set(v_reuseFailAlloc_4407_, 35, v_assignment_4385_);
lean_ctor_set(v_reuseFailAlloc_4407_, 36, v_conflict_x3f_4387_);
lean_ctor_set(v_reuseFailAlloc_4407_, 37, v_diseqSplits_4388_);
lean_ctor_set(v_reuseFailAlloc_4407_, 38, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4407_, 39, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4407_, 40, v_occurs_4391_);
lean_ctor_set(v_reuseFailAlloc_4407_, 41, v_ignored_4392_);
lean_ctor_set_uint8(v_reuseFailAlloc_4407_, sizeof(void*)*42, v_caseSplits_4386_);
v___x_4402_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4403_ = lean_array_fset(v_xs_x27_4397_, v___y_4332_, v___x_4402_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4403_);
v___x_4405_ = v___x_4347_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_typeIdOf_4337_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_exprToStructId_4338_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_exprToStructIdEntries_4339_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v_forbiddenNatModules_4340_);
lean_ctor_set(v_reuseFailAlloc_4406_, 5, v_natStructs_4341_);
lean_ctor_set(v_reuseFailAlloc_4406_, 6, v_natTypeIdOf_4342_);
lean_ctor_set(v_reuseFailAlloc_4406_, 7, v_exprToNatStructId_4343_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4418_, lean_object* v_snd_4419_, lean_object* v_fst_4420_, lean_object* v_s_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4418_, v_snd_4419_, v_fst_4420_, v_s_4421_);
lean_dec(v___y_4418_);
return v_res_4422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4425_ = l_Lean_stringToMessageData(v___x_4424_);
return v___x_4425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4433_ = l_Lean_Name_append(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v_toCold_4513_; lean_object* v_options_4514_; lean_object* v_inheritedTraceOptions_4515_; uint8_t v_hasTrace_4516_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v_options_4533_; lean_object* v_inheritedTraceOptions_4534_; lean_object* v___y_4535_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; 
v_toCold_4513_ = lean_ctor_get(v_a_4444_, 0);
v_options_4514_ = lean_ctor_get(v_toCold_4513_, 2);
v_inheritedTraceOptions_4515_ = lean_ctor_get(v_toCold_4513_, 11);
v_hasTrace_4516_ = lean_ctor_get_uint8(v_options_4514_, sizeof(void*)*1);
if (v_hasTrace_4516_ == 0)
{
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
goto v___jp_4551_;
}
else
{
lean_object* v_cls_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v_cls_4660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4515_, v_options_4514_, v___x_4661_);
if (v___x_4662_ == 0)
{
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4663_; 
v___x_4663_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v___x_4663_, 1);
v___x_4665_ = l_Lean_MessageData_ofExpr(v_a_4664_);
v___x_4666_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4660_, v___x_4665_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_dec_ref_known(v___x_4666_, 1);
v___y_4552_ = v_a_4435_;
v___y_4553_ = v_a_4436_;
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
goto v___jp_4551_;
}
else
{
lean_dec_ref(v_c_4434_);
return v___x_4666_;
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec_ref(v_c_4434_);
v_a_4667_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___x_4663_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4663_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
v___jp_4447_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = lean_box(0);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
v___jp_4450_:
{
lean_object* v___f_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_inc(v___y_4456_);
v___f_4467_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4467_, 0, v___y_4456_);
lean_closure_set(v___f_4467_, 1, v___y_4452_);
lean_closure_set(v___f_4467_, 2, v___y_4451_);
v___x_4468_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4469_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4468_, v___f_4467_, v___y_4457_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4469_, 1);
v___x_4470_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4454_, v___y_4453_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4470_;
}
else
{
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec(v___y_4453_);
return v___x_4469_;
}
}
v___jp_4471_:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; uint8_t v_caseSplits_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v_caseSplits_4490_ = lean_ctor_get_uint8(v_a_4489_, sizeof(void*)*42);
lean_dec(v_a_4489_);
if (v_caseSplits_4490_ == 0)
{
lean_object* v___x_4491_; 
v___x_4491_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; uint8_t v___x_4493_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = lean_unbox(v_a_4492_);
lean_dec(v_a_4492_);
if (v___x_4493_ == 0)
{
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
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4494_; lean_object* v_a_4495_; lean_object* v___x_4496_; 
lean_inc_ref(v___y_4476_);
v___x_4494_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4476_);
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref(v___x_4494_);
v___x_4496_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4495_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_dec_ref_known(v___x_4496_, 1);
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
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
goto v___jp_4450_;
}
else
{
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
return v___x_4496_;
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
v_a_4497_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4491_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4491_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
else
{
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
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
goto v___jp_4450_;
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
v_a_4505_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4488_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4488_);
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
v___jp_4517_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4534_, v_options_4533_, v___x_4537_);
if (v___x_4538_ == 0)
{
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
v___y_4484_ = v___y_4530_;
v___y_4485_ = v___y_4531_;
v___y_4486_ = v___y_4532_;
v___y_4487_ = v___y_4535_;
goto v___jp_4471_;
}
else
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4535_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
lean_dec_ref_known(v___x_4539_, 1);
v___x_4541_ = l_Lean_MessageData_ofExpr(v_a_4540_);
v___x_4542_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4536_, v___x_4541_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4535_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_dec_ref_known(v___x_4542_, 1);
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
v___y_4484_ = v___y_4530_;
v___y_4485_ = v___y_4531_;
v___y_4486_ = v___y_4532_;
v___y_4487_ = v___y_4535_;
goto v___jp_4471_;
}
else
{
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
return v___x_4542_;
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
v_a_4543_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4539_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4539_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
v___jp_4551_:
{
lean_object* v___x_4563_; 
lean_inc_ref(v___y_4561_);
v___x_4563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4434_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v_p_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v_p_4565_ = lean_ctor_get(v_a_4564_, 0);
v___x_4566_ = lean_box(0);
v___x_4567_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4565_, v___x_4566_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
v___x_4568_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4564_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v_snd_4570_; lean_object* v_toCold_4571_; lean_object* v_options_4572_; uint8_t v_hasTrace_4573_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref_known(v___x_4568_, 1);
v_snd_4570_ = lean_ctor_get(v_a_4569_, 1);
lean_inc(v_snd_4570_);
v_toCold_4571_ = lean_ctor_get(v___y_4561_, 0);
v_options_4572_ = lean_ctor_get(v_toCold_4571_, 2);
v_hasTrace_4573_ = lean_ctor_get_uint8(v_options_4572_, sizeof(void*)*1);
if (v_hasTrace_4573_ == 0)
{
lean_object* v_fst_4574_; lean_object* v_fst_4575_; lean_object* v_snd_4576_; 
v_fst_4574_ = lean_ctor_get(v_a_4569_, 0);
lean_inc(v_fst_4574_);
lean_dec(v_a_4569_);
v_fst_4575_ = lean_ctor_get(v_snd_4570_, 0);
lean_inc_n(v_fst_4575_, 2);
v_snd_4576_ = lean_ctor_get(v_snd_4570_, 1);
lean_inc_n(v_snd_4576_, 2);
lean_dec(v_snd_4570_);
v___y_4472_ = v_fst_4575_;
v___y_4473_ = v_snd_4576_;
v___y_4474_ = v_fst_4575_;
v___y_4475_ = v_fst_4574_;
v___y_4476_ = v_snd_4576_;
v___y_4477_ = v___y_4552_;
v___y_4478_ = v___y_4553_;
v___y_4479_ = v___y_4554_;
v___y_4480_ = v___y_4555_;
v___y_4481_ = v___y_4556_;
v___y_4482_ = v___y_4557_;
v___y_4483_ = v___y_4558_;
v___y_4484_ = v___y_4559_;
v___y_4485_ = v___y_4560_;
v___y_4486_ = v___y_4561_;
v___y_4487_ = v___y_4562_;
goto v___jp_4471_;
}
else
{
lean_object* v_fst_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4623_; 
v_fst_4577_ = lean_ctor_get(v_a_4569_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v_a_4569_);
if (v_isSharedCheck_4623_ == 0)
{
lean_object* v_unused_4624_; 
v_unused_4624_ = lean_ctor_get(v_a_4569_, 1);
lean_dec(v_unused_4624_);
v___x_4579_ = v_a_4569_;
v_isShared_4580_ = v_isSharedCheck_4623_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_fst_4577_);
lean_dec(v_a_4569_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4623_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v_fst_4581_; lean_object* v_snd_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4622_; 
v_fst_4581_ = lean_ctor_get(v_snd_4570_, 0);
v_snd_4582_ = lean_ctor_get(v_snd_4570_, 1);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_snd_4570_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4584_ = v_snd_4570_;
v_isShared_4585_ = v_isSharedCheck_4622_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_snd_4582_);
lean_inc(v_fst_4581_);
lean_dec(v_snd_4570_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4622_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v_inheritedTraceOptions_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; uint8_t v___x_4589_; 
v_inheritedTraceOptions_4586_ = lean_ctor_get(v_toCold_4571_, 11);
v___x_4587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4586_, v_options_4572_, v___x_4588_);
if (v___x_4589_ == 0)
{
lean_del_object(v___x_4584_);
lean_del_object(v___x_4579_);
lean_inc(v_snd_4582_);
lean_inc(v_fst_4581_);
v___y_4518_ = v_fst_4581_;
v___y_4519_ = v_snd_4582_;
v___y_4520_ = v_fst_4581_;
v___y_4521_ = v_fst_4577_;
v___y_4522_ = v_snd_4582_;
v___y_4523_ = v___y_4552_;
v___y_4524_ = v___y_4553_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v_options_4533_ = v_options_4572_;
v_inheritedTraceOptions_4534_ = v_inheritedTraceOptions_4586_;
v___y_4535_ = v___y_4562_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4590_; 
v___x_4590_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4581_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4592_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v___x_4592_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4582_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v___x_4594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4595_ = l_Lean_MessageData_ofExpr(v_a_4591_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set_tag(v___x_4584_, 7);
lean_ctor_set(v___x_4584_, 1, v___x_4595_);
lean_ctor_set(v___x_4584_, 0, v___x_4594_);
v___x_4597_ = v___x_4584_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4598_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4580_ == 0)
{
lean_ctor_set_tag(v___x_4579_, 7);
lean_ctor_set(v___x_4579_, 1, v___x_4598_);
lean_ctor_set(v___x_4579_, 0, v___x_4597_);
v___x_4600_ = v___x_4579_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4601_ = l_Lean_MessageData_ofExpr(v_a_4593_);
v___x_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4587_, v___x_4602_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_dec_ref_known(v___x_4603_, 1);
lean_inc(v_snd_4582_);
lean_inc(v_fst_4581_);
v___y_4518_ = v_fst_4581_;
v___y_4519_ = v_snd_4582_;
v___y_4520_ = v_fst_4581_;
v___y_4521_ = v_fst_4577_;
v___y_4522_ = v_snd_4582_;
v___y_4523_ = v___y_4552_;
v___y_4524_ = v___y_4553_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v_options_4533_ = v_options_4572_;
v_inheritedTraceOptions_4534_ = v_inheritedTraceOptions_4586_;
v___y_4535_ = v___y_4562_;
goto v___jp_4517_;
}
else
{
lean_dec(v_snd_4582_);
lean_dec(v_fst_4581_);
lean_dec(v_fst_4577_);
return v___x_4603_;
}
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec(v_a_4591_);
lean_del_object(v___x_4584_);
lean_dec(v_snd_4582_);
lean_dec(v_fst_4581_);
lean_del_object(v___x_4579_);
lean_dec(v_fst_4577_);
v_a_4606_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4592_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4592_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_del_object(v___x_4584_);
lean_dec(v_snd_4582_);
lean_dec(v_fst_4581_);
lean_del_object(v___x_4579_);
lean_dec(v_fst_4577_);
v_a_4614_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4590_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4590_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
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
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
v_a_4625_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4568_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4568_);
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
else
{
lean_object* v_toCold_4633_; lean_object* v_options_4634_; uint8_t v_hasTrace_4635_; 
v_toCold_4633_ = lean_ctor_get(v___y_4561_, 0);
v_options_4634_ = lean_ctor_get(v_toCold_4633_, 2);
v_hasTrace_4635_ = lean_ctor_get_uint8(v_options_4634_, sizeof(void*)*1);
if (v_hasTrace_4635_ == 0)
{
lean_dec(v_a_4564_);
goto v___jp_4447_;
}
else
{
lean_object* v_inheritedTraceOptions_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v_inheritedTraceOptions_4636_ = lean_ctor_get(v_toCold_4633_, 11);
v___x_4637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4638_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4636_, v_options_4634_, v___x_4638_);
if (v___x_4639_ == 0)
{
lean_dec(v_a_4564_);
goto v___jp_4447_;
}
else
{
lean_object* v___x_4640_; 
v___x_4640_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4564_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v_a_4564_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v___x_4640_, 1);
v___x_4642_ = l_Lean_MessageData_ofExpr(v_a_4641_);
v___x_4643_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4637_, v___x_4642_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_dec_ref_known(v___x_4643_, 1);
goto v___jp_4447_;
}
else
{
return v___x_4643_;
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
v_a_4644_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4640_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4640_);
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
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
v_a_4652_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4563_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4563_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec(v_a_4676_);
return v_res_4688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_cls_4693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4695_ = l_Lean_Name_append(v___x_4694_, v_cls_4693_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4696_, lean_object* v_b_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v_toCold_4706_; lean_object* v_options_4707_; uint8_t v_hasTrace_4708_; 
v_toCold_4706_ = lean_ctor_get(v_a_4700_, 0);
v_options_4707_ = lean_ctor_get(v_toCold_4706_, 2);
v_hasTrace_4708_ = lean_ctor_get_uint8(v_options_4707_, sizeof(void*)*1);
if (v_hasTrace_4708_ == 0)
{
lean_dec_ref(v_b_4697_);
lean_dec_ref(v_a_4696_);
goto v___jp_4703_;
}
else
{
lean_object* v_inheritedTraceOptions_4709_; lean_object* v_cls_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v_inheritedTraceOptions_4709_ = lean_ctor_get(v_toCold_4706_, 11);
v_cls_4710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4709_, v_options_4707_, v___x_4711_);
if (v___x_4712_ == 0)
{
lean_dec_ref(v_b_4697_);
lean_dec_ref(v_a_4696_);
goto v___jp_4703_;
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4713_ = l_Lean_MessageData_ofExpr(v_a_4696_);
v___x_4714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = l_Lean_MessageData_ofExpr(v_b_4697_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4710_, v___x_4717_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
return v___x_4718_;
}
}
v___jp_4703_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = lean_box(0);
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
return v___x_4705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4719_, lean_object* v_b_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4719_, v_b_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4727_, lean_object* v_b_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4727_, v_b_4728_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4742_, lean_object* v_b_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4742_, v_b_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
lean_dec(v_a_4746_);
lean_dec(v_a_4745_);
lean_dec(v_a_4744_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4757_, lean_object* v_b_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4757_, v_a_4760_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; uint8_t v___x_4773_; lean_object* v___x_4774_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4771_, 1);
v___x_4773_ = 0;
lean_inc_ref(v_a_4757_);
v___x_4774_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4757_, v___x_4773_, v_a_4772_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4824_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4777_ = v___x_4774_;
v_isShared_4778_ = v_isSharedCheck_4824_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4774_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4824_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
if (lean_obj_tag(v_a_4775_) == 1)
{
lean_object* v_val_4779_; lean_object* v___x_4780_; 
lean_del_object(v___x_4777_);
v_val_4779_ = lean_ctor_get(v_a_4775_, 0);
lean_inc(v_val_4779_);
lean_dec_ref_known(v_a_4775_, 1);
v___x_4780_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4758_, v_a_4760_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4782_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4780_, 1);
lean_inc_ref(v_b_4758_);
v___x_4782_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4758_, v___x_4773_, v_a_4781_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4803_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4785_ = v___x_4782_;
v_isShared_4786_ = v_isSharedCheck_4803_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4803_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
if (lean_obj_tag(v_a_4783_) == 1)
{
lean_object* v_val_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_val_4787_ = lean_ctor_get(v_a_4783_, 0);
lean_inc_n(v_val_4787_, 2);
lean_dec_ref_known(v_a_4783_, 1);
lean_inc(v_val_4779_);
v___x_4788_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4788_, 0, v_val_4779_);
lean_ctor_set(v___x_4788_, 1, v_val_4787_);
v___x_4789_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4788_);
v___x_4790_ = lean_box(0);
v___x_4791_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4789_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_del_object(v___x_4785_);
v___x_4792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4792_, 0, v_a_4757_);
lean_ctor_set(v___x_4792_, 1, v_b_4758_);
lean_ctor_set(v___x_4792_, 2, v_val_4779_);
lean_ctor_set(v___x_4792_, 3, v_val_4787_);
v___x_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4789_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v___x_4794_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4793_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
return v___x_4794_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_dec(v___x_4789_);
lean_dec(v_val_4787_);
lean_dec(v_val_4779_);
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v___x_4795_ = lean_box(0);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4795_);
v___x_4797_ = v___x_4785_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
lean_dec(v_a_4783_);
lean_dec(v_val_4779_);
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v___x_4799_ = lean_box(0);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4799_);
v___x_4801_ = v___x_4785_;
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
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec(v_val_4779_);
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v_a_4804_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4782_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4782_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec(v_val_4779_);
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v_a_4812_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4780_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4780_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4822_; 
lean_dec(v_a_4775_);
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v___x_4820_ = lean_box(0);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4820_);
v___x_4822_ = v___x_4777_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
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
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v_a_4825_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4774_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4774_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec_ref(v_b_4758_);
lean_dec_ref(v_a_4757_);
v_a_4833_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4771_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4771_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4841_, lean_object* v_b_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4841_, v_b_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec(v_a_4844_);
lean_dec(v_a_4843_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4856_, lean_object* v_b_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4872_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_a_4871_);
lean_dec_ref_known(v___x_4870_, 1);
lean_inc_ref(v_a_4856_);
v___x_4872_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4856_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v_fst_4874_; lean_object* v___x_4875_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
v_fst_4874_ = lean_ctor_get(v_a_4873_, 0);
lean_inc(v_fst_4874_);
lean_dec(v_a_4873_);
lean_inc_ref(v_b_4857_);
v___x_4875_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v_fst_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4960_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
v_fst_4877_ = lean_ctor_get(v_a_4876_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v_a_4876_);
if (v_isSharedCheck_4960_ == 0)
{
lean_object* v_unused_4961_; 
v_unused_4961_ = lean_ctor_get(v_a_4876_, 1);
lean_dec(v_unused_4961_);
v___x_4879_ = v_a_4876_;
v_isShared_4880_ = v_isSharedCheck_4960_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_fst_4877_);
lean_dec(v_a_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4960_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v_id_4881_; lean_object* v_structId_4882_; lean_object* v___x_4883_; 
v_id_4881_ = lean_ctor_get(v_a_4871_, 0);
lean_inc(v_id_4881_);
v_structId_4882_ = lean_ctor_get(v_a_4871_, 1);
lean_inc(v_structId_4882_);
lean_dec(v_a_4871_);
v___x_4883_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4856_, v_a_4859_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4883_, 1);
v___x_4885_ = 0;
v___x_4886_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4874_, v___x_4885_, v_a_4884_, v_structId_4882_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4943_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4943_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4943_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
if (lean_obj_tag(v_a_4887_) == 1)
{
lean_object* v_val_4891_; lean_object* v___x_4892_; 
lean_del_object(v___x_4889_);
v_val_4891_ = lean_ctor_get(v_a_4887_, 0);
lean_inc(v_val_4891_);
lean_dec_ref_known(v_a_4887_, 1);
v___x_4892_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4857_, v_a_4859_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4894_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4894_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4877_, v___x_4885_, v_a_4893_, v_structId_4882_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4922_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4922_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4922_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
if (lean_obj_tag(v_a_4895_) == 1)
{
lean_object* v_val_4899_; lean_object* v___x_4901_; 
v_val_4899_ = lean_ctor_get(v_a_4895_, 0);
lean_inc_n(v_val_4899_, 2);
lean_dec_ref_known(v_a_4895_, 1);
lean_inc(v_val_4891_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set_tag(v___x_4879_, 3);
lean_ctor_set(v___x_4879_, 1, v_val_4899_);
lean_ctor_set(v___x_4879_, 0, v_val_4891_);
v___x_4901_ = v___x_4879_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_val_4891_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_val_4899_);
v___x_4901_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4902_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4901_);
v___x_4903_ = lean_box(0);
v___x_4904_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4902_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_del_object(v___x_4897_);
lean_inc(v_val_4899_);
lean_inc(v_val_4891_);
lean_inc(v_id_4881_);
lean_inc_ref(v_b_4857_);
lean_inc_ref(v_a_4856_);
v___x_4905_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4905_, 0, v_a_4856_);
lean_ctor_set(v___x_4905_, 1, v_b_4857_);
lean_ctor_set(v___x_4905_, 2, v_id_4881_);
lean_ctor_set(v___x_4905_, 3, v_val_4891_);
lean_ctor_set(v___x_4905_, 4, v_val_4899_);
lean_inc(v___x_4902_);
v___x_4906_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4906_, 0, v___x_4902_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
lean_ctor_set_uint8(v___x_4906_, sizeof(void*)*2, v___x_4885_);
v___x_4907_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4906_, v_structId_4882_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_dec_ref_known(v___x_4907_, 1);
v___x_4908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4909_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4902_, v___x_4908_);
v___x_4910_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4910_, 0, v_b_4857_);
lean_ctor_set(v___x_4910_, 1, v_a_4856_);
lean_ctor_set(v___x_4910_, 2, v_id_4881_);
lean_ctor_set(v___x_4910_, 3, v_val_4899_);
lean_ctor_set(v___x_4910_, 4, v_val_4891_);
v___x_4911_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4911_, 0, v___x_4909_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*2, v___x_4885_);
v___x_4912_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4911_, v_structId_4882_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
lean_dec(v_structId_4882_);
return v___x_4912_;
}
else
{
lean_dec(v___x_4902_);
lean_dec(v_val_4899_);
lean_dec(v_val_4891_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
return v___x_4907_;
}
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4915_; 
lean_dec(v___x_4902_);
lean_dec(v_val_4899_);
lean_dec(v_val_4891_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v___x_4913_ = lean_box(0);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4913_);
v___x_4915_ = v___x_4897_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
lean_dec(v_a_4895_);
lean_dec(v_val_4891_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v___x_4918_ = lean_box(0);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4918_);
v___x_4920_ = v___x_4897_;
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
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_dec(v_val_4891_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4923_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4894_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4894_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
else
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4938_; 
lean_dec(v_val_4891_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec(v_fst_4877_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4931_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4933_ = v___x_4892_;
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v___x_4892_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
else
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
lean_dec(v_a_4887_);
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec(v_fst_4877_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v___x_4939_ = lean_box(0);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4939_);
v___x_4941_ = v___x_4889_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4939_);
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
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec(v_fst_4877_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4944_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4886_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4886_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v_structId_4882_);
lean_dec(v_id_4881_);
lean_del_object(v___x_4879_);
lean_dec(v_fst_4877_);
lean_dec(v_fst_4874_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4952_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4883_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4883_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
lean_dec(v_fst_4874_);
lean_dec(v_a_4871_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4962_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4875_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4875_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_dec(v_a_4871_);
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4970_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4872_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4872_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_dec_ref(v_b_4857_);
lean_dec_ref(v_a_4856_);
v_a_4978_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4870_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4870_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4986_, lean_object* v_b_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4986_, v_b_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec(v_a_4988_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5001_, lean_object* v_b_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5017_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
lean_dec_ref_known(v___x_5015_, 1);
lean_inc_ref(v_a_5001_);
v___x_5017_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5001_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v_fst_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5115_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5017_, 1);
v_fst_5019_ = lean_ctor_get(v_a_5018_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v_a_5018_);
if (v_isSharedCheck_5115_ == 0)
{
lean_object* v_unused_5116_; 
v_unused_5116_ = lean_ctor_get(v_a_5018_, 1);
lean_dec(v_unused_5116_);
v___x_5021_ = v_a_5018_;
v_isShared_5022_ = v_isSharedCheck_5115_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_fst_5019_);
lean_dec(v_a_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5115_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; 
lean_inc_ref(v_b_5002_);
v___x_5023_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v_fst_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5105_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___x_5023_, 1);
v_fst_5025_ = lean_ctor_get(v_a_5024_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_a_5024_);
if (v_isSharedCheck_5105_ == 0)
{
lean_object* v_unused_5106_; 
v_unused_5106_ = lean_ctor_get(v_a_5024_, 1);
lean_dec(v_unused_5106_);
v___x_5027_ = v_a_5024_;
v_isShared_5028_ = v_isSharedCheck_5105_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_fst_5025_);
lean_dec(v_a_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5105_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v_id_5029_; lean_object* v_structId_5030_; lean_object* v___x_5031_; 
v_id_5029_ = lean_ctor_get(v_a_5016_, 0);
lean_inc(v_id_5029_);
v_structId_5030_ = lean_ctor_get(v_a_5016_, 1);
lean_inc(v_structId_5030_);
lean_dec(v_a_5016_);
v___x_5031_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5001_, v_a_5004_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; uint8_t v___x_5033_; lean_object* v___x_5034_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5033_ = 0;
v___x_5034_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5019_, v___x_5033_, v_a_5032_, v_structId_5030_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5088_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5037_ = v___x_5034_;
v_isShared_5038_ = v_isSharedCheck_5088_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5034_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5088_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
if (lean_obj_tag(v_a_5035_) == 1)
{
lean_object* v_val_5039_; lean_object* v___x_5040_; 
lean_del_object(v___x_5037_);
v_val_5039_ = lean_ctor_get(v_a_5035_, 0);
lean_inc(v_val_5039_);
lean_dec_ref_known(v_a_5035_, 1);
v___x_5040_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5002_, v_a_5004_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5042_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v___x_5042_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5025_, v___x_5033_, v_a_5041_, v_structId_5030_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5067_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5045_ = v___x_5042_;
v_isShared_5046_ = v_isSharedCheck_5067_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5042_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5067_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
if (lean_obj_tag(v_a_5043_) == 1)
{
lean_object* v_val_5047_; lean_object* v___x_5049_; 
v_val_5047_ = lean_ctor_get(v_a_5043_, 0);
lean_inc_n(v_val_5047_, 2);
lean_dec_ref_known(v_a_5043_, 1);
lean_inc(v_val_5039_);
if (v_isShared_5028_ == 0)
{
lean_ctor_set_tag(v___x_5027_, 3);
lean_ctor_set(v___x_5027_, 1, v_val_5047_);
lean_ctor_set(v___x_5027_, 0, v_val_5039_);
v___x_5049_ = v___x_5027_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_val_5039_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v_val_5047_);
v___x_5049_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v___x_5050_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5049_);
v___x_5051_ = lean_box(0);
v___x_5052_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5050_, v___x_5051_);
if (v___x_5052_ == 0)
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
lean_del_object(v___x_5045_);
v___x_5053_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5053_, 0, v_a_5001_);
lean_ctor_set(v___x_5053_, 1, v_b_5002_);
lean_ctor_set(v___x_5053_, 2, v_id_5029_);
lean_ctor_set(v___x_5053_, 3, v_val_5039_);
lean_ctor_set(v___x_5053_, 4, v_val_5047_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 1, v___x_5053_);
lean_ctor_set(v___x_5021_, 0, v___x_5050_);
v___x_5055_ = v___x_5021_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5050_);
lean_ctor_set(v_reuseFailAlloc_5057_, 1, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; 
v___x_5056_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5055_, v_structId_5030_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_structId_5030_);
return v___x_5056_;
}
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
lean_dec(v___x_5050_);
lean_dec(v_val_5047_);
lean_dec(v_val_5039_);
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v___x_5058_ = lean_box(0);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v___x_5058_);
v___x_5060_ = v___x_5045_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5065_; 
lean_dec(v_a_5043_);
lean_dec(v_val_5039_);
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v___x_5063_ = lean_box(0);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v___x_5063_);
v___x_5065_ = v___x_5045_;
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
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v_val_5039_);
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5068_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5042_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5042_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec(v_val_5039_);
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_dec(v_fst_5025_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5076_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5040_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5040_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
else
{
lean_object* v___x_5084_; lean_object* v___x_5086_; 
lean_dec(v_a_5035_);
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_dec(v_fst_5025_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v___x_5084_ = lean_box(0);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 0, v___x_5084_);
v___x_5086_ = v___x_5037_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
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
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_dec(v_fst_5025_);
lean_del_object(v___x_5021_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5089_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5034_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5034_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec(v_structId_5030_);
lean_dec(v_id_5029_);
lean_del_object(v___x_5027_);
lean_dec(v_fst_5025_);
lean_del_object(v___x_5021_);
lean_dec(v_fst_5019_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5097_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5031_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5031_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_del_object(v___x_5021_);
lean_dec(v_fst_5019_);
lean_dec(v_a_5016_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5107_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5023_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5023_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec(v_a_5016_);
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5117_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5017_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5017_);
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
lean_dec_ref(v_b_5002_);
lean_dec_ref(v_a_5001_);
v_a_5125_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5015_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5015_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5133_, lean_object* v_b_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5133_, v_b_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec_ref(v_a_5140_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec(v_a_5135_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5148_, lean_object* v_b_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_){
_start:
{
size_t v___x_5161_; size_t v___x_5162_; uint8_t v___x_5163_; 
v___x_5161_ = lean_ptr_addr(v_a_5148_);
v___x_5162_ = lean_ptr_addr(v_b_5149_);
v___x_5163_ = lean_usize_dec_eq(v___x_5161_, v___x_5162_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; 
v___x_5164_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5148_, v_b_5149_, v_a_5150_, v_a_5158_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5165_);
lean_dec_ref_known(v___x_5164_, 1);
if (lean_obj_tag(v_a_5165_) == 1)
{
lean_object* v_val_5166_; lean_object* v___x_5167_; 
v_val_5166_ = lean_ctor_get(v_a_5165_, 0);
lean_inc(v_val_5166_);
lean_dec_ref_known(v_a_5165_, 1);
v___x_5167_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
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
v___x_5170_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
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
v___x_5173_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5148_, v_b_5149_, v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_val_5166_);
return v___x_5173_;
}
else
{
lean_object* v___x_5174_; 
lean_dec(v_val_5166_);
v___x_5174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5148_, v_b_5149_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
return v___x_5174_;
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec(v_val_5166_);
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v_a_5175_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5170_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5170_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
else
{
lean_object* v___x_5183_; 
v___x_5183_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; uint8_t v___x_5185_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_a_5184_);
lean_dec_ref_known(v___x_5183_, 1);
v___x_5185_ = lean_unbox(v_a_5184_);
lean_dec(v_a_5184_);
if (v___x_5185_ == 0)
{
lean_object* v___x_5186_; 
v___x_5186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5148_, v_b_5149_, v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_val_5166_);
return v___x_5186_;
}
else
{
lean_object* v___x_5187_; 
v___x_5187_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5148_, v_b_5149_, v_val_5166_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_val_5166_);
return v___x_5187_;
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec(v_val_5166_);
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
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
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_dec(v_val_5166_);
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v_a_5196_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5167_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5167_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
lean_object* v___x_5204_; 
lean_dec(v_a_5165_);
v___x_5204_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5148_, v_b_5149_, v_a_5150_, v_a_5158_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5227_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5207_ = v___x_5204_;
v_isShared_5208_ = v_isSharedCheck_5227_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5204_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5227_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
if (lean_obj_tag(v_a_5205_) == 1)
{
lean_object* v_val_5209_; lean_object* v___x_5210_; 
lean_del_object(v___x_5207_);
v_val_5209_ = lean_ctor_get(v_a_5205_, 0);
lean_inc(v_val_5209_);
lean_dec_ref_known(v_a_5205_, 1);
v___x_5210_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5209_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v_a_5211_; lean_object* v_orderedAddInst_x3f_5212_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_a_5211_);
lean_dec_ref_known(v___x_5210_, 1);
v_orderedAddInst_x3f_5212_ = lean_ctor_get(v_a_5211_, 9);
lean_inc(v_orderedAddInst_x3f_5212_);
lean_dec(v_a_5211_);
if (lean_obj_tag(v_orderedAddInst_x3f_5212_) == 0)
{
lean_object* v___x_5213_; 
v___x_5213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5148_, v_b_5149_, v_val_5209_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_val_5209_);
return v___x_5213_;
}
else
{
lean_object* v___x_5214_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5212_, 1);
v___x_5214_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5148_, v_b_5149_, v_val_5209_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_val_5209_);
return v___x_5214_;
}
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec(v_val_5209_);
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v_a_5215_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5210_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5210_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
else
{
lean_object* v___x_5223_; lean_object* v___x_5225_; 
lean_dec(v_a_5205_);
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v___x_5223_ = lean_box(0);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v___x_5223_);
v___x_5225_ = v___x_5207_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v_a_5228_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5204_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5204_);
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
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v_a_5236_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5164_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5164_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
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
lean_object* v___x_5244_; lean_object* v___x_5245_; 
lean_dec_ref(v_b_5149_);
lean_dec_ref(v_a_5148_);
v___x_5244_ = lean_box(0);
v___x_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5244_);
return v___x_5245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5246_, lean_object* v_b_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5246_, v_b_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec(v_a_5251_);
lean_dec_ref(v_a_5250_);
lean_dec(v_a_5249_);
lean_dec(v_a_5248_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5260_, lean_object* v_b_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
uint8_t v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5274_ = 0;
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = lean_box(v___x_5274_);
lean_inc_ref(v_a_5260_);
v___x_5277_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5277_, 0, v_a_5260_);
lean_closure_set(v___x_5277_, 1, v___x_5276_);
lean_closure_set(v___x_5277_, 2, v___x_5275_);
v___x_5278_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5277_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5380_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5281_ = v___x_5278_;
v_isShared_5282_ = v_isSharedCheck_5380_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5278_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5380_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
if (lean_obj_tag(v_a_5279_) == 1)
{
lean_object* v_val_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
lean_del_object(v___x_5281_);
v_val_5283_ = lean_ctor_get(v_a_5279_, 0);
lean_inc(v_val_5283_);
lean_dec_ref_known(v_a_5279_, 1);
v___x_5284_ = lean_box(v___x_5274_);
lean_inc_ref(v_b_5261_);
v___x_5285_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5285_, 0, v_b_5261_);
lean_closure_set(v___x_5285_, 1, v___x_5284_);
lean_closure_set(v___x_5285_, 2, v___x_5275_);
v___x_5286_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5285_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5367_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5289_ = v___x_5286_;
v_isShared_5290_ = v_isSharedCheck_5367_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5286_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5367_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
if (lean_obj_tag(v_a_5287_) == 1)
{
lean_object* v_val_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_del_object(v___x_5289_);
v_val_5291_ = lean_ctor_get(v_a_5287_, 0);
lean_inc_n(v_val_5291_, 2);
lean_dec_ref_known(v_a_5287_, 1);
lean_inc(v_val_5283_);
v___x_5292_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5292_, 0, v_val_5283_);
lean_ctor_set(v___x_5292_, 1, v_val_5291_);
v___x_5293_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5292_);
lean_inc_ref(v_b_5261_);
lean_inc_ref(v_a_5260_);
v___x_5294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5294_, 0, v_a_5260_);
lean_ctor_set(v___x_5294_, 1, v_b_5261_);
lean_ctor_set(v___x_5294_, 2, v_val_5283_);
lean_ctor_set(v___x_5294_, 3, v_val_5291_);
v___x_5295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5293_);
lean_ctor_set(v___x_5295_, 1, v___x_5294_);
v___x_5296_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5295_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; lean_object* v_p_5298_; lean_object* v___x_5299_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_a_5297_);
lean_dec_ref_known(v___x_5296_, 1);
v_p_5298_ = lean_ctor_get(v_a_5297_, 0);
v___x_5299_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5260_, v_a_5263_);
lean_dec_ref(v_a_5260_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5301_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
lean_inc(v_a_5300_);
lean_dec_ref_known(v___x_5299_, 1);
v___x_5301_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5261_, v_a_5263_);
lean_dec_ref(v_b_5261_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___y_5304_; uint8_t v___x_5338_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref_known(v___x_5301_, 1);
v___x_5338_ = lean_nat_dec_le(v_a_5300_, v_a_5302_);
if (v___x_5338_ == 0)
{
lean_dec(v_a_5302_);
v___y_5304_ = v_a_5300_;
goto v___jp_5303_;
}
else
{
lean_dec(v_a_5300_);
v___y_5304_ = v_a_5302_;
goto v___jp_5303_;
}
v___jp_5303_:
{
lean_object* v___x_5305_; 
lean_inc(v___y_5304_);
lean_inc_ref(v_p_5298_);
v___x_5305_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5298_, v___y_5304_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5307_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref_known(v___x_5305_, 1);
v___x_5307_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5306_, v___x_5274_, v___y_5304_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5321_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5310_ = v___x_5307_;
v_isShared_5311_ = v_isSharedCheck_5321_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5307_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5321_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
if (lean_obj_tag(v_a_5308_) == 1)
{
lean_object* v_val_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
lean_del_object(v___x_5310_);
v_val_5312_ = lean_ctor_get(v_a_5308_, 0);
lean_inc_n(v_val_5312_, 2);
lean_dec_ref_known(v_a_5308_, 1);
v___x_5313_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5312_);
v___x_5314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5314_, 0, v_a_5297_);
lean_ctor_set(v___x_5314_, 1, v_val_5312_);
v___x_5315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5313_);
lean_ctor_set(v___x_5315_, 1, v___x_5314_);
v___x_5316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5315_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
return v___x_5316_;
}
else
{
lean_object* v___x_5317_; lean_object* v___x_5319_; 
lean_dec(v_a_5308_);
lean_dec(v_a_5297_);
v___x_5317_ = lean_box(0);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 0, v___x_5317_);
v___x_5319_ = v___x_5310_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5317_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_dec(v_a_5297_);
v_a_5322_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5307_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5307_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
lean_dec(v___y_5304_);
lean_dec(v_a_5297_);
v_a_5330_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5305_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5305_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec(v_a_5300_);
lean_dec(v_a_5297_);
v_a_5339_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5301_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5301_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
lean_dec(v_a_5297_);
lean_dec_ref(v_b_5261_);
v_a_5347_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5299_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5299_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
lean_dec_ref(v_b_5261_);
lean_dec_ref(v_a_5260_);
v_a_5355_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5296_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5296_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
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
lean_object* v___x_5363_; lean_object* v___x_5365_; 
lean_dec(v_a_5287_);
lean_dec(v_val_5283_);
lean_dec_ref(v_b_5261_);
lean_dec_ref(v_a_5260_);
v___x_5363_ = lean_box(0);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 0, v___x_5363_);
v___x_5365_ = v___x_5289_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5363_);
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
lean_dec(v_val_5283_);
lean_dec_ref(v_b_5261_);
lean_dec_ref(v_a_5260_);
v_a_5368_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5286_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5286_);
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
lean_dec(v_a_5279_);
lean_dec_ref(v_b_5261_);
lean_dec_ref(v_a_5260_);
v___x_5376_ = lean_box(0);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v___x_5376_);
v___x_5378_ = v___x_5281_;
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
lean_dec_ref(v_b_5261_);
lean_dec_ref(v_a_5260_);
v_a_5381_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5278_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5278_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5389_, lean_object* v_b_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5389_, v_b_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec(v_a_5391_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5404_, lean_object* v_b_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5404_, v_a_5407_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v_a_5419_; uint8_t v___x_5420_; lean_object* v___x_5421_; 
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_a_5419_);
lean_dec_ref_known(v___x_5418_, 1);
v___x_5420_ = 0;
lean_inc_ref(v_a_5404_);
v___x_5421_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5404_, v___x_5420_, v_a_5419_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5465_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5424_ = v___x_5421_;
v_isShared_5425_ = v_isSharedCheck_5465_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v___x_5421_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5465_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
if (lean_obj_tag(v_a_5422_) == 1)
{
lean_object* v_val_5426_; lean_object* v___x_5427_; 
lean_del_object(v___x_5424_);
v_val_5426_ = lean_ctor_get(v_a_5422_, 0);
lean_inc(v_val_5426_);
lean_dec_ref_known(v_a_5422_, 1);
v___x_5427_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5405_, v_a_5407_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_a_5428_; lean_object* v___x_5429_; 
v_a_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_a_5428_);
lean_dec_ref_known(v___x_5427_, 1);
lean_inc_ref(v_b_5405_);
v___x_5429_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5405_, v___x_5420_, v_a_5428_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5444_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5444_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5444_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
if (lean_obj_tag(v_a_5430_) == 1)
{
lean_object* v_val_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
lean_del_object(v___x_5432_);
v_val_5434_ = lean_ctor_get(v_a_5430_, 0);
lean_inc_n(v_val_5434_, 2);
lean_dec_ref_known(v_a_5430_, 1);
lean_inc(v_val_5426_);
v___x_5435_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5435_, 0, v_val_5426_);
lean_ctor_set(v___x_5435_, 1, v_val_5434_);
v___x_5436_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5435_);
v___x_5437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5437_, 0, v_a_5404_);
lean_ctor_set(v___x_5437_, 1, v_b_5405_);
lean_ctor_set(v___x_5437_, 2, v_val_5426_);
lean_ctor_set(v___x_5437_, 3, v_val_5434_);
v___x_5438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5436_);
lean_ctor_set(v___x_5438_, 1, v___x_5437_);
v___x_5439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5438_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
return v___x_5439_;
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5442_; 
lean_dec(v_a_5430_);
lean_dec(v_val_5426_);
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v___x_5440_ = lean_box(0);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5440_);
v___x_5442_ = v___x_5432_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5440_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
else
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_dec(v_val_5426_);
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v_a_5445_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5429_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5429_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5445_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
}
else
{
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5460_; 
lean_dec(v_val_5426_);
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v_a_5453_ = lean_ctor_get(v___x_5427_, 0);
v_isSharedCheck_5460_ = !lean_is_exclusive(v___x_5427_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5455_ = v___x_5427_;
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5427_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v___x_5458_; 
if (v_isShared_5456_ == 0)
{
v___x_5458_ = v___x_5455_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
else
{
lean_object* v___x_5461_; lean_object* v___x_5463_; 
lean_dec(v_a_5422_);
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v___x_5461_ = lean_box(0);
if (v_isShared_5425_ == 0)
{
lean_ctor_set(v___x_5424_, 0, v___x_5461_);
v___x_5463_ = v___x_5424_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5461_);
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
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v_a_5466_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5421_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5421_);
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
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_dec_ref(v_b_5405_);
lean_dec_ref(v_a_5404_);
v_a_5474_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5418_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5418_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5482_, lean_object* v_b_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5482_, v_b_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
lean_dec(v_a_5490_);
lean_dec_ref(v_a_5489_);
lean_dec(v_a_5488_);
lean_dec_ref(v_a_5487_);
lean_dec(v_a_5486_);
lean_dec(v_a_5485_);
lean_dec(v_a_5484_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5497_, lean_object* v_b_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_){
_start:
{
lean_object* v___x_5511_; 
v___x_5511_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
if (lean_obj_tag(v___x_5511_) == 0)
{
lean_object* v_a_5512_; lean_object* v_addRightCancelInst_x3f_5513_; 
v_a_5512_ = lean_ctor_get(v___x_5511_, 0);
lean_inc(v_a_5512_);
lean_dec_ref_known(v___x_5511_, 1);
v_addRightCancelInst_x3f_5513_ = lean_ctor_get(v_a_5512_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5513_) == 0)
{
lean_object* v___x_5514_; 
lean_dec(v_a_5512_);
v___x_5514_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5497_, v_b_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
return v___x_5514_;
}
else
{
lean_object* v_id_5515_; lean_object* v_structId_5516_; lean_object* v___x_5517_; 
v_id_5515_ = lean_ctor_get(v_a_5512_, 0);
lean_inc(v_id_5515_);
v_structId_5516_ = lean_ctor_get(v_a_5512_, 1);
lean_inc(v_structId_5516_);
lean_dec(v_a_5512_);
lean_inc_ref(v_a_5497_);
v___x_5517_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5497_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
if (lean_obj_tag(v___x_5517_) == 0)
{
lean_object* v_a_5518_; lean_object* v_fst_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5607_; 
v_a_5518_ = lean_ctor_get(v___x_5517_, 0);
lean_inc(v_a_5518_);
lean_dec_ref_known(v___x_5517_, 1);
v_fst_5519_ = lean_ctor_get(v_a_5518_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v_a_5518_);
if (v_isSharedCheck_5607_ == 0)
{
lean_object* v_unused_5608_; 
v_unused_5608_ = lean_ctor_get(v_a_5518_, 1);
lean_dec(v_unused_5608_);
v___x_5521_ = v_a_5518_;
v_isShared_5522_ = v_isSharedCheck_5607_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_fst_5519_);
lean_dec(v_a_5518_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5607_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; 
lean_inc_ref(v_b_5498_);
v___x_5523_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v_fst_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5597_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_a_5524_);
lean_dec_ref_known(v___x_5523_, 1);
v_fst_5525_ = lean_ctor_get(v_a_5524_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v_a_5524_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; 
v_unused_5598_ = lean_ctor_get(v_a_5524_, 1);
lean_dec(v_unused_5598_);
v___x_5527_ = v_a_5524_;
v_isShared_5528_ = v_isSharedCheck_5597_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_fst_5525_);
lean_dec(v_a_5524_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5597_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5529_; 
v___x_5529_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5497_, v_a_5500_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; uint8_t v___x_5531_; lean_object* v___x_5532_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
lean_inc(v_a_5530_);
lean_dec_ref_known(v___x_5529_, 1);
v___x_5531_ = 0;
v___x_5532_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5519_, v___x_5531_, v_a_5530_, v_structId_5516_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5580_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5580_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5580_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
if (lean_obj_tag(v_a_5533_) == 1)
{
lean_object* v_val_5537_; lean_object* v___x_5538_; 
lean_del_object(v___x_5535_);
v_val_5537_ = lean_ctor_get(v_a_5533_, 0);
lean_inc(v_val_5537_);
lean_dec_ref_known(v_a_5533_, 1);
v___x_5538_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5498_, v_a_5500_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; lean_object* v___x_5540_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5538_, 1);
v___x_5540_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5525_, v___x_5531_, v_a_5539_, v_structId_5516_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5559_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5543_ = v___x_5540_;
v_isShared_5544_ = v_isSharedCheck_5559_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5540_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5559_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
if (lean_obj_tag(v_a_5541_) == 1)
{
lean_object* v_val_5545_; lean_object* v___x_5547_; 
lean_del_object(v___x_5543_);
v_val_5545_ = lean_ctor_get(v_a_5541_, 0);
lean_inc_n(v_val_5545_, 2);
lean_dec_ref_known(v_a_5541_, 1);
lean_inc(v_val_5537_);
if (v_isShared_5528_ == 0)
{
lean_ctor_set_tag(v___x_5527_, 3);
lean_ctor_set(v___x_5527_, 1, v_val_5545_);
lean_ctor_set(v___x_5527_, 0, v_val_5537_);
v___x_5547_ = v___x_5527_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_val_5537_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v_val_5545_);
v___x_5547_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5548_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5547_);
v___x_5549_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5549_, 0, v_a_5497_);
lean_ctor_set(v___x_5549_, 1, v_b_5498_);
lean_ctor_set(v___x_5549_, 2, v_id_5515_);
lean_ctor_set(v___x_5549_, 3, v_val_5537_);
lean_ctor_set(v___x_5549_, 4, v_val_5545_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5549_);
lean_ctor_set(v___x_5521_, 0, v___x_5548_);
v___x_5551_ = v___x_5521_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5553_, 1, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5552_; 
v___x_5552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5551_, v_structId_5516_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
lean_dec(v_structId_5516_);
return v___x_5552_;
}
}
}
else
{
lean_object* v___x_5555_; lean_object* v___x_5557_; 
lean_dec(v_a_5541_);
lean_dec(v_val_5537_);
lean_del_object(v___x_5527_);
lean_del_object(v___x_5521_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v___x_5555_ = lean_box(0);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 0, v___x_5555_);
v___x_5557_ = v___x_5543_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
lean_dec(v_val_5537_);
lean_del_object(v___x_5527_);
lean_del_object(v___x_5521_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5560_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5540_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5540_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
lean_dec(v_val_5537_);
lean_del_object(v___x_5527_);
lean_dec(v_fst_5525_);
lean_del_object(v___x_5521_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5568_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5538_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5538_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
else
{
lean_object* v___x_5576_; lean_object* v___x_5578_; 
lean_dec(v_a_5533_);
lean_del_object(v___x_5527_);
lean_dec(v_fst_5525_);
lean_del_object(v___x_5521_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v___x_5576_ = lean_box(0);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 0, v___x_5576_);
v___x_5578_ = v___x_5535_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
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
lean_del_object(v___x_5527_);
lean_dec(v_fst_5525_);
lean_del_object(v___x_5521_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5581_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5532_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5532_);
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
lean_object* v_a_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5596_; 
lean_del_object(v___x_5527_);
lean_dec(v_fst_5525_);
lean_del_object(v___x_5521_);
lean_dec(v_fst_5519_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5589_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5591_ = v___x_5529_;
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_dec(v___x_5529_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5592_ == 0)
{
v___x_5594_ = v___x_5591_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5589_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
}
}
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
lean_del_object(v___x_5521_);
lean_dec(v_fst_5519_);
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5599_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5523_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5523_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
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
}
else
{
lean_object* v_a_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5616_; 
lean_dec(v_structId_5516_);
lean_dec(v_id_5515_);
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5609_ = lean_ctor_get(v___x_5517_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5517_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5611_ = v___x_5517_;
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_a_5609_);
lean_dec(v___x_5517_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5614_; 
if (v_isShared_5612_ == 0)
{
v___x_5614_ = v___x_5611_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_a_5609_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
}
else
{
lean_object* v_a_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5624_; 
lean_dec_ref(v_b_5498_);
lean_dec_ref(v_a_5497_);
v_a_5617_ = lean_ctor_get(v___x_5511_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5511_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5619_ = v___x_5511_;
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_a_5617_);
lean_dec(v___x_5511_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5625_, lean_object* v_b_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5625_, v_b_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
lean_dec(v_a_5637_);
lean_dec_ref(v_a_5636_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
lean_dec(v_a_5631_);
lean_dec_ref(v_a_5630_);
lean_dec(v_a_5629_);
lean_dec(v_a_5628_);
lean_dec(v_a_5627_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5640_, lean_object* v_b_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v___x_5653_; 
v___x_5653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5640_, v_b_5641_, v_a_5642_, v_a_5650_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_a_5654_);
lean_dec_ref_known(v___x_5653_, 1);
if (lean_obj_tag(v_a_5654_) == 1)
{
lean_object* v_val_5655_; lean_object* v___x_5656_; 
v_val_5655_ = lean_ctor_get(v_a_5654_, 0);
lean_inc(v_val_5655_);
lean_dec_ref_known(v_a_5654_, 1);
v___x_5656_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5655_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; uint8_t v___x_5658_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = lean_unbox(v_a_5657_);
lean_dec(v_a_5657_);
if (v___x_5658_ == 0)
{
lean_object* v___x_5659_; 
v___x_5659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5640_, v_b_5641_, v_val_5655_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
lean_dec(v_val_5655_);
return v___x_5659_;
}
else
{
lean_object* v___x_5660_; 
v___x_5660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5640_, v_b_5641_, v_val_5655_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
lean_dec(v_val_5655_);
return v___x_5660_;
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
lean_dec(v_val_5655_);
lean_dec_ref(v_b_5641_);
lean_dec_ref(v_a_5640_);
v_a_5661_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5656_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5656_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v___x_5669_; 
lean_dec(v_a_5654_);
v___x_5669_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5640_, v_b_5641_, v_a_5642_, v_a_5650_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5680_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5672_ = v___x_5669_;
v_isShared_5673_ = v_isSharedCheck_5680_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5669_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5680_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
if (lean_obj_tag(v_a_5670_) == 1)
{
lean_object* v_val_5674_; lean_object* v___x_5675_; 
lean_del_object(v___x_5672_);
v_val_5674_ = lean_ctor_get(v_a_5670_, 0);
lean_inc(v_val_5674_);
lean_dec_ref_known(v_a_5670_, 1);
v___x_5675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5640_, v_b_5641_, v_val_5674_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
lean_dec(v_val_5674_);
return v___x_5675_;
}
else
{
lean_object* v___x_5676_; lean_object* v___x_5678_; 
lean_dec(v_a_5670_);
lean_dec_ref(v_b_5641_);
lean_dec_ref(v_a_5640_);
v___x_5676_ = lean_box(0);
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 0, v___x_5676_);
v___x_5678_ = v___x_5672_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec_ref(v_b_5641_);
lean_dec_ref(v_a_5640_);
v_a_5681_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5669_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5669_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
else
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5696_; 
lean_dec_ref(v_b_5641_);
lean_dec_ref(v_a_5640_);
v_a_5689_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5691_ = v___x_5653_;
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5653_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5697_, lean_object* v_b_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5697_, v_b_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
lean_dec(v_a_5706_);
lean_dec_ref(v_a_5705_);
lean_dec(v_a_5704_);
lean_dec_ref(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_a_5701_);
lean_dec(v_a_5700_);
lean_dec(v_a_5699_);
return v_res_5710_;
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
