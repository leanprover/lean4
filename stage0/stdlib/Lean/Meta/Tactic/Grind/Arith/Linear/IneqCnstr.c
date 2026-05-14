// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.Linear.Den import Lean.Meta.Tactic.Grind.Arith.Linear.StructId import Lean.Meta.Tactic.Grind.Arith.Linear.Reify import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 219, 223, 129, 16, 82, 214, 104)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value),LEAN_SCALAR_PTR_LITERAL(30, 205, 246, 167, 183, 132, 208, 174)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__12_value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(lean_object* v_fn_x3f_1_, lean_object* v_inst_2_){
_start:
{
if (lean_obj_tag(v_fn_x3f_1_) == 1)
{
lean_object* v_val_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v_val_3_ = lean_ctor_get(v_fn_x3f_1_, 0);
v___x_4_ = l_Lean_Expr_appArg_x21(v_val_3_);
v___x_5_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_4_, v_inst_2_);
lean_dec_ref(v___x_4_);
return v___x_5_;
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 0;
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object* v_fn_x3f_7_, lean_object* v_inst_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_fn_x3f_7_, v_inst_8_);
lean_dec_ref(v_inst_8_);
lean_dec(v_fn_x3f_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(lean_object* v_c_11_, lean_object* v_x_12_, size_t v_x_13_, size_t v_x_14_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_cs_15_; size_t v_j_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_cs_15_ = lean_ctor_get(v_x_12_, 0);
v_j_16_ = lean_usize_shift_right(v_x_13_, v_x_14_);
v___x_17_ = lean_usize_to_nat(v_j_16_);
v___x_18_ = lean_array_get_size(v_cs_15_);
v___x_19_ = lean_nat_dec_lt(v___x_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_dec(v___x_17_);
lean_dec_ref(v_c_11_);
return v_x_12_;
}
else
{
lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_37_; 
lean_inc_ref(v_cs_15_);
v_isSharedCheck_37_ = !lean_is_exclusive(v_x_12_);
if (v_isSharedCheck_37_ == 0)
{
lean_object* v_unused_38_; 
v_unused_38_ = lean_ctor_get(v_x_12_, 0);
lean_dec(v_unused_38_);
v___x_21_ = v_x_12_;
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
else
{
lean_dec(v_x_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
size_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v_i_26_; size_t v___x_27_; size_t v_shift_28_; lean_object* v_v_29_; lean_object* v___x_30_; lean_object* v_xs_x27_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_23_ = ((size_t)1ULL);
v___x_24_ = lean_usize_shift_left(v___x_23_, v_x_14_);
v___x_25_ = lean_usize_sub(v___x_24_, v___x_23_);
v_i_26_ = lean_usize_land(v_x_13_, v___x_25_);
v___x_27_ = ((size_t)5ULL);
v_shift_28_ = lean_usize_sub(v_x_14_, v___x_27_);
v_v_29_ = lean_array_fget(v_cs_15_, v___x_17_);
v___x_30_ = lean_box(0);
v_xs_x27_31_ = lean_array_fset(v_cs_15_, v___x_17_, v___x_30_);
v___x_32_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_11_, v_v_29_, v_i_26_, v_shift_28_);
v___x_33_ = lean_array_fset(v_xs_x27_31_, v___x_17_, v___x_32_);
lean_dec(v___x_17_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_33_);
v___x_35_ = v___x_21_;
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
lean_object* v_vs_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_vs_39_ = lean_ctor_get(v_x_12_, 0);
v___x_40_ = lean_usize_to_nat(v_x_13_);
v___x_41_ = lean_array_get_size(v_vs_39_);
v___x_42_ = lean_nat_dec_lt(v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
lean_dec(v___x_40_);
lean_dec_ref(v_c_11_);
return v_x_12_;
}
else
{
lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_54_; 
lean_inc_ref(v_vs_39_);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_12_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v_x_12_, 0);
lean_dec(v_unused_55_);
v___x_44_ = v_x_12_;
v_isShared_45_ = v_isSharedCheck_54_;
goto v_resetjp_43_;
}
else
{
lean_dec(v_x_12_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_54_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_v_46_; lean_object* v___x_47_; lean_object* v_xs_x27_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v_v_46_ = lean_array_fget(v_vs_39_, v___x_40_);
v___x_47_ = lean_box(0);
v_xs_x27_48_ = lean_array_fset(v_vs_39_, v___x_40_, v___x_47_);
v___x_49_ = l_Lean_PersistentArray_push___redArg(v_v_46_, v_c_11_);
v___x_50_ = lean_array_fset(v_xs_x27_48_, v___x_40_, v___x_49_);
lean_dec(v___x_40_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_50_);
v___x_52_ = v___x_44_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4___boxed(lean_object* v_c_56_, lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
size_t v_x_84492__boxed_60_; size_t v_x_84493__boxed_61_; lean_object* v_res_62_; 
v_x_84492__boxed_60_ = lean_unbox_usize(v_x_58_);
lean_dec(v_x_58_);
v_x_84493__boxed_61_ = lean_unbox_usize(v_x_59_);
lean_dec(v_x_59_);
v_res_62_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_56_, v_x_57_, v_x_84492__boxed_60_, v_x_84493__boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object* v_c_63_, lean_object* v_t_64_, lean_object* v_i_65_){
_start:
{
lean_object* v_root_66_; lean_object* v_tail_67_; lean_object* v_size_68_; size_t v_shift_69_; lean_object* v_tailOff_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_94_; 
v_root_66_ = lean_ctor_get(v_t_64_, 0);
v_tail_67_ = lean_ctor_get(v_t_64_, 1);
v_size_68_ = lean_ctor_get(v_t_64_, 2);
v_shift_69_ = lean_ctor_get_usize(v_t_64_, 4);
v_tailOff_70_ = lean_ctor_get(v_t_64_, 3);
v_isSharedCheck_94_ = !lean_is_exclusive(v_t_64_);
if (v_isSharedCheck_94_ == 0)
{
v___x_72_ = v_t_64_;
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_tailOff_70_);
lean_inc(v_size_68_);
lean_inc(v_tail_67_);
lean_inc(v_root_66_);
lean_dec(v_t_64_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_le(v_tailOff_70_, v_i_65_);
if (v___x_74_ == 0)
{
size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_usize_of_nat(v_i_65_);
v___x_76_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_63_, v_root_66_, v___x_75_, v_shift_69_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_76_);
v___x_78_ = v___x_72_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_tail_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_size_68_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_tailOff_70_);
lean_ctor_set_usize(v_reuseFailAlloc_79_, 4, v_shift_69_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_nat_sub(v_i_65_, v_tailOff_70_);
v___x_81_ = lean_array_get_size(v_tail_67_);
v___x_82_ = lean_nat_dec_lt(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_84_; 
lean_dec(v___x_80_);
lean_dec_ref(v_c_63_);
if (v_isShared_73_ == 0)
{
v___x_84_ = v___x_72_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_root_66_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_tail_67_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_size_68_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_tailOff_70_);
lean_ctor_set_usize(v_reuseFailAlloc_85_, 4, v_shift_69_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v_v_86_; lean_object* v___x_87_; lean_object* v_xs_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v_v_86_ = lean_array_fget(v_tail_67_, v___x_80_);
v___x_87_ = lean_box(0);
v_xs_x27_88_ = lean_array_fset(v_tail_67_, v___x_80_, v___x_87_);
v___x_89_ = l_Lean_PersistentArray_push___redArg(v_v_86_, v_c_63_);
v___x_90_ = lean_array_fset(v_xs_x27_88_, v___x_80_, v___x_89_);
lean_dec(v___x_80_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_90_);
v___x_92_ = v___x_72_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_root_66_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_size_68_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v_tailOff_70_);
lean_ctor_set_usize(v_reuseFailAlloc_93_, 4, v_shift_69_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object* v_c_95_, lean_object* v_t_96_, lean_object* v_i_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_95_, v_t_96_, v_i_97_);
lean_dec(v_i_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object* v___y_99_, lean_object* v_c_100_, lean_object* v_v_101_, lean_object* v_s_102_){
_start:
{
lean_object* v_structs_103_; lean_object* v_typeIdOf_104_; lean_object* v_exprToStructId_105_; lean_object* v_exprToStructIdEntries_106_; lean_object* v_forbiddenNatModules_107_; lean_object* v_natStructs_108_; lean_object* v_natTypeIdOf_109_; lean_object* v_exprToNatStructId_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_structs_103_ = lean_ctor_get(v_s_102_, 0);
v_typeIdOf_104_ = lean_ctor_get(v_s_102_, 1);
v_exprToStructId_105_ = lean_ctor_get(v_s_102_, 2);
v_exprToStructIdEntries_106_ = lean_ctor_get(v_s_102_, 3);
v_forbiddenNatModules_107_ = lean_ctor_get(v_s_102_, 4);
v_natStructs_108_ = lean_ctor_get(v_s_102_, 5);
v_natTypeIdOf_109_ = lean_ctor_get(v_s_102_, 6);
v_exprToNatStructId_110_ = lean_ctor_get(v_s_102_, 7);
v___x_111_ = lean_array_get_size(v_structs_103_);
v___x_112_ = lean_nat_dec_lt(v___y_99_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_c_100_);
return v_s_102_;
}
else
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_174_; 
lean_inc_ref(v_exprToNatStructId_110_);
lean_inc_ref(v_natTypeIdOf_109_);
lean_inc_ref(v_natStructs_108_);
lean_inc_ref(v_forbiddenNatModules_107_);
lean_inc_ref(v_exprToStructIdEntries_106_);
lean_inc_ref(v_exprToStructId_105_);
lean_inc_ref(v_typeIdOf_104_);
lean_inc_ref(v_structs_103_);
v_isSharedCheck_174_ = !lean_is_exclusive(v_s_102_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; 
v_unused_175_ = lean_ctor_get(v_s_102_, 7);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_s_102_, 6);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_s_102_, 5);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_s_102_, 4);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_s_102_, 3);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_s_102_, 2);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_s_102_, 1);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_s_102_, 0);
lean_dec(v_unused_182_);
v___x_114_ = v_s_102_;
v_isShared_115_ = v_isSharedCheck_174_;
goto v_resetjp_113_;
}
else
{
lean_dec(v_s_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_174_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_v_116_; lean_object* v_id_117_; lean_object* v_ringId_x3f_118_; lean_object* v_type_119_; lean_object* v_u_120_; lean_object* v_intModuleInst_121_; lean_object* v_leInst_x3f_122_; lean_object* v_ltInst_x3f_123_; lean_object* v_lawfulOrderLTInst_x3f_124_; lean_object* v_isPreorderInst_x3f_125_; lean_object* v_orderedAddInst_x3f_126_; lean_object* v_isLinearInst_x3f_127_; lean_object* v_noNatDivInst_x3f_128_; lean_object* v_ringInst_x3f_129_; lean_object* v_commRingInst_x3f_130_; lean_object* v_orderedRingInst_x3f_131_; lean_object* v_fieldInst_x3f_132_; lean_object* v_charInst_x3f_133_; lean_object* v_zero_134_; lean_object* v_ofNatZero_135_; lean_object* v_one_x3f_136_; lean_object* v_leFn_x3f_137_; lean_object* v_ltFn_x3f_138_; lean_object* v_addFn_139_; lean_object* v_zsmulFn_140_; lean_object* v_nsmulFn_141_; lean_object* v_zsmulFn_x3f_142_; lean_object* v_nsmulFn_x3f_143_; lean_object* v_homomulFn_x3f_144_; lean_object* v_subFn_145_; lean_object* v_negFn_146_; lean_object* v_vars_147_; lean_object* v_varMap_148_; lean_object* v_lowers_149_; lean_object* v_uppers_150_; lean_object* v_diseqs_151_; lean_object* v_assignment_152_; uint8_t v_caseSplits_153_; lean_object* v_conflict_x3f_154_; lean_object* v_diseqSplits_155_; lean_object* v_elimEqs_156_; lean_object* v_elimStack_157_; lean_object* v_occurs_158_; lean_object* v_ignored_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_173_; 
v_v_116_ = lean_array_fget(v_structs_103_, v___y_99_);
v_id_117_ = lean_ctor_get(v_v_116_, 0);
v_ringId_x3f_118_ = lean_ctor_get(v_v_116_, 1);
v_type_119_ = lean_ctor_get(v_v_116_, 2);
v_u_120_ = lean_ctor_get(v_v_116_, 3);
v_intModuleInst_121_ = lean_ctor_get(v_v_116_, 4);
v_leInst_x3f_122_ = lean_ctor_get(v_v_116_, 5);
v_ltInst_x3f_123_ = lean_ctor_get(v_v_116_, 6);
v_lawfulOrderLTInst_x3f_124_ = lean_ctor_get(v_v_116_, 7);
v_isPreorderInst_x3f_125_ = lean_ctor_get(v_v_116_, 8);
v_orderedAddInst_x3f_126_ = lean_ctor_get(v_v_116_, 9);
v_isLinearInst_x3f_127_ = lean_ctor_get(v_v_116_, 10);
v_noNatDivInst_x3f_128_ = lean_ctor_get(v_v_116_, 11);
v_ringInst_x3f_129_ = lean_ctor_get(v_v_116_, 12);
v_commRingInst_x3f_130_ = lean_ctor_get(v_v_116_, 13);
v_orderedRingInst_x3f_131_ = lean_ctor_get(v_v_116_, 14);
v_fieldInst_x3f_132_ = lean_ctor_get(v_v_116_, 15);
v_charInst_x3f_133_ = lean_ctor_get(v_v_116_, 16);
v_zero_134_ = lean_ctor_get(v_v_116_, 17);
v_ofNatZero_135_ = lean_ctor_get(v_v_116_, 18);
v_one_x3f_136_ = lean_ctor_get(v_v_116_, 19);
v_leFn_x3f_137_ = lean_ctor_get(v_v_116_, 20);
v_ltFn_x3f_138_ = lean_ctor_get(v_v_116_, 21);
v_addFn_139_ = lean_ctor_get(v_v_116_, 22);
v_zsmulFn_140_ = lean_ctor_get(v_v_116_, 23);
v_nsmulFn_141_ = lean_ctor_get(v_v_116_, 24);
v_zsmulFn_x3f_142_ = lean_ctor_get(v_v_116_, 25);
v_nsmulFn_x3f_143_ = lean_ctor_get(v_v_116_, 26);
v_homomulFn_x3f_144_ = lean_ctor_get(v_v_116_, 27);
v_subFn_145_ = lean_ctor_get(v_v_116_, 28);
v_negFn_146_ = lean_ctor_get(v_v_116_, 29);
v_vars_147_ = lean_ctor_get(v_v_116_, 30);
v_varMap_148_ = lean_ctor_get(v_v_116_, 31);
v_lowers_149_ = lean_ctor_get(v_v_116_, 32);
v_uppers_150_ = lean_ctor_get(v_v_116_, 33);
v_diseqs_151_ = lean_ctor_get(v_v_116_, 34);
v_assignment_152_ = lean_ctor_get(v_v_116_, 35);
v_caseSplits_153_ = lean_ctor_get_uint8(v_v_116_, sizeof(void*)*42);
v_conflict_x3f_154_ = lean_ctor_get(v_v_116_, 36);
v_diseqSplits_155_ = lean_ctor_get(v_v_116_, 37);
v_elimEqs_156_ = lean_ctor_get(v_v_116_, 38);
v_elimStack_157_ = lean_ctor_get(v_v_116_, 39);
v_occurs_158_ = lean_ctor_get(v_v_116_, 40);
v_ignored_159_ = lean_ctor_get(v_v_116_, 41);
v_isSharedCheck_173_ = !lean_is_exclusive(v_v_116_);
if (v_isSharedCheck_173_ == 0)
{
v___x_161_ = v_v_116_;
v_isShared_162_ = v_isSharedCheck_173_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_ignored_159_);
lean_inc(v_occurs_158_);
lean_inc(v_elimStack_157_);
lean_inc(v_elimEqs_156_);
lean_inc(v_diseqSplits_155_);
lean_inc(v_conflict_x3f_154_);
lean_inc(v_assignment_152_);
lean_inc(v_diseqs_151_);
lean_inc(v_uppers_150_);
lean_inc(v_lowers_149_);
lean_inc(v_varMap_148_);
lean_inc(v_vars_147_);
lean_inc(v_negFn_146_);
lean_inc(v_subFn_145_);
lean_inc(v_homomulFn_x3f_144_);
lean_inc(v_nsmulFn_x3f_143_);
lean_inc(v_zsmulFn_x3f_142_);
lean_inc(v_nsmulFn_141_);
lean_inc(v_zsmulFn_140_);
lean_inc(v_addFn_139_);
lean_inc(v_ltFn_x3f_138_);
lean_inc(v_leFn_x3f_137_);
lean_inc(v_one_x3f_136_);
lean_inc(v_ofNatZero_135_);
lean_inc(v_zero_134_);
lean_inc(v_charInst_x3f_133_);
lean_inc(v_fieldInst_x3f_132_);
lean_inc(v_orderedRingInst_x3f_131_);
lean_inc(v_commRingInst_x3f_130_);
lean_inc(v_ringInst_x3f_129_);
lean_inc(v_noNatDivInst_x3f_128_);
lean_inc(v_isLinearInst_x3f_127_);
lean_inc(v_orderedAddInst_x3f_126_);
lean_inc(v_isPreorderInst_x3f_125_);
lean_inc(v_lawfulOrderLTInst_x3f_124_);
lean_inc(v_ltInst_x3f_123_);
lean_inc(v_leInst_x3f_122_);
lean_inc(v_intModuleInst_121_);
lean_inc(v_u_120_);
lean_inc(v_type_119_);
lean_inc(v_ringId_x3f_118_);
lean_inc(v_id_117_);
lean_dec(v_v_116_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_173_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v_xs_x27_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_163_ = lean_box(0);
v_xs_x27_164_ = lean_array_fset(v_structs_103_, v___y_99_, v___x_163_);
v___x_165_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_100_, v_uppers_150_, v_v_101_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 33, v___x_165_);
v___x_167_ = v___x_161_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_id_117_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_ringId_x3f_118_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_type_119_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_u_120_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_intModuleInst_121_);
lean_ctor_set(v_reuseFailAlloc_172_, 5, v_leInst_x3f_122_);
lean_ctor_set(v_reuseFailAlloc_172_, 6, v_ltInst_x3f_123_);
lean_ctor_set(v_reuseFailAlloc_172_, 7, v_lawfulOrderLTInst_x3f_124_);
lean_ctor_set(v_reuseFailAlloc_172_, 8, v_isPreorderInst_x3f_125_);
lean_ctor_set(v_reuseFailAlloc_172_, 9, v_orderedAddInst_x3f_126_);
lean_ctor_set(v_reuseFailAlloc_172_, 10, v_isLinearInst_x3f_127_);
lean_ctor_set(v_reuseFailAlloc_172_, 11, v_noNatDivInst_x3f_128_);
lean_ctor_set(v_reuseFailAlloc_172_, 12, v_ringInst_x3f_129_);
lean_ctor_set(v_reuseFailAlloc_172_, 13, v_commRingInst_x3f_130_);
lean_ctor_set(v_reuseFailAlloc_172_, 14, v_orderedRingInst_x3f_131_);
lean_ctor_set(v_reuseFailAlloc_172_, 15, v_fieldInst_x3f_132_);
lean_ctor_set(v_reuseFailAlloc_172_, 16, v_charInst_x3f_133_);
lean_ctor_set(v_reuseFailAlloc_172_, 17, v_zero_134_);
lean_ctor_set(v_reuseFailAlloc_172_, 18, v_ofNatZero_135_);
lean_ctor_set(v_reuseFailAlloc_172_, 19, v_one_x3f_136_);
lean_ctor_set(v_reuseFailAlloc_172_, 20, v_leFn_x3f_137_);
lean_ctor_set(v_reuseFailAlloc_172_, 21, v_ltFn_x3f_138_);
lean_ctor_set(v_reuseFailAlloc_172_, 22, v_addFn_139_);
lean_ctor_set(v_reuseFailAlloc_172_, 23, v_zsmulFn_140_);
lean_ctor_set(v_reuseFailAlloc_172_, 24, v_nsmulFn_141_);
lean_ctor_set(v_reuseFailAlloc_172_, 25, v_zsmulFn_x3f_142_);
lean_ctor_set(v_reuseFailAlloc_172_, 26, v_nsmulFn_x3f_143_);
lean_ctor_set(v_reuseFailAlloc_172_, 27, v_homomulFn_x3f_144_);
lean_ctor_set(v_reuseFailAlloc_172_, 28, v_subFn_145_);
lean_ctor_set(v_reuseFailAlloc_172_, 29, v_negFn_146_);
lean_ctor_set(v_reuseFailAlloc_172_, 30, v_vars_147_);
lean_ctor_set(v_reuseFailAlloc_172_, 31, v_varMap_148_);
lean_ctor_set(v_reuseFailAlloc_172_, 32, v_lowers_149_);
lean_ctor_set(v_reuseFailAlloc_172_, 33, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_172_, 34, v_diseqs_151_);
lean_ctor_set(v_reuseFailAlloc_172_, 35, v_assignment_152_);
lean_ctor_set(v_reuseFailAlloc_172_, 36, v_conflict_x3f_154_);
lean_ctor_set(v_reuseFailAlloc_172_, 37, v_diseqSplits_155_);
lean_ctor_set(v_reuseFailAlloc_172_, 38, v_elimEqs_156_);
lean_ctor_set(v_reuseFailAlloc_172_, 39, v_elimStack_157_);
lean_ctor_set(v_reuseFailAlloc_172_, 40, v_occurs_158_);
lean_ctor_set(v_reuseFailAlloc_172_, 41, v_ignored_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*42, v_caseSplits_153_);
v___x_167_ = v_reuseFailAlloc_172_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_array_fset(v_xs_x27_164_, v___y_99_, v___x_167_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_168_);
v___x_170_ = v___x_114_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_typeIdOf_104_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_exprToStructId_105_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_exprToStructIdEntries_106_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_forbiddenNatModules_107_);
lean_ctor_set(v_reuseFailAlloc_171_, 5, v_natStructs_108_);
lean_ctor_set(v_reuseFailAlloc_171_, 6, v_natTypeIdOf_109_);
lean_ctor_set(v_reuseFailAlloc_171_, 7, v_exprToNatStructId_110_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object* v___y_183_, lean_object* v_c_184_, lean_object* v_v_185_, lean_object* v_s_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(v___y_183_, v_c_184_, v_v_185_, v_s_186_);
lean_dec(v_v_185_);
lean_dec(v___y_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object* v___y_188_, lean_object* v_c_189_, lean_object* v_v_190_, lean_object* v_s_191_){
_start:
{
lean_object* v_structs_192_; lean_object* v_typeIdOf_193_; lean_object* v_exprToStructId_194_; lean_object* v_exprToStructIdEntries_195_; lean_object* v_forbiddenNatModules_196_; lean_object* v_natStructs_197_; lean_object* v_natTypeIdOf_198_; lean_object* v_exprToNatStructId_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_structs_192_ = lean_ctor_get(v_s_191_, 0);
v_typeIdOf_193_ = lean_ctor_get(v_s_191_, 1);
v_exprToStructId_194_ = lean_ctor_get(v_s_191_, 2);
v_exprToStructIdEntries_195_ = lean_ctor_get(v_s_191_, 3);
v_forbiddenNatModules_196_ = lean_ctor_get(v_s_191_, 4);
v_natStructs_197_ = lean_ctor_get(v_s_191_, 5);
v_natTypeIdOf_198_ = lean_ctor_get(v_s_191_, 6);
v_exprToNatStructId_199_ = lean_ctor_get(v_s_191_, 7);
v___x_200_ = lean_array_get_size(v_structs_192_);
v___x_201_ = lean_nat_dec_lt(v___y_188_, v___x_200_);
if (v___x_201_ == 0)
{
lean_dec_ref(v_c_189_);
return v_s_191_;
}
else
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_263_; 
lean_inc_ref(v_exprToNatStructId_199_);
lean_inc_ref(v_natTypeIdOf_198_);
lean_inc_ref(v_natStructs_197_);
lean_inc_ref(v_forbiddenNatModules_196_);
lean_inc_ref(v_exprToStructIdEntries_195_);
lean_inc_ref(v_exprToStructId_194_);
lean_inc_ref(v_typeIdOf_193_);
lean_inc_ref(v_structs_192_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_s_191_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_264_ = lean_ctor_get(v_s_191_, 7);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_s_191_, 6);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_s_191_, 5);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_s_191_, 4);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_s_191_, 3);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_s_191_, 2);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_s_191_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_s_191_, 0);
lean_dec(v_unused_271_);
v___x_203_ = v_s_191_;
v_isShared_204_ = v_isSharedCheck_263_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_s_191_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_263_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_v_205_; lean_object* v_id_206_; lean_object* v_ringId_x3f_207_; lean_object* v_type_208_; lean_object* v_u_209_; lean_object* v_intModuleInst_210_; lean_object* v_leInst_x3f_211_; lean_object* v_ltInst_x3f_212_; lean_object* v_lawfulOrderLTInst_x3f_213_; lean_object* v_isPreorderInst_x3f_214_; lean_object* v_orderedAddInst_x3f_215_; lean_object* v_isLinearInst_x3f_216_; lean_object* v_noNatDivInst_x3f_217_; lean_object* v_ringInst_x3f_218_; lean_object* v_commRingInst_x3f_219_; lean_object* v_orderedRingInst_x3f_220_; lean_object* v_fieldInst_x3f_221_; lean_object* v_charInst_x3f_222_; lean_object* v_zero_223_; lean_object* v_ofNatZero_224_; lean_object* v_one_x3f_225_; lean_object* v_leFn_x3f_226_; lean_object* v_ltFn_x3f_227_; lean_object* v_addFn_228_; lean_object* v_zsmulFn_229_; lean_object* v_nsmulFn_230_; lean_object* v_zsmulFn_x3f_231_; lean_object* v_nsmulFn_x3f_232_; lean_object* v_homomulFn_x3f_233_; lean_object* v_subFn_234_; lean_object* v_negFn_235_; lean_object* v_vars_236_; lean_object* v_varMap_237_; lean_object* v_lowers_238_; lean_object* v_uppers_239_; lean_object* v_diseqs_240_; lean_object* v_assignment_241_; uint8_t v_caseSplits_242_; lean_object* v_conflict_x3f_243_; lean_object* v_diseqSplits_244_; lean_object* v_elimEqs_245_; lean_object* v_elimStack_246_; lean_object* v_occurs_247_; lean_object* v_ignored_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_262_; 
v_v_205_ = lean_array_fget(v_structs_192_, v___y_188_);
v_id_206_ = lean_ctor_get(v_v_205_, 0);
v_ringId_x3f_207_ = lean_ctor_get(v_v_205_, 1);
v_type_208_ = lean_ctor_get(v_v_205_, 2);
v_u_209_ = lean_ctor_get(v_v_205_, 3);
v_intModuleInst_210_ = lean_ctor_get(v_v_205_, 4);
v_leInst_x3f_211_ = lean_ctor_get(v_v_205_, 5);
v_ltInst_x3f_212_ = lean_ctor_get(v_v_205_, 6);
v_lawfulOrderLTInst_x3f_213_ = lean_ctor_get(v_v_205_, 7);
v_isPreorderInst_x3f_214_ = lean_ctor_get(v_v_205_, 8);
v_orderedAddInst_x3f_215_ = lean_ctor_get(v_v_205_, 9);
v_isLinearInst_x3f_216_ = lean_ctor_get(v_v_205_, 10);
v_noNatDivInst_x3f_217_ = lean_ctor_get(v_v_205_, 11);
v_ringInst_x3f_218_ = lean_ctor_get(v_v_205_, 12);
v_commRingInst_x3f_219_ = lean_ctor_get(v_v_205_, 13);
v_orderedRingInst_x3f_220_ = lean_ctor_get(v_v_205_, 14);
v_fieldInst_x3f_221_ = lean_ctor_get(v_v_205_, 15);
v_charInst_x3f_222_ = lean_ctor_get(v_v_205_, 16);
v_zero_223_ = lean_ctor_get(v_v_205_, 17);
v_ofNatZero_224_ = lean_ctor_get(v_v_205_, 18);
v_one_x3f_225_ = lean_ctor_get(v_v_205_, 19);
v_leFn_x3f_226_ = lean_ctor_get(v_v_205_, 20);
v_ltFn_x3f_227_ = lean_ctor_get(v_v_205_, 21);
v_addFn_228_ = lean_ctor_get(v_v_205_, 22);
v_zsmulFn_229_ = lean_ctor_get(v_v_205_, 23);
v_nsmulFn_230_ = lean_ctor_get(v_v_205_, 24);
v_zsmulFn_x3f_231_ = lean_ctor_get(v_v_205_, 25);
v_nsmulFn_x3f_232_ = lean_ctor_get(v_v_205_, 26);
v_homomulFn_x3f_233_ = lean_ctor_get(v_v_205_, 27);
v_subFn_234_ = lean_ctor_get(v_v_205_, 28);
v_negFn_235_ = lean_ctor_get(v_v_205_, 29);
v_vars_236_ = lean_ctor_get(v_v_205_, 30);
v_varMap_237_ = lean_ctor_get(v_v_205_, 31);
v_lowers_238_ = lean_ctor_get(v_v_205_, 32);
v_uppers_239_ = lean_ctor_get(v_v_205_, 33);
v_diseqs_240_ = lean_ctor_get(v_v_205_, 34);
v_assignment_241_ = lean_ctor_get(v_v_205_, 35);
v_caseSplits_242_ = lean_ctor_get_uint8(v_v_205_, sizeof(void*)*42);
v_conflict_x3f_243_ = lean_ctor_get(v_v_205_, 36);
v_diseqSplits_244_ = lean_ctor_get(v_v_205_, 37);
v_elimEqs_245_ = lean_ctor_get(v_v_205_, 38);
v_elimStack_246_ = lean_ctor_get(v_v_205_, 39);
v_occurs_247_ = lean_ctor_get(v_v_205_, 40);
v_ignored_248_ = lean_ctor_get(v_v_205_, 41);
v_isSharedCheck_262_ = !lean_is_exclusive(v_v_205_);
if (v_isSharedCheck_262_ == 0)
{
v___x_250_ = v_v_205_;
v_isShared_251_ = v_isSharedCheck_262_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_ignored_248_);
lean_inc(v_occurs_247_);
lean_inc(v_elimStack_246_);
lean_inc(v_elimEqs_245_);
lean_inc(v_diseqSplits_244_);
lean_inc(v_conflict_x3f_243_);
lean_inc(v_assignment_241_);
lean_inc(v_diseqs_240_);
lean_inc(v_uppers_239_);
lean_inc(v_lowers_238_);
lean_inc(v_varMap_237_);
lean_inc(v_vars_236_);
lean_inc(v_negFn_235_);
lean_inc(v_subFn_234_);
lean_inc(v_homomulFn_x3f_233_);
lean_inc(v_nsmulFn_x3f_232_);
lean_inc(v_zsmulFn_x3f_231_);
lean_inc(v_nsmulFn_230_);
lean_inc(v_zsmulFn_229_);
lean_inc(v_addFn_228_);
lean_inc(v_ltFn_x3f_227_);
lean_inc(v_leFn_x3f_226_);
lean_inc(v_one_x3f_225_);
lean_inc(v_ofNatZero_224_);
lean_inc(v_zero_223_);
lean_inc(v_charInst_x3f_222_);
lean_inc(v_fieldInst_x3f_221_);
lean_inc(v_orderedRingInst_x3f_220_);
lean_inc(v_commRingInst_x3f_219_);
lean_inc(v_ringInst_x3f_218_);
lean_inc(v_noNatDivInst_x3f_217_);
lean_inc(v_isLinearInst_x3f_216_);
lean_inc(v_orderedAddInst_x3f_215_);
lean_inc(v_isPreorderInst_x3f_214_);
lean_inc(v_lawfulOrderLTInst_x3f_213_);
lean_inc(v_ltInst_x3f_212_);
lean_inc(v_leInst_x3f_211_);
lean_inc(v_intModuleInst_210_);
lean_inc(v_u_209_);
lean_inc(v_type_208_);
lean_inc(v_ringId_x3f_207_);
lean_inc(v_id_206_);
lean_dec(v_v_205_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_262_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v_xs_x27_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_252_ = lean_box(0);
v_xs_x27_253_ = lean_array_fset(v_structs_192_, v___y_188_, v___x_252_);
v___x_254_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_189_, v_lowers_238_, v_v_190_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 32, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_id_206_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_ringId_x3f_207_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_type_208_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_u_209_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_intModuleInst_210_);
lean_ctor_set(v_reuseFailAlloc_261_, 5, v_leInst_x3f_211_);
lean_ctor_set(v_reuseFailAlloc_261_, 6, v_ltInst_x3f_212_);
lean_ctor_set(v_reuseFailAlloc_261_, 7, v_lawfulOrderLTInst_x3f_213_);
lean_ctor_set(v_reuseFailAlloc_261_, 8, v_isPreorderInst_x3f_214_);
lean_ctor_set(v_reuseFailAlloc_261_, 9, v_orderedAddInst_x3f_215_);
lean_ctor_set(v_reuseFailAlloc_261_, 10, v_isLinearInst_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_261_, 11, v_noNatDivInst_x3f_217_);
lean_ctor_set(v_reuseFailAlloc_261_, 12, v_ringInst_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_261_, 13, v_commRingInst_x3f_219_);
lean_ctor_set(v_reuseFailAlloc_261_, 14, v_orderedRingInst_x3f_220_);
lean_ctor_set(v_reuseFailAlloc_261_, 15, v_fieldInst_x3f_221_);
lean_ctor_set(v_reuseFailAlloc_261_, 16, v_charInst_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_261_, 17, v_zero_223_);
lean_ctor_set(v_reuseFailAlloc_261_, 18, v_ofNatZero_224_);
lean_ctor_set(v_reuseFailAlloc_261_, 19, v_one_x3f_225_);
lean_ctor_set(v_reuseFailAlloc_261_, 20, v_leFn_x3f_226_);
lean_ctor_set(v_reuseFailAlloc_261_, 21, v_ltFn_x3f_227_);
lean_ctor_set(v_reuseFailAlloc_261_, 22, v_addFn_228_);
lean_ctor_set(v_reuseFailAlloc_261_, 23, v_zsmulFn_229_);
lean_ctor_set(v_reuseFailAlloc_261_, 24, v_nsmulFn_230_);
lean_ctor_set(v_reuseFailAlloc_261_, 25, v_zsmulFn_x3f_231_);
lean_ctor_set(v_reuseFailAlloc_261_, 26, v_nsmulFn_x3f_232_);
lean_ctor_set(v_reuseFailAlloc_261_, 27, v_homomulFn_x3f_233_);
lean_ctor_set(v_reuseFailAlloc_261_, 28, v_subFn_234_);
lean_ctor_set(v_reuseFailAlloc_261_, 29, v_negFn_235_);
lean_ctor_set(v_reuseFailAlloc_261_, 30, v_vars_236_);
lean_ctor_set(v_reuseFailAlloc_261_, 31, v_varMap_237_);
lean_ctor_set(v_reuseFailAlloc_261_, 32, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 33, v_uppers_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 34, v_diseqs_240_);
lean_ctor_set(v_reuseFailAlloc_261_, 35, v_assignment_241_);
lean_ctor_set(v_reuseFailAlloc_261_, 36, v_conflict_x3f_243_);
lean_ctor_set(v_reuseFailAlloc_261_, 37, v_diseqSplits_244_);
lean_ctor_set(v_reuseFailAlloc_261_, 38, v_elimEqs_245_);
lean_ctor_set(v_reuseFailAlloc_261_, 39, v_elimStack_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 40, v_occurs_247_);
lean_ctor_set(v_reuseFailAlloc_261_, 41, v_ignored_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*42, v_caseSplits_242_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_array_fset(v_xs_x27_253_, v___y_188_, v___x_256_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_257_);
v___x_259_ = v___x_203_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_typeIdOf_193_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_exprToStructId_194_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_exprToStructIdEntries_195_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_forbiddenNatModules_196_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_natStructs_197_);
lean_ctor_set(v_reuseFailAlloc_260_, 6, v_natTypeIdOf_198_);
lean_ctor_set(v_reuseFailAlloc_260_, 7, v_exprToNatStructId_199_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object* v___y_272_, lean_object* v_c_273_, lean_object* v_v_274_, lean_object* v_s_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(v___y_272_, v_c_273_, v_v_274_, v_s_275_);
lean_dec(v_v_274_);
lean_dec(v___y_272_);
return v_res_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(lean_object* v_k_279_, lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0);
v___x_294_ = lean_int_dec_eq(v_k_279_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_316_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_316_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_vars_302_; lean_object* v_zsmulFn_303_; lean_object* v_size_304_; lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_vars_302_ = lean_ctor_get(v_a_298_, 30);
lean_inc_ref(v_vars_302_);
lean_dec(v_a_298_);
v_zsmulFn_303_ = lean_ctor_get(v_a_296_, 23);
lean_inc_ref(v_zsmulFn_303_);
lean_dec(v_a_296_);
v_size_304_ = lean_ctor_get(v_vars_302_, 2);
v___x_305_ = l_Lean_mkIntLit(v_k_279_);
v___x_312_ = l_Lean_instInhabitedExpr;
v___x_313_ = lean_nat_dec_lt(v_x_280_, v_size_304_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v_vars_302_);
v___x_314_ = l_outOfBounds___redArg(v___x_312_);
v___y_307_ = v___x_314_;
goto v___jp_306_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentArray_get_x21___redArg(v___x_312_, v_vars_302_, v_x_280_);
lean_dec_ref(v_vars_302_);
v___y_307_ = v___x_315_;
goto v___jp_306_;
}
v___jp_306_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = l_Lean_mkAppB(v_zsmulFn_303_, v___x_305_, v___y_307_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_308_);
v___x_310_ = v___x_300_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_a_296_);
v_a_317_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_297_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_297_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_325_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_295_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_295_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_350_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_vars_338_; lean_object* v_size_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_vars_338_ = lean_ctor_get(v_a_334_, 30);
lean_inc_ref(v_vars_338_);
lean_dec(v_a_334_);
v_size_339_ = lean_ctor_get(v_vars_338_, 2);
v___x_340_ = l_Lean_instInhabitedExpr;
v___x_341_ = lean_nat_dec_lt(v_x_280_, v_size_339_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec_ref(v_vars_338_);
v___x_342_ = l_outOfBounds___redArg(v___x_340_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_342_);
v___x_344_ = v___x_336_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = l_Lean_PersistentArray_get_x21___redArg(v___x_340_, v_vars_338_, v_x_280_);
lean_dec_ref(v_vars_338_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_346_);
v___x_348_ = v___x_336_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_333_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_333_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_k_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_359_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v___y_361_);
lean_dec(v_x_360_);
lean_dec(v_k_359_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(lean_object* v_p_374_, lean_object* v_acc_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
if (lean_obj_tag(v_p_374_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_acc_375_);
return v___x_388_;
}
else
{
lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; lean_object* v___x_392_; 
v_k_389_ = lean_ctor_get(v_p_374_, 0);
v_v_390_ = lean_ctor_get(v_p_374_, 1);
v_p_391_ = lean_ctor_get(v_p_374_, 2);
v___x_392_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref(v___x_392_);
v___x_394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_389_, v_v_390_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_addFn_396_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v___x_394_);
v_addFn_396_ = lean_ctor_get(v_a_393_, 22);
lean_inc_ref(v_addFn_396_);
lean_dec(v_a_393_);
v___x_397_ = l_Lean_mkAppB(v_addFn_396_, v_acc_375_, v_a_395_);
v_p_374_ = v_p_391_;
v_acc_375_ = v___x_397_;
goto _start;
}
else
{
lean_dec(v_a_393_);
lean_dec_ref(v_acc_375_);
return v___x_394_;
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_acc_375_);
v_a_399_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_392_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_392_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(lean_object* v_p_407_, lean_object* v_acc_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_407_, v_acc_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
lean_dec(v___y_409_);
lean_dec(v_p_407_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(lean_object* v_p_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
if (lean_obj_tag(v_p_422_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_zero_440_; lean_object* v___x_442_; 
v_zero_440_ = lean_ctor_get(v_a_436_, 17);
lean_inc_ref(v_zero_440_);
lean_dec(v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_zero_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_zero_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_a_445_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_435_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_k_453_; lean_object* v_v_454_; lean_object* v_p_455_; lean_object* v___x_456_; 
v_k_453_ = lean_ctor_get(v_p_422_, 0);
v_v_454_ = lean_ctor_get(v_p_422_, 1);
v_p_455_ = lean_ctor_get(v_p_422_, 2);
v___x_456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_453_, v_v_454_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_455_, v_a_457_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_458_;
}
else
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_p_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec(v_p_459_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(lean_object* v_msgData_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v_env_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_lctx_483_; lean_object* v_options_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_env_480_);
lean_dec(v___x_479_);
v___x_481_ = lean_st_ref_get(v___y_475_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_mctx_482_);
lean_dec(v___x_481_);
v_lctx_483_ = lean_ctor_get(v___y_474_, 2);
v_options_484_ = lean_ctor_get(v___y_476_, 2);
lean_inc_ref(v_options_484_);
lean_inc_ref(v_lctx_483_);
v___x_485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_485_, 0, v_env_480_);
lean_ctor_set(v___x_485_, 1, v_mctx_482_);
lean_ctor_set(v___x_485_, 2, v_lctx_483_);
lean_ctor_set(v___x_485_, 3, v_options_484_);
v___x_486_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_msgData_473_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object* v_msgData_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_ref_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_ref_501_ = lean_ctor_get(v___y_498_, 5);
v___x_502_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_inc(v_ref_501_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_ref_501_);
lean_ctor_set(v___x_507_, 1, v_a_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 1);
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_msg_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_546_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_ltFn_x3f_539_; 
v_ltFn_x3f_539_ = lean_ctor_get(v_a_535_, 21);
lean_inc(v_ltFn_x3f_539_);
lean_dec(v_a_535_);
if (lean_obj_tag(v_ltFn_x3f_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; 
v_val_540_ = lean_ctor_get(v_ltFn_x3f_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v_ltFn_x3f_539_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_val_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_val_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_ltFn_x3f_539_);
lean_del_object(v___x_537_);
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
v___x_545_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_544_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_545_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_534_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_534_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
return v_res_567_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_595_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_595_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_leFn_x3f_588_; 
v_leFn_x3f_588_ = lean_ctor_get(v_a_584_, 20);
lean_inc(v_leFn_x3f_588_);
lean_dec(v_a_584_);
if (lean_obj_tag(v_leFn_x3f_588_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_591_; 
v_val_589_ = lean_ctor_get(v_leFn_x3f_588_, 0);
lean_inc(v_val_589_);
lean_dec_ref(v_leFn_x3f_588_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_val_589_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_val_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_leFn_x3f_588_);
lean_del_object(v___x_586_);
v___x_593_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
v___x_594_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_593_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_594_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_583_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_583_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v___y_604_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object* v_p_617_, uint8_t v_strict_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
if (v_strict_618_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_617_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_ofNatZero_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v_ofNatZero_640_ = lean_ctor_get(v_a_636_, 18);
lean_inc_ref(v_ofNatZero_640_);
lean_dec(v_a_636_);
v___x_641_ = l_Lean_mkAppB(v_a_632_, v_a_634_, v_ofNatZero_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_634_);
lean_dec(v_a_632_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_dec(v_a_632_);
return v___x_633_;
}
}
else
{
return v___x_631_;
}
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_617_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v___x_656_);
v___x_658_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_ofNatZero_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_ofNatZero_663_ = lean_ctor_get(v_a_659_, 18);
lean_inc_ref(v_ofNatZero_663_);
lean_dec(v_a_659_);
v___x_664_ = l_Lean_mkAppB(v_a_655_, v_a_657_, v_ofNatZero_663_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_664_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_657_);
lean_dec(v_a_655_);
v_a_669_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_658_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_658_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_dec(v_a_655_);
return v___x_656_;
}
}
else
{
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_p_677_, lean_object* v_strict_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_strict_boxed_691_; lean_object* v_res_692_; 
v_strict_boxed_691_ = lean_unbox(v_strict_678_);
v_res_692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_677_, v_strict_boxed_691_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v___y_680_);
lean_dec(v___y_679_);
lean_dec(v_p_677_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_c_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_p_706_; uint8_t v_strict_707_; lean_object* v___x_708_; 
v_p_706_ = lean_ctor_get(v_c_693_, 0);
v_strict_707_ = lean_ctor_get_uint8(v_c_693_, sizeof(void*)*2);
v___x_708_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_706_, v_strict_707_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_c_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v_c_709_);
return v_res_722_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_723_; double v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_float_of_nat(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object* v_cls_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_ref_735_; lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_782_; 
v_ref_735_ = lean_ctor_get(v___y_732_, 5);
v___x_736_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_782_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_782_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_782_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v_traceState_742_; lean_object* v_env_743_; lean_object* v_nextMacroScope_744_; lean_object* v_ngen_745_; lean_object* v_auxDeclNGen_746_; lean_object* v_cache_747_; lean_object* v_messages_748_; lean_object* v_infoState_749_; lean_object* v_snapshotTasks_750_; lean_object* v_newDecls_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_781_; 
v___x_741_ = lean_st_ref_take(v___y_733_);
v_traceState_742_ = lean_ctor_get(v___x_741_, 4);
v_env_743_ = lean_ctor_get(v___x_741_, 0);
v_nextMacroScope_744_ = lean_ctor_get(v___x_741_, 1);
v_ngen_745_ = lean_ctor_get(v___x_741_, 2);
v_auxDeclNGen_746_ = lean_ctor_get(v___x_741_, 3);
v_cache_747_ = lean_ctor_get(v___x_741_, 5);
v_messages_748_ = lean_ctor_get(v___x_741_, 6);
v_infoState_749_ = lean_ctor_get(v___x_741_, 7);
v_snapshotTasks_750_ = lean_ctor_get(v___x_741_, 8);
v_newDecls_751_ = lean_ctor_get(v___x_741_, 9);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_781_ == 0)
{
v___x_753_ = v___x_741_;
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_newDecls_751_);
lean_inc(v_snapshotTasks_750_);
lean_inc(v_infoState_749_);
lean_inc(v_messages_748_);
lean_inc(v_cache_747_);
lean_inc(v_traceState_742_);
lean_inc(v_auxDeclNGen_746_);
lean_inc(v_ngen_745_);
lean_inc(v_nextMacroScope_744_);
lean_inc(v_env_743_);
lean_dec(v___x_741_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint64_t v_tid_755_; lean_object* v_traces_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_780_; 
v_tid_755_ = lean_ctor_get_uint64(v_traceState_742_, sizeof(void*)*1);
v_traces_756_ = lean_ctor_get(v_traceState_742_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_traceState_742_);
if (v_isSharedCheck_780_ == 0)
{
v___x_758_ = v_traceState_742_;
v_isShared_759_ = v_isSharedCheck_780_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_traces_756_);
lean_dec(v_traceState_742_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_780_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; double v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0);
v___x_762_ = 0;
v___x_763_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1));
v___x_764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_764_, 0, v_cls_728_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3, v___x_761_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3 + 8, v___x_761_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*3 + 16, v___x_762_);
v___x_765_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2));
v___x_766_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v_a_737_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_inc(v_ref_735_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_735_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_PersistentArray_push___redArg(v_traces_756_, v___x_767_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_768_);
v___x_770_ = v___x_758_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_768_);
lean_ctor_set_uint64(v_reuseFailAlloc_779_, sizeof(void*)*1, v_tid_755_);
v___x_770_ = v_reuseFailAlloc_779_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v___x_770_);
v___x_772_ = v___x_753_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_env_743_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_nextMacroScope_744_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_ngen_745_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_auxDeclNGen_746_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_778_, 5, v_cache_747_);
lean_ctor_set(v_reuseFailAlloc_778_, 6, v_messages_748_);
lean_ctor_set(v_reuseFailAlloc_778_, 7, v_infoState_749_);
lean_ctor_set(v_reuseFailAlloc_778_, 8, v_snapshotTasks_750_);
lean_ctor_set(v_reuseFailAlloc_778_, 9, v_newDecls_751_);
v___x_772_ = v_reuseFailAlloc_778_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_st_ref_set(v___y_733_, v___x_772_);
v___x_774_ = lean_box(0);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_774_);
v___x_776_ = v___x_739_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(lean_object* v_cls_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_783_, v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_nat_to_int(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_805_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_806_ = l_Lean_Name_append(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_814_ = l_Lean_Name_append(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_822_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_823_ = l_Lean_Name_append(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16(void){
_start:
{
lean_object* v_cls_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_cls_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_830_ = l_Lean_Name_append(v___x_829_, v_cls_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* v_c_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v_options_921_; lean_object* v_inheritedTraceOptions_922_; uint8_t v_hasTrace_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; 
v_options_921_ = lean_ctor_get(v_a_841_, 2);
v_inheritedTraceOptions_922_ = lean_ctor_get(v_a_841_, 13);
v_hasTrace_923_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_923_ == 0)
{
v___y_925_ = v_a_832_;
v___y_926_ = v_a_833_;
v___y_927_ = v_a_834_;
v___y_928_ = v_a_835_;
v___y_929_ = v_a_836_;
v___y_930_ = v_a_837_;
v___y_931_ = v_a_838_;
v___y_932_ = v_a_839_;
v___y_933_ = v_a_840_;
v___y_934_ = v_a_841_;
v___y_935_ = v_a_842_;
goto v___jp_924_;
}
else
{
lean_object* v_cls_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_cls_996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_997_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_998_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_922_, v_options_921_, v___x_997_);
if (v___x_998_ == 0)
{
v___y_925_ = v_a_832_;
v___y_926_ = v_a_833_;
v___y_927_ = v_a_834_;
v___y_928_ = v_a_835_;
v___y_929_ = v_a_836_;
v___y_930_ = v_a_837_;
v___y_931_ = v_a_838_;
v___y_932_ = v_a_839_;
v___y_933_ = v_a_840_;
v___y_934_ = v_a_841_;
v___y_935_ = v_a_842_;
goto v___jp_924_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = l_Lean_MessageData_ofExpr(v_a_1000_);
v___x_1002_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_996_, v___x_1001_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_dec_ref(v___x_1002_);
v___y_925_ = v_a_832_;
v___y_926_ = v_a_833_;
v___y_927_ = v_a_834_;
v___y_928_ = v_a_835_;
v___y_929_ = v_a_836_;
v___y_930_ = v_a_837_;
v___y_931_ = v_a_838_;
v___y_932_ = v_a_839_;
v___y_933_ = v_a_840_;
v___y_934_ = v_a_841_;
v___y_935_ = v_a_842_;
goto v___jp_924_;
}
else
{
lean_dec_ref(v_c_831_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_c_831_);
v_a_1003_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_999_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_999_);
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
}
v___jp_844_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
v___jp_847_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_c_831_);
v___x_860_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_859_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v___x_860_;
}
v___jp_861_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_831_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_887_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_887_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; uint8_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = 0;
v___x_880_ = lean_unbox(v_a_875_);
lean_dec(v_a_875_);
v___x_881_ = l_Lean_instBEqLBool_beq(v___x_880_, v___x_879_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v___y_862_);
v___x_882_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_882_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_886_; 
lean_del_object(v___x_877_);
v___x_886_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_862_, v___y_863_, v___y_864_);
return v___x_886_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v___y_862_);
v_a_888_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_874_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_874_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; uint8_t v___x_914_; 
lean_dec_ref(v___x_912_);
v___x_913_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_914_ = lean_int_dec_lt(v___y_900_, v___x_913_);
lean_dec(v___y_900_);
if (v___x_914_ == 0)
{
lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc_ref(v_c_831_);
lean_inc(v___y_901_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_915_, 0, v___y_901_);
lean_closure_set(v___f_915_, 1, v_c_831_);
lean_closure_set(v___f_915_, 2, v___y_897_);
v___x_916_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_917_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_916_, v___f_915_, v___y_902_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref(v___x_917_);
v___y_862_ = v___y_898_;
v___y_863_ = v___y_901_;
v___y_864_ = v___y_902_;
v___y_865_ = v___y_903_;
v___y_866_ = v___y_904_;
v___y_867_ = v___y_905_;
v___y_868_ = v___y_906_;
v___y_869_ = v___y_907_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_909_;
v___y_872_ = v___y_910_;
v___y_873_ = v___y_911_;
goto v___jp_861_;
}
else
{
lean_dec(v___y_898_);
lean_dec_ref(v_c_831_);
return v___x_917_;
}
}
else
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc_ref(v_c_831_);
lean_inc(v___y_901_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(v___f_918_, 0, v___y_901_);
lean_closure_set(v___f_918_, 1, v_c_831_);
lean_closure_set(v___f_918_, 2, v___y_897_);
v___x_919_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_920_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_919_, v___f_918_, v___y_902_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref(v___x_920_);
v___y_862_ = v___y_898_;
v___y_863_ = v___y_901_;
v___y_864_ = v___y_902_;
v___y_865_ = v___y_903_;
v___y_866_ = v___y_904_;
v___y_867_ = v___y_905_;
v___y_868_ = v___y_906_;
v___y_869_ = v___y_907_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_909_;
v___y_872_ = v___y_910_;
v___y_873_ = v___y_911_;
goto v___jp_861_;
}
else
{
lean_dec(v___y_898_);
lean_dec_ref(v_c_831_);
return v___x_920_;
}
}
}
else
{
lean_dec(v___y_900_);
lean_dec(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v_c_831_);
return v___x_912_;
}
}
v___jp_924_:
{
lean_object* v_p_936_; 
v_p_936_ = lean_ctor_get(v_c_831_, 0);
if (lean_obj_tag(v_p_936_) == 0)
{
uint8_t v_strict_937_; 
v_strict_937_ = lean_ctor_get_uint8(v_c_831_, sizeof(void*)*2);
if (v_strict_937_ == 0)
{
lean_object* v_options_938_; uint8_t v_hasTrace_939_; 
v_options_938_ = lean_ctor_get(v___y_934_, 2);
v_hasTrace_939_ = lean_ctor_get_uint8(v_options_938_, sizeof(void*)*1);
if (v_hasTrace_939_ == 0)
{
lean_dec_ref(v_c_831_);
goto v___jp_844_;
}
else
{
lean_object* v_inheritedTraceOptions_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_inheritedTraceOptions_940_ = lean_ctor_get(v___y_934_, 13);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_942_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_943_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_940_, v_options_938_, v___x_942_);
if (v___x_943_ == 0)
{
lean_dec_ref(v_c_831_);
goto v___jp_844_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec_ref(v_c_831_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v___x_944_);
v___x_946_ = l_Lean_MessageData_ofExpr(v_a_945_);
v___x_947_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_941_, v___x_946_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_947_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_944_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_944_);
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
}
}
else
{
lean_object* v_options_956_; uint8_t v_hasTrace_957_; 
v_options_956_ = lean_ctor_get(v___y_934_, 2);
v_hasTrace_957_ = lean_ctor_get_uint8(v_options_956_, sizeof(void*)*1);
if (v_hasTrace_957_ == 0)
{
v___y_848_ = v___y_925_;
v___y_849_ = v___y_926_;
v___y_850_ = v___y_927_;
v___y_851_ = v___y_928_;
v___y_852_ = v___y_929_;
v___y_853_ = v___y_930_;
v___y_854_ = v___y_931_;
v___y_855_ = v___y_932_;
v___y_856_ = v___y_933_;
v___y_857_ = v___y_934_;
v___y_858_ = v___y_935_;
goto v___jp_847_;
}
else
{
lean_object* v_inheritedTraceOptions_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_inheritedTraceOptions_958_ = lean_ctor_get(v___y_934_, 13);
v___x_959_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_960_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_961_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_958_, v_options_956_, v___x_960_);
if (v___x_961_ == 0)
{
v___y_848_ = v___y_925_;
v___y_849_ = v___y_926_;
v___y_850_ = v___y_927_;
v___y_851_ = v___y_928_;
v___y_852_ = v___y_929_;
v___y_853_ = v___y_930_;
v___y_854_ = v___y_931_;
v___y_855_ = v___y_932_;
v___y_856_ = v___y_933_;
v___y_857_ = v___y_934_;
v___y_858_ = v___y_935_;
goto v___jp_847_;
}
else
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = l_Lean_MessageData_ofExpr(v_a_963_);
v___x_965_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_959_, v___x_964_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref(v___x_965_);
v___y_848_ = v___y_925_;
v___y_849_ = v___y_926_;
v___y_850_ = v___y_927_;
v___y_851_ = v___y_928_;
v___y_852_ = v___y_929_;
v___y_853_ = v___y_930_;
v___y_854_ = v___y_931_;
v___y_855_ = v___y_932_;
v___y_856_ = v___y_933_;
v___y_857_ = v___y_934_;
v___y_858_ = v___y_935_;
goto v___jp_847_;
}
else
{
lean_dec_ref(v_c_831_);
return v___x_965_;
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec_ref(v_c_831_);
v_a_966_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_962_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_974_; uint8_t v_hasTrace_975_; 
v_options_974_ = lean_ctor_get(v___y_934_, 2);
v_hasTrace_975_ = lean_ctor_get_uint8(v_options_974_, sizeof(void*)*1);
if (v_hasTrace_975_ == 0)
{
lean_object* v_k_976_; lean_object* v_v_977_; 
v_k_976_ = lean_ctor_get(v_p_936_, 0);
v_v_977_ = lean_ctor_get(v_p_936_, 1);
lean_inc(v_k_976_);
lean_inc_ref(v_p_936_);
lean_inc_n(v_v_977_, 2);
v___y_897_ = v_v_977_;
v___y_898_ = v_v_977_;
v___y_899_ = v_p_936_;
v___y_900_ = v_k_976_;
v___y_901_ = v___y_925_;
v___y_902_ = v___y_926_;
v___y_903_ = v___y_927_;
v___y_904_ = v___y_928_;
v___y_905_ = v___y_929_;
v___y_906_ = v___y_930_;
v___y_907_ = v___y_931_;
v___y_908_ = v___y_932_;
v___y_909_ = v___y_933_;
v___y_910_ = v___y_934_;
v___y_911_ = v___y_935_;
goto v___jp_896_;
}
else
{
lean_object* v_k_978_; lean_object* v_v_979_; lean_object* v_inheritedTraceOptions_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_k_978_ = lean_ctor_get(v_p_936_, 0);
v_v_979_ = lean_ctor_get(v_p_936_, 1);
v_inheritedTraceOptions_980_ = lean_ctor_get(v___y_934_, 13);
v___x_981_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_982_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_980_, v_options_974_, v___x_982_);
if (v___x_983_ == 0)
{
lean_inc(v_k_978_);
lean_inc_ref(v_p_936_);
lean_inc_n(v_v_979_, 2);
v___y_897_ = v_v_979_;
v___y_898_ = v_v_979_;
v___y_899_ = v_p_936_;
v___y_900_ = v_k_978_;
v___y_901_ = v___y_925_;
v___y_902_ = v___y_926_;
v___y_903_ = v___y_927_;
v___y_904_ = v___y_928_;
v___y_905_ = v___y_929_;
v___y_906_ = v___y_930_;
v___y_907_ = v___y_931_;
v___y_908_ = v___y_932_;
v___y_909_ = v___y_933_;
v___y_910_ = v___y_934_;
v___y_911_ = v___y_935_;
goto v___jp_896_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = l_Lean_MessageData_ofExpr(v_a_985_);
v___x_987_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_981_, v___x_986_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref(v___x_987_);
lean_inc(v_k_978_);
lean_inc_ref(v_p_936_);
lean_inc_n(v_v_979_, 2);
v___y_897_ = v_v_979_;
v___y_898_ = v_v_979_;
v___y_899_ = v_p_936_;
v___y_900_ = v_k_978_;
v___y_901_ = v___y_925_;
v___y_902_ = v___y_926_;
v___y_903_ = v___y_927_;
v___y_904_ = v___y_928_;
v___y_905_ = v___y_929_;
v___y_906_ = v___y_930_;
v___y_907_ = v___y_931_;
v___y_908_ = v___y_932_;
v___y_909_ = v___y_933_;
v___y_910_ = v___y_934_;
v___y_911_ = v___y_935_;
goto v___jp_896_;
}
else
{
lean_dec_ref(v_c_831_);
return v___x_987_;
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_c_831_);
v_a_988_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_984_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_984_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec(v_a_1012_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1025_, v_msg_1026_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1040_, v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1056_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1070_, v_msg_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1085_, lean_object* v_e_1086_, lean_object* v_s_1087_){
_start:
{
lean_object* v_structs_1088_; lean_object* v_typeIdOf_1089_; lean_object* v_exprToStructId_1090_; lean_object* v_exprToStructIdEntries_1091_; lean_object* v_forbiddenNatModules_1092_; lean_object* v_natStructs_1093_; lean_object* v_natTypeIdOf_1094_; lean_object* v_exprToNatStructId_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_structs_1088_ = lean_ctor_get(v_s_1087_, 0);
v_typeIdOf_1089_ = lean_ctor_get(v_s_1087_, 1);
v_exprToStructId_1090_ = lean_ctor_get(v_s_1087_, 2);
v_exprToStructIdEntries_1091_ = lean_ctor_get(v_s_1087_, 3);
v_forbiddenNatModules_1092_ = lean_ctor_get(v_s_1087_, 4);
v_natStructs_1093_ = lean_ctor_get(v_s_1087_, 5);
v_natTypeIdOf_1094_ = lean_ctor_get(v_s_1087_, 6);
v_exprToNatStructId_1095_ = lean_ctor_get(v_s_1087_, 7);
v___x_1096_ = lean_array_get_size(v_structs_1088_);
v___x_1097_ = lean_nat_dec_lt(v_a_1085_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v_e_1086_);
return v_s_1087_;
}
else
{
lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1159_; 
lean_inc_ref(v_exprToNatStructId_1095_);
lean_inc_ref(v_natTypeIdOf_1094_);
lean_inc_ref(v_natStructs_1093_);
lean_inc_ref(v_forbiddenNatModules_1092_);
lean_inc_ref(v_exprToStructIdEntries_1091_);
lean_inc_ref(v_exprToStructId_1090_);
lean_inc_ref(v_typeIdOf_1089_);
lean_inc_ref(v_structs_1088_);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_s_1087_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1160_ = lean_ctor_get(v_s_1087_, 7);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_s_1087_, 6);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_s_1087_, 5);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_s_1087_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_s_1087_, 3);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_s_1087_, 2);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_s_1087_, 1);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_s_1087_, 0);
lean_dec(v_unused_1167_);
v___x_1099_ = v_s_1087_;
v_isShared_1100_ = v_isSharedCheck_1159_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v_s_1087_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1159_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_v_1101_; lean_object* v_id_1102_; lean_object* v_ringId_x3f_1103_; lean_object* v_type_1104_; lean_object* v_u_1105_; lean_object* v_intModuleInst_1106_; lean_object* v_leInst_x3f_1107_; lean_object* v_ltInst_x3f_1108_; lean_object* v_lawfulOrderLTInst_x3f_1109_; lean_object* v_isPreorderInst_x3f_1110_; lean_object* v_orderedAddInst_x3f_1111_; lean_object* v_isLinearInst_x3f_1112_; lean_object* v_noNatDivInst_x3f_1113_; lean_object* v_ringInst_x3f_1114_; lean_object* v_commRingInst_x3f_1115_; lean_object* v_orderedRingInst_x3f_1116_; lean_object* v_fieldInst_x3f_1117_; lean_object* v_charInst_x3f_1118_; lean_object* v_zero_1119_; lean_object* v_ofNatZero_1120_; lean_object* v_one_x3f_1121_; lean_object* v_leFn_x3f_1122_; lean_object* v_ltFn_x3f_1123_; lean_object* v_addFn_1124_; lean_object* v_zsmulFn_1125_; lean_object* v_nsmulFn_1126_; lean_object* v_zsmulFn_x3f_1127_; lean_object* v_nsmulFn_x3f_1128_; lean_object* v_homomulFn_x3f_1129_; lean_object* v_subFn_1130_; lean_object* v_negFn_1131_; lean_object* v_vars_1132_; lean_object* v_varMap_1133_; lean_object* v_lowers_1134_; lean_object* v_uppers_1135_; lean_object* v_diseqs_1136_; lean_object* v_assignment_1137_; uint8_t v_caseSplits_1138_; lean_object* v_conflict_x3f_1139_; lean_object* v_diseqSplits_1140_; lean_object* v_elimEqs_1141_; lean_object* v_elimStack_1142_; lean_object* v_occurs_1143_; lean_object* v_ignored_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1158_; 
v_v_1101_ = lean_array_fget(v_structs_1088_, v_a_1085_);
v_id_1102_ = lean_ctor_get(v_v_1101_, 0);
v_ringId_x3f_1103_ = lean_ctor_get(v_v_1101_, 1);
v_type_1104_ = lean_ctor_get(v_v_1101_, 2);
v_u_1105_ = lean_ctor_get(v_v_1101_, 3);
v_intModuleInst_1106_ = lean_ctor_get(v_v_1101_, 4);
v_leInst_x3f_1107_ = lean_ctor_get(v_v_1101_, 5);
v_ltInst_x3f_1108_ = lean_ctor_get(v_v_1101_, 6);
v_lawfulOrderLTInst_x3f_1109_ = lean_ctor_get(v_v_1101_, 7);
v_isPreorderInst_x3f_1110_ = lean_ctor_get(v_v_1101_, 8);
v_orderedAddInst_x3f_1111_ = lean_ctor_get(v_v_1101_, 9);
v_isLinearInst_x3f_1112_ = lean_ctor_get(v_v_1101_, 10);
v_noNatDivInst_x3f_1113_ = lean_ctor_get(v_v_1101_, 11);
v_ringInst_x3f_1114_ = lean_ctor_get(v_v_1101_, 12);
v_commRingInst_x3f_1115_ = lean_ctor_get(v_v_1101_, 13);
v_orderedRingInst_x3f_1116_ = lean_ctor_get(v_v_1101_, 14);
v_fieldInst_x3f_1117_ = lean_ctor_get(v_v_1101_, 15);
v_charInst_x3f_1118_ = lean_ctor_get(v_v_1101_, 16);
v_zero_1119_ = lean_ctor_get(v_v_1101_, 17);
v_ofNatZero_1120_ = lean_ctor_get(v_v_1101_, 18);
v_one_x3f_1121_ = lean_ctor_get(v_v_1101_, 19);
v_leFn_x3f_1122_ = lean_ctor_get(v_v_1101_, 20);
v_ltFn_x3f_1123_ = lean_ctor_get(v_v_1101_, 21);
v_addFn_1124_ = lean_ctor_get(v_v_1101_, 22);
v_zsmulFn_1125_ = lean_ctor_get(v_v_1101_, 23);
v_nsmulFn_1126_ = lean_ctor_get(v_v_1101_, 24);
v_zsmulFn_x3f_1127_ = lean_ctor_get(v_v_1101_, 25);
v_nsmulFn_x3f_1128_ = lean_ctor_get(v_v_1101_, 26);
v_homomulFn_x3f_1129_ = lean_ctor_get(v_v_1101_, 27);
v_subFn_1130_ = lean_ctor_get(v_v_1101_, 28);
v_negFn_1131_ = lean_ctor_get(v_v_1101_, 29);
v_vars_1132_ = lean_ctor_get(v_v_1101_, 30);
v_varMap_1133_ = lean_ctor_get(v_v_1101_, 31);
v_lowers_1134_ = lean_ctor_get(v_v_1101_, 32);
v_uppers_1135_ = lean_ctor_get(v_v_1101_, 33);
v_diseqs_1136_ = lean_ctor_get(v_v_1101_, 34);
v_assignment_1137_ = lean_ctor_get(v_v_1101_, 35);
v_caseSplits_1138_ = lean_ctor_get_uint8(v_v_1101_, sizeof(void*)*42);
v_conflict_x3f_1139_ = lean_ctor_get(v_v_1101_, 36);
v_diseqSplits_1140_ = lean_ctor_get(v_v_1101_, 37);
v_elimEqs_1141_ = lean_ctor_get(v_v_1101_, 38);
v_elimStack_1142_ = lean_ctor_get(v_v_1101_, 39);
v_occurs_1143_ = lean_ctor_get(v_v_1101_, 40);
v_ignored_1144_ = lean_ctor_get(v_v_1101_, 41);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_v_1101_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1146_ = v_v_1101_;
v_isShared_1147_ = v_isSharedCheck_1158_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_ignored_1144_);
lean_inc(v_occurs_1143_);
lean_inc(v_elimStack_1142_);
lean_inc(v_elimEqs_1141_);
lean_inc(v_diseqSplits_1140_);
lean_inc(v_conflict_x3f_1139_);
lean_inc(v_assignment_1137_);
lean_inc(v_diseqs_1136_);
lean_inc(v_uppers_1135_);
lean_inc(v_lowers_1134_);
lean_inc(v_varMap_1133_);
lean_inc(v_vars_1132_);
lean_inc(v_negFn_1131_);
lean_inc(v_subFn_1130_);
lean_inc(v_homomulFn_x3f_1129_);
lean_inc(v_nsmulFn_x3f_1128_);
lean_inc(v_zsmulFn_x3f_1127_);
lean_inc(v_nsmulFn_1126_);
lean_inc(v_zsmulFn_1125_);
lean_inc(v_addFn_1124_);
lean_inc(v_ltFn_x3f_1123_);
lean_inc(v_leFn_x3f_1122_);
lean_inc(v_one_x3f_1121_);
lean_inc(v_ofNatZero_1120_);
lean_inc(v_zero_1119_);
lean_inc(v_charInst_x3f_1118_);
lean_inc(v_fieldInst_x3f_1117_);
lean_inc(v_orderedRingInst_x3f_1116_);
lean_inc(v_commRingInst_x3f_1115_);
lean_inc(v_ringInst_x3f_1114_);
lean_inc(v_noNatDivInst_x3f_1113_);
lean_inc(v_isLinearInst_x3f_1112_);
lean_inc(v_orderedAddInst_x3f_1111_);
lean_inc(v_isPreorderInst_x3f_1110_);
lean_inc(v_lawfulOrderLTInst_x3f_1109_);
lean_inc(v_ltInst_x3f_1108_);
lean_inc(v_leInst_x3f_1107_);
lean_inc(v_intModuleInst_1106_);
lean_inc(v_u_1105_);
lean_inc(v_type_1104_);
lean_inc(v_ringId_x3f_1103_);
lean_inc(v_id_1102_);
lean_dec(v_v_1101_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1158_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v_xs_x27_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1148_ = lean_box(0);
v_xs_x27_1149_ = lean_array_fset(v_structs_1088_, v_a_1085_, v___x_1148_);
v___x_1150_ = l_Lean_PersistentArray_push___redArg(v_ignored_1144_, v_e_1086_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 41, v___x_1150_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_id_1102_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_ringId_x3f_1103_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_type_1104_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_u_1105_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_intModuleInst_1106_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_leInst_x3f_1107_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_ltInst_x3f_1108_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_lawfulOrderLTInst_x3f_1109_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_isPreorderInst_x3f_1110_);
lean_ctor_set(v_reuseFailAlloc_1157_, 9, v_orderedAddInst_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1157_, 10, v_isLinearInst_x3f_1112_);
lean_ctor_set(v_reuseFailAlloc_1157_, 11, v_noNatDivInst_x3f_1113_);
lean_ctor_set(v_reuseFailAlloc_1157_, 12, v_ringInst_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1157_, 13, v_commRingInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1157_, 14, v_orderedRingInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1157_, 15, v_fieldInst_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1157_, 16, v_charInst_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1157_, 17, v_zero_1119_);
lean_ctor_set(v_reuseFailAlloc_1157_, 18, v_ofNatZero_1120_);
lean_ctor_set(v_reuseFailAlloc_1157_, 19, v_one_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1157_, 20, v_leFn_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1157_, 21, v_ltFn_x3f_1123_);
lean_ctor_set(v_reuseFailAlloc_1157_, 22, v_addFn_1124_);
lean_ctor_set(v_reuseFailAlloc_1157_, 23, v_zsmulFn_1125_);
lean_ctor_set(v_reuseFailAlloc_1157_, 24, v_nsmulFn_1126_);
lean_ctor_set(v_reuseFailAlloc_1157_, 25, v_zsmulFn_x3f_1127_);
lean_ctor_set(v_reuseFailAlloc_1157_, 26, v_nsmulFn_x3f_1128_);
lean_ctor_set(v_reuseFailAlloc_1157_, 27, v_homomulFn_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1157_, 28, v_subFn_1130_);
lean_ctor_set(v_reuseFailAlloc_1157_, 29, v_negFn_1131_);
lean_ctor_set(v_reuseFailAlloc_1157_, 30, v_vars_1132_);
lean_ctor_set(v_reuseFailAlloc_1157_, 31, v_varMap_1133_);
lean_ctor_set(v_reuseFailAlloc_1157_, 32, v_lowers_1134_);
lean_ctor_set(v_reuseFailAlloc_1157_, 33, v_uppers_1135_);
lean_ctor_set(v_reuseFailAlloc_1157_, 34, v_diseqs_1136_);
lean_ctor_set(v_reuseFailAlloc_1157_, 35, v_assignment_1137_);
lean_ctor_set(v_reuseFailAlloc_1157_, 36, v_conflict_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1157_, 37, v_diseqSplits_1140_);
lean_ctor_set(v_reuseFailAlloc_1157_, 38, v_elimEqs_1141_);
lean_ctor_set(v_reuseFailAlloc_1157_, 39, v_elimStack_1142_);
lean_ctor_set(v_reuseFailAlloc_1157_, 40, v_occurs_1143_);
lean_ctor_set(v_reuseFailAlloc_1157_, 41, v___x_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*42, v_caseSplits_1138_);
v___x_1152_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_array_fset(v_xs_x27_1149_, v_a_1085_, v___x_1152_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1153_);
v___x_1155_ = v___x_1099_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_typeIdOf_1089_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_exprToStructId_1090_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_exprToStructIdEntries_1091_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_forbiddenNatModules_1092_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_natStructs_1093_);
lean_ctor_set(v_reuseFailAlloc_1156_, 6, v_natTypeIdOf_1094_);
lean_ctor_set(v_reuseFailAlloc_1156_, 7, v_exprToNatStructId_1095_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1168_, lean_object* v_e_1169_, lean_object* v_s_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1168_, v_e_1169_, v_s_1170_);
lean_dec(v_a_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1172_, lean_object* v_lhs_1173_, lean_object* v_rhs_1174_, uint8_t v_strict_1175_, uint8_t v_eqTrue_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1189_ = 0;
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_box(v___x_1189_);
v___x_1192_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1192_, 0, v_lhs_1173_);
lean_closure_set(v___x_1192_, 1, v___x_1191_);
lean_closure_set(v___x_1192_, 2, v___x_1190_);
v___x_1193_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1192_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1348_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1348_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1348_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
if (lean_obj_tag(v_a_1194_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1196_);
v_val_1198_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v_a_1194_);
v___x_1199_ = lean_box(v___x_1189_);
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1200_, 0, v_rhs_1174_);
lean_closure_set(v___x_1200_, 1, v___x_1199_);
lean_closure_set(v___x_1200_, 2, v___x_1190_);
v___x_1201_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1200_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1335_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1335_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1335_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
if (lean_obj_tag(v_a_1202_) == 1)
{
lean_object* v_val_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1204_);
v_val_1206_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v_a_1202_);
v___x_1207_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1172_, v_a_1178_);
if (lean_obj_tag(v___x_1207_) == 0)
{
if (v_eqTrue_1176_ == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; uint8_t v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_unbox(v_a_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v_a_1210_);
lean_dec(v_a_1208_);
lean_dec(v_val_1206_);
lean_dec(v_val_1198_);
lean_inc(v_a_1177_);
v___f_1212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1212_, 0, v_a_1177_);
lean_closure_set(v___f_1212_, 1, v_e_1172_);
v___x_1213_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1214_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1213_, v___f_1212_, v_a_1178_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___y_1218_; 
lean_inc(v_val_1198_);
lean_inc(v_val_1206_);
v___x_1215_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_val_1206_);
lean_ctor_set(v___x_1215_, 1, v_val_1198_);
v___x_1216_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1215_);
if (v_strict_1175_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_unbox(v_a_1210_);
lean_dec(v_a_1210_);
v___y_1218_ = v___x_1265_;
goto v___jp_1217_;
}
else
{
lean_dec(v_a_1210_);
v___y_1218_ = v_eqTrue_1176_;
goto v___jp_1217_;
}
v___jp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1219_, 0, v_e_1172_);
lean_ctor_set(v___x_1219_, 1, v_val_1198_);
lean_ctor_set(v___x_1219_, 2, v_val_1206_);
v___x_1220_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*2, v___y_1218_);
v___x_1221_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1220_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v_p_1223_; lean_object* v___x_1224_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___x_1221_);
v_p_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_a_1208_);
lean_inc_ref(v_p_1223_);
v___x_1224_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1223_, v_a_1208_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1225_, v___x_1189_, v_a_1208_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1240_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1240_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1240_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
if (lean_obj_tag(v_a_1227_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1229_);
v_val_1231_ = lean_ctor_get(v_a_1227_, 0);
lean_inc_n(v_val_1231_, 2);
lean_dec_ref(v_a_1227_);
v___x_1232_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1231_);
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_a_1222_);
lean_ctor_set(v___x_1233_, 1, v_val_1231_);
v___x_1234_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2, v___y_1218_);
v___x_1235_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1234_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v_a_1227_);
lean_dec(v_a_1222_);
v___x_1236_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1236_);
v___x_1238_ = v___x_1229_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_a_1222_);
v_a_1241_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1226_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1226_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1222_);
lean_dec(v_a_1208_);
v_a_1249_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1224_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1224_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1208_);
v_a_1257_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1221_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1221_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1208_);
lean_dec(v_val_1206_);
lean_dec(v_val_1198_);
lean_dec_ref(v_e_1172_);
v_a_1266_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1209_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1209_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1274_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1207_);
lean_inc(v_val_1206_);
lean_inc(v_val_1198_);
v___x_1275_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_val_1198_);
lean_ctor_set(v___x_1275_, 1, v_val_1206_);
v___x_1276_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_e_1172_);
lean_ctor_set(v___x_1277_, 1, v_val_1198_);
lean_ctor_set(v___x_1277_, 2, v_val_1206_);
v___x_1278_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*2, v_strict_1175_);
v___x_1279_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1278_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_p_1281_; lean_object* v___x_1282_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v_p_1281_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_a_1274_);
lean_inc_ref(v_p_1281_);
v___x_1282_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1281_, v_a_1274_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1283_, v___x_1189_, v_a_1274_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1298_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
if (lean_obj_tag(v_a_1285_) == 1)
{
lean_object* v_val_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_del_object(v___x_1287_);
v_val_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc_n(v_val_1289_, 2);
lean_dec_ref(v_a_1285_);
v___x_1290_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1289_);
v___x_1291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1280_);
lean_ctor_set(v___x_1291_, 1, v_val_1289_);
v___x_1292_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*2, v_strict_1175_);
v___x_1293_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1292_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_dec(v_a_1285_);
lean_dec(v_a_1280_);
v___x_1294_ = lean_box(0);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1294_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_a_1280_);
v_a_1299_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1284_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1284_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_a_1280_);
lean_dec(v_a_1274_);
v_a_1307_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1282_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1282_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_a_1274_);
v_a_1315_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1279_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1279_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_val_1206_);
lean_dec(v_val_1198_);
lean_dec_ref(v_e_1172_);
v_a_1323_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1207_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1207_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec(v_a_1202_);
lean_dec(v_val_1198_);
lean_dec_ref(v_e_1172_);
v___x_1331_ = lean_box(0);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1331_);
v___x_1333_ = v___x_1204_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_val_1198_);
lean_dec_ref(v_e_1172_);
v_a_1336_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1201_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1201_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_dec(v_a_1194_);
lean_dec_ref(v_rhs_1174_);
lean_dec_ref(v_e_1172_);
v___x_1344_ = lean_box(0);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1344_);
v___x_1346_ = v___x_1196_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_rhs_1174_);
lean_dec_ref(v_e_1172_);
v_a_1349_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1193_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1193_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1357_ = _args[0];
lean_object* v_lhs_1358_ = _args[1];
lean_object* v_rhs_1359_ = _args[2];
lean_object* v_strict_1360_ = _args[3];
lean_object* v_eqTrue_1361_ = _args[4];
lean_object* v_a_1362_ = _args[5];
lean_object* v_a_1363_ = _args[6];
lean_object* v_a_1364_ = _args[7];
lean_object* v_a_1365_ = _args[8];
lean_object* v_a_1366_ = _args[9];
lean_object* v_a_1367_ = _args[10];
lean_object* v_a_1368_ = _args[11];
lean_object* v_a_1369_ = _args[12];
lean_object* v_a_1370_ = _args[13];
lean_object* v_a_1371_ = _args[14];
lean_object* v_a_1372_ = _args[15];
lean_object* v_a_1373_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1374_; uint8_t v_eqTrue_boxed_1375_; lean_object* v_res_1376_; 
v_strict_boxed_1374_ = lean_unbox(v_strict_1360_);
v_eqTrue_boxed_1375_ = lean_unbox(v_eqTrue_1361_);
v_res_1376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1357_, v_lhs_1358_, v_rhs_1359_, v_strict_boxed_1374_, v_eqTrue_boxed_1375_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec(v_a_1362_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1377_, lean_object* v_lhs_1378_, lean_object* v_rhs_1379_, uint8_t v_strict_1380_, uint8_t v_eqTrue_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1378_, v_a_1383_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = 0;
v___x_1397_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1378_, v___x_1396_, v_a_1395_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1464_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1464_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1464_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1400_);
v_val_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1402_);
lean_dec_ref(v_a_1398_);
v___x_1403_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1379_, v_a_1383_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1379_, v___x_1396_, v_a_1404_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1443_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1443_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1443_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
if (lean_obj_tag(v_a_1406_) == 1)
{
lean_del_object(v___x_1408_);
if (v_eqTrue_1381_ == 0)
{
lean_object* v_val_1410_; lean_object* v___x_1411_; 
v_val_1410_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v_a_1406_);
v___x_1411_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; uint8_t v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_unbox(v_a_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v_a_1412_);
lean_dec(v_val_1410_);
lean_dec(v_val_1402_);
lean_inc(v_a_1382_);
v___f_1414_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1414_, 0, v_a_1382_);
lean_closure_set(v___f_1414_, 1, v_e_1377_);
v___x_1415_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1416_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1415_, v___f_1414_, v_a_1383_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___y_1420_; 
lean_inc(v_val_1402_);
lean_inc(v_val_1410_);
v___x_1417_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_val_1410_);
lean_ctor_set(v___x_1417_, 1, v_val_1402_);
v___x_1418_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1417_);
if (v_strict_1380_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_unbox(v_a_1412_);
lean_dec(v_a_1412_);
v___y_1420_ = v___x_1424_;
goto v___jp_1419_;
}
else
{
lean_dec(v_a_1412_);
v___y_1420_ = v_eqTrue_1381_;
goto v___jp_1419_;
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_e_1377_);
lean_ctor_set(v___x_1421_, 1, v_val_1402_);
lean_ctor_set(v___x_1421_, 2, v_val_1410_);
v___x_1422_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1418_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*2, v___y_1420_);
v___x_1423_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1422_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1423_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_val_1410_);
lean_dec(v_val_1402_);
lean_dec_ref(v_e_1377_);
v_a_1425_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1411_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1411_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_val_1433_ = lean_ctor_get(v_a_1406_, 0);
lean_inc_n(v_val_1433_, 2);
lean_dec_ref(v_a_1406_);
lean_inc(v_val_1402_);
v___x_1434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_val_1402_);
lean_ctor_set(v___x_1434_, 1, v_val_1433_);
v___x_1435_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1436_, 0, v_e_1377_);
lean_ctor_set(v___x_1436_, 1, v_val_1402_);
lean_ctor_set(v___x_1436_, 2, v_val_1433_);
v___x_1437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*2, v_strict_1380_);
v___x_1438_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1437_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec(v_a_1406_);
lean_dec(v_val_1402_);
lean_dec_ref(v_e_1377_);
v___x_1439_ = lean_box(0);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1439_);
v___x_1441_ = v___x_1408_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_val_1402_);
lean_dec_ref(v_e_1377_);
v_a_1444_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1405_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1405_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_val_1402_);
lean_dec_ref(v_rhs_1379_);
lean_dec_ref(v_e_1377_);
v_a_1452_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1403_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1403_);
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
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec(v_a_1398_);
lean_dec_ref(v_rhs_1379_);
lean_dec_ref(v_e_1377_);
v___x_1460_ = lean_box(0);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1460_);
v___x_1462_ = v___x_1400_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
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
lean_dec_ref(v_rhs_1379_);
lean_dec_ref(v_e_1377_);
v_a_1465_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1397_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1397_);
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
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_rhs_1379_);
lean_dec_ref(v_lhs_1378_);
lean_dec_ref(v_e_1377_);
v_a_1473_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1394_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1394_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1481_ = _args[0];
lean_object* v_lhs_1482_ = _args[1];
lean_object* v_rhs_1483_ = _args[2];
lean_object* v_strict_1484_ = _args[3];
lean_object* v_eqTrue_1485_ = _args[4];
lean_object* v_a_1486_ = _args[5];
lean_object* v_a_1487_ = _args[6];
lean_object* v_a_1488_ = _args[7];
lean_object* v_a_1489_ = _args[8];
lean_object* v_a_1490_ = _args[9];
lean_object* v_a_1491_ = _args[10];
lean_object* v_a_1492_ = _args[11];
lean_object* v_a_1493_ = _args[12];
lean_object* v_a_1494_ = _args[13];
lean_object* v_a_1495_ = _args[14];
lean_object* v_a_1496_ = _args[15];
lean_object* v_a_1497_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1498_; uint8_t v_eqTrue_boxed_1499_; lean_object* v_res_1500_; 
v_strict_boxed_1498_ = lean_unbox(v_strict_1484_);
v_eqTrue_boxed_1499_ = lean_unbox(v_eqTrue_1485_);
v_res_1500_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1481_, v_lhs_1482_, v_rhs_1483_, v_strict_boxed_1498_, v_eqTrue_boxed_1499_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1501_, lean_object* v_lhs_1502_, lean_object* v_rhs_1503_, uint8_t v_strict_1504_, uint8_t v_eqTrue_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
lean_inc_ref(v_lhs_1502_);
v___x_1520_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1502_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_fst_1522_; lean_object* v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v_fst_1522_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_fst_1522_);
lean_dec(v_a_1521_);
lean_inc_ref(v_rhs_1503_);
v___x_1523_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1503_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_fst_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1608_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v_fst_1525_ = lean_ctor_get(v_a_1524_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_a_1524_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_a_1524_, 1);
lean_dec(v_unused_1609_);
v___x_1527_ = v_a_1524_;
v_isShared_1528_ = v_isSharedCheck_1608_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_fst_1525_);
lean_dec(v_a_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1608_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1502_, v_a_1507_);
lean_dec_ref(v_lhs_1502_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_id_1531_; lean_object* v_structId_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v_id_1531_ = lean_ctor_get(v_a_1519_, 0);
lean_inc(v_id_1531_);
v_structId_1532_ = lean_ctor_get(v_a_1519_, 1);
lean_inc(v_structId_1532_);
lean_dec(v_a_1519_);
v___x_1533_ = 0;
v___x_1534_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1522_, v___x_1533_, v_a_1530_, v_structId_1532_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1591_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1591_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1591_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
if (lean_obj_tag(v_a_1535_) == 1)
{
lean_object* v_val_1539_; lean_object* v___x_1540_; 
lean_del_object(v___x_1537_);
v_val_1539_ = lean_ctor_get(v_a_1535_, 0);
lean_inc(v_val_1539_);
lean_dec_ref(v_a_1535_);
v___x_1540_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1503_, v_a_1507_);
lean_dec_ref(v_rhs_1503_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1525_, v___x_1533_, v_a_1541_, v_structId_1532_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1570_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1570_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1570_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 1)
{
lean_del_object(v___x_1545_);
if (v_eqTrue_1505_ == 0)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc_n(v_val_1547_, 2);
lean_dec_ref(v_a_1543_);
lean_inc(v_val_1539_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 3);
lean_ctor_set(v___x_1527_, 1, v_val_1539_);
lean_ctor_set(v___x_1527_, 0, v_val_1547_);
v___x_1549_ = v___x_1527_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_val_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_val_1539_);
v___x_1549_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; uint8_t v___y_1552_; 
v___x_1550_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1549_);
if (v_strict_1504_ == 0)
{
uint8_t v___x_1556_; 
v___x_1556_ = 1;
v___y_1552_ = v___x_1556_;
goto v___jp_1551_;
}
else
{
v___y_1552_ = v_eqTrue_1505_;
goto v___jp_1551_;
}
v___jp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1553_, 0, v_e_1501_);
lean_ctor_set(v___x_1553_, 1, v_id_1531_);
lean_ctor_set(v___x_1553_, 2, v_val_1539_);
lean_ctor_set(v___x_1553_, 3, v_val_1547_);
v___x_1554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1550_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*2, v___y_1552_);
v___x_1555_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1554_, v_structId_1532_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_structId_1532_);
return v___x_1555_;
}
}
}
else
{
lean_object* v_val_1558_; lean_object* v___x_1560_; 
v_val_1558_ = lean_ctor_get(v_a_1543_, 0);
lean_inc_n(v_val_1558_, 2);
lean_dec_ref(v_a_1543_);
lean_inc(v_val_1539_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 3);
lean_ctor_set(v___x_1527_, 1, v_val_1558_);
lean_ctor_set(v___x_1527_, 0, v_val_1539_);
v___x_1560_ = v___x_1527_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_val_1539_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_val_1558_);
v___x_1560_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v_e_1501_);
lean_ctor_set(v___x_1562_, 1, v_id_1531_);
lean_ctor_set(v___x_1562_, 2, v_val_1539_);
lean_ctor_set(v___x_1562_, 3, v_val_1558_);
v___x_1563_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*2, v_strict_1504_);
v___x_1564_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1563_, v_structId_1532_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_structId_1532_);
return v___x_1564_;
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec(v_a_1543_);
lean_dec(v_val_1539_);
lean_dec(v_structId_1532_);
lean_dec(v_id_1531_);
lean_del_object(v___x_1527_);
lean_dec_ref(v_e_1501_);
v___x_1566_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1566_);
v___x_1568_ = v___x_1545_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
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
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_val_1539_);
lean_dec(v_structId_1532_);
lean_dec(v_id_1531_);
lean_del_object(v___x_1527_);
lean_dec_ref(v_e_1501_);
v_a_1571_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1542_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1542_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_val_1539_);
lean_dec(v_structId_1532_);
lean_dec(v_id_1531_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1525_);
lean_dec_ref(v_e_1501_);
v_a_1579_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1540_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1540_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_a_1535_);
lean_dec(v_structId_1532_);
lean_dec(v_id_1531_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1525_);
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_e_1501_);
v___x_1587_ = lean_box(0);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1587_);
v___x_1589_ = v___x_1537_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_structId_1532_);
lean_dec(v_id_1531_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1525_);
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_e_1501_);
v_a_1592_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1534_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1534_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1527_);
lean_dec(v_fst_1525_);
lean_dec(v_fst_1522_);
lean_dec(v_a_1519_);
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_e_1501_);
v_a_1600_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1529_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1529_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_fst_1522_);
lean_dec(v_a_1519_);
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_lhs_1502_);
lean_dec_ref(v_e_1501_);
v_a_1610_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1523_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1523_);
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
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_lhs_1502_);
lean_dec_ref(v_e_1501_);
v_a_1618_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1520_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1520_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_rhs_1503_);
lean_dec_ref(v_lhs_1502_);
lean_dec_ref(v_e_1501_);
v_a_1626_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1518_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1518_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1634_ = _args[0];
lean_object* v_lhs_1635_ = _args[1];
lean_object* v_rhs_1636_ = _args[2];
lean_object* v_strict_1637_ = _args[3];
lean_object* v_eqTrue_1638_ = _args[4];
lean_object* v_a_1639_ = _args[5];
lean_object* v_a_1640_ = _args[6];
lean_object* v_a_1641_ = _args[7];
lean_object* v_a_1642_ = _args[8];
lean_object* v_a_1643_ = _args[9];
lean_object* v_a_1644_ = _args[10];
lean_object* v_a_1645_ = _args[11];
lean_object* v_a_1646_ = _args[12];
lean_object* v_a_1647_ = _args[13];
lean_object* v_a_1648_ = _args[14];
lean_object* v_a_1649_ = _args[15];
lean_object* v_a_1650_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1651_; uint8_t v_eqTrue_boxed_1652_; lean_object* v_res_1653_; 
v_strict_boxed_1651_ = lean_unbox(v_strict_1637_);
v_eqTrue_boxed_1652_ = lean_unbox(v_eqTrue_1638_);
v_res_1653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1634_, v_lhs_1635_, v_rhs_1636_, v_strict_boxed_1651_, v_eqTrue_boxed_1652_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec(v_a_1639_);
return v_res_1653_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1654_) == 0)
{
if (lean_obj_tag(v_x_1655_) == 0)
{
uint8_t v___x_1656_; 
v___x_1656_ = 1;
return v___x_1656_;
}
else
{
uint8_t v___x_1657_; 
v___x_1657_ = 0;
return v___x_1657_;
}
}
else
{
if (lean_obj_tag(v_x_1655_) == 0)
{
uint8_t v___x_1658_; 
v___x_1658_ = 0;
return v___x_1658_;
}
else
{
lean_object* v_val_1659_; lean_object* v_val_1660_; uint8_t v___x_1661_; 
v_val_1659_ = lean_ctor_get(v_x_1654_, 0);
v_val_1660_ = lean_ctor_get(v_x_1655_, 0);
v___x_1661_ = lean_expr_eqv(v_val_1659_, v_val_1660_);
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_res_1664_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1662_, v_x_1663_);
lean_dec(v_x_1663_);
lean_dec(v_x_1662_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1666_, uint8_t v_eqTrue_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1670_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1891_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1891_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1891_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
uint8_t v_linarith_1684_; 
v_linarith_1684_ = lean_ctor_get_uint8(v_a_1680_, sizeof(void*)*13 + 22);
lean_dec(v_a_1680_);
if (v_linarith_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec_ref(v_e_1666_);
v___x_1685_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1685_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1689_ = l_Lean_Expr_getAppNumArgs(v_e_1666_);
v___x_1690_ = lean_unsigned_to_nat(4u);
v___x_1691_ = lean_nat_dec_eq(v___x_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_dec(v___x_1689_);
lean_dec_ref(v_e_1666_);
v___x_1692_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1692_);
v___x_1694_ = v___x_1682_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v___x_1689_, v___x_1696_);
lean_inc(v___x_1697_);
v___x_1698_ = l_Lean_Expr_getRevArg_x21(v_e_1666_, v___x_1697_);
lean_inc_ref(v___x_1698_);
v___x_1699_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1698_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1882_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1882_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1882_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v_strict_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; 
v___x_1704_ = lean_nat_sub(v___x_1697_, v___x_1696_);
lean_dec(v___x_1697_);
v___x_1705_ = l_Lean_Expr_getRevArg_x21(v_e_1666_, v___x_1704_);
v___x_1706_ = lean_unsigned_to_nat(2u);
v___x_1707_ = lean_nat_sub(v___x_1689_, v___x_1706_);
v___x_1708_ = lean_nat_sub(v___x_1707_, v___x_1696_);
lean_dec(v___x_1707_);
v___x_1709_ = l_Lean_Expr_getRevArg_x21(v_e_1666_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = lean_nat_sub(v___x_1689_, v___x_1710_);
lean_dec(v___x_1689_);
v___x_1712_ = lean_nat_sub(v___x_1711_, v___x_1696_);
lean_dec(v___x_1711_);
v___x_1713_ = l_Lean_Expr_getRevArg_x21(v_e_1666_, v___x_1712_);
if (lean_obj_tag(v_a_1700_) == 1)
{
lean_object* v_val_1740_; lean_object* v___x_1741_; 
lean_del_object(v___x_1702_);
lean_dec_ref(v___x_1698_);
lean_del_object(v___x_1682_);
v_val_1740_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_val_1740_);
lean_dec_ref(v_a_1700_);
v___x_1741_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1740_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1755_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1755_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1755_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_leFn_x3f_1746_; lean_object* v_ltFn_x3f_1747_; uint8_t v___x_1748_; 
v_leFn_x3f_1746_ = lean_ctor_get(v_a_1742_, 20);
lean_inc(v_leFn_x3f_1746_);
v_ltFn_x3f_1747_ = lean_ctor_get(v_a_1742_, 21);
lean_inc(v_ltFn_x3f_1747_);
lean_dec(v_a_1742_);
v___x_1748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1746_, v___x_1705_);
lean_dec(v_leFn_x3f_1746_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1747_, v___x_1705_);
lean_dec_ref(v___x_1705_);
lean_dec(v_ltFn_x3f_1747_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec(v_val_1740_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1750_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1750_);
v___x_1752_ = v___x_1744_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
else
{
lean_del_object(v___x_1744_);
v_strict_1715_ = v___x_1691_;
v___y_1716_ = v_val_1740_;
v___y_1717_ = v_a_1668_;
v___y_1718_ = v_a_1669_;
v___y_1719_ = v_a_1670_;
v___y_1720_ = v_a_1671_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
goto v___jp_1714_;
}
}
else
{
uint8_t v___x_1754_; 
lean_dec(v_ltFn_x3f_1747_);
lean_del_object(v___x_1744_);
lean_dec_ref(v___x_1705_);
v___x_1754_ = 0;
v_strict_1715_ = v___x_1754_;
v___y_1716_ = v_val_1740_;
v___y_1717_ = v_a_1668_;
v___y_1718_ = v_a_1669_;
v___y_1719_ = v_a_1670_;
v___y_1720_ = v_a_1671_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_val_1740_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_dec_ref(v_e_1666_);
v_a_1756_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1741_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1741_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v___x_1764_; 
lean_dec(v_a_1700_);
v___x_1764_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1698_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1873_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1873_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1873_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
if (lean_obj_tag(v_a_1765_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1868_; 
v_val_1769_ = lean_ctor_get(v_a_1765_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_a_1765_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1771_ = v_a_1765_;
v_isShared_1772_ = v_isSharedCheck_1868_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_val_1769_);
lean_dec(v_a_1765_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1868_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1769_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1859_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1859_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1859_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_leInst_x3f_1783_; lean_object* v_ltInst_x3f_1784_; lean_object* v_lawfulOrderLTInst_x3f_1785_; lean_object* v_isPreorderInst_x3f_1786_; lean_object* v_orderedAddInst_x3f_1787_; lean_object* v_isLinearInst_x3f_1788_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v___y_1802_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1824_; uint8_t v_strict_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1842_; uint8_t v___y_1853_; uint8_t v___y_1855_; uint8_t v___y_1857_; 
v_leInst_x3f_1783_ = lean_ctor_get(v_a_1774_, 5);
lean_inc(v_leInst_x3f_1783_);
v_ltInst_x3f_1784_ = lean_ctor_get(v_a_1774_, 6);
lean_inc(v_ltInst_x3f_1784_);
v_lawfulOrderLTInst_x3f_1785_ = lean_ctor_get(v_a_1774_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1785_);
v_isPreorderInst_x3f_1786_ = lean_ctor_get(v_a_1774_, 8);
lean_inc(v_isPreorderInst_x3f_1786_);
v_orderedAddInst_x3f_1787_ = lean_ctor_get(v_a_1774_, 9);
lean_inc(v_orderedAddInst_x3f_1787_);
v_isLinearInst_x3f_1788_ = lean_ctor_get(v_a_1774_, 10);
lean_inc(v_isLinearInst_x3f_1788_);
lean_dec(v_a_1774_);
if (lean_obj_tag(v_leInst_x3f_1783_) == 0)
{
if (v___x_1691_ == 0)
{
v___y_1857_ = v___x_1691_;
goto v___jp_1856_;
}
else
{
lean_dec(v_isPreorderInst_x3f_1786_);
v___y_1855_ = v___x_1691_;
goto v___jp_1854_;
}
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = 0;
v___y_1857_ = v___x_1858_;
goto v___jp_1856_;
}
v___jp_1778_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
v___jp_1789_:
{
if (v___y_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_dec(v_isLinearInst_x3f_1788_);
lean_del_object(v___x_1767_);
v___x_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1666_, v___x_1709_, v___x_1713_, v___y_1794_, v_eqTrue_1667_, v___y_1792_, v___y_1790_, v___y_1801_, v___y_1796_, v___y_1791_, v___y_1800_, v___y_1797_, v___y_1798_, v___y_1793_, v___y_1795_, v___y_1799_);
lean_dec(v___y_1792_);
return v___x_1803_;
}
else
{
if (lean_obj_tag(v_isLinearInst_x3f_1788_) == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
lean_dec(v___y_1792_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1804_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1804_);
v___x_1806_ = v___x_1767_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v_isLinearInst_x3f_1788_);
lean_del_object(v___x_1767_);
v___x_1808_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1666_, v___x_1709_, v___x_1713_, v___y_1794_, v_eqTrue_1667_, v___y_1792_, v___y_1790_, v___y_1801_, v___y_1796_, v___y_1791_, v___y_1800_, v___y_1797_, v___y_1798_, v___y_1793_, v___y_1795_, v___y_1799_);
lean_dec(v___y_1792_);
return v___x_1808_;
}
}
}
v___jp_1809_:
{
if (v_eqTrue_1667_ == 0)
{
v___y_1790_ = v___y_1810_;
v___y_1791_ = v___y_1811_;
v___y_1792_ = v___y_1812_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1814_;
v___y_1795_ = v___y_1815_;
v___y_1796_ = v___y_1816_;
v___y_1797_ = v___y_1817_;
v___y_1798_ = v___y_1818_;
v___y_1799_ = v___y_1819_;
v___y_1800_ = v___y_1820_;
v___y_1801_ = v___y_1821_;
v___y_1802_ = v___x_1691_;
goto v___jp_1789_;
}
else
{
v___y_1790_ = v___y_1810_;
v___y_1791_ = v___y_1811_;
v___y_1792_ = v___y_1812_;
v___y_1793_ = v___y_1813_;
v___y_1794_ = v___y_1814_;
v___y_1795_ = v___y_1815_;
v___y_1796_ = v___y_1816_;
v___y_1797_ = v___y_1817_;
v___y_1798_ = v___y_1818_;
v___y_1799_ = v___y_1819_;
v___y_1800_ = v___y_1820_;
v___y_1801_ = v___y_1821_;
v___y_1802_ = v___y_1822_;
goto v___jp_1789_;
}
}
v___jp_1823_:
{
if (v_strict_1825_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1785_);
lean_del_object(v___x_1702_);
v___y_1810_ = v___y_1827_;
v___y_1811_ = v___y_1830_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1834_;
v___y_1814_ = v_strict_1825_;
v___y_1815_ = v___y_1835_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1832_;
v___y_1818_ = v___y_1833_;
v___y_1819_ = v___y_1836_;
v___y_1820_ = v___y_1831_;
v___y_1821_ = v___y_1828_;
v___y_1822_ = v_strict_1825_;
goto v___jp_1809_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1785_) == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v___y_1826_);
lean_dec(v_isLinearInst_x3f_1788_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1837_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1837_);
v___x_1839_ = v___x_1702_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_dec_ref(v_lawfulOrderLTInst_x3f_1785_);
lean_del_object(v___x_1702_);
v___y_1810_ = v___y_1827_;
v___y_1811_ = v___y_1830_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1834_;
v___y_1814_ = v_strict_1825_;
v___y_1815_ = v___y_1835_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1832_;
v___y_1818_ = v___y_1833_;
v___y_1819_ = v___y_1836_;
v___y_1820_ = v___y_1831_;
v___y_1821_ = v___y_1828_;
v___y_1822_ = v___y_1824_;
goto v___jp_1809_;
}
}
}
v___jp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1705_);
v___x_1844_ = v___x_1771_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1705_);
v___x_1844_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1844_, v_leInst_x3f_1783_);
lean_dec(v_leInst_x3f_1783_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1844_, v_ltInst_x3f_1784_);
lean_dec(v_ltInst_x3f_1784_);
lean_dec_ref(v___x_1844_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec(v_isLinearInst_x3f_1788_);
lean_dec(v_lawfulOrderLTInst_x3f_1785_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
v___x_1847_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1847_);
v___x_1849_ = v___x_1682_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
lean_del_object(v___x_1682_);
v___y_1824_ = v___y_1842_;
v_strict_1825_ = v___x_1691_;
v___y_1826_ = v_val_1769_;
v___y_1827_ = v_a_1668_;
v___y_1828_ = v_a_1669_;
v___y_1829_ = v_a_1670_;
v___y_1830_ = v_a_1671_;
v___y_1831_ = v_a_1672_;
v___y_1832_ = v_a_1673_;
v___y_1833_ = v_a_1674_;
v___y_1834_ = v_a_1675_;
v___y_1835_ = v_a_1676_;
v___y_1836_ = v_a_1677_;
goto v___jp_1823_;
}
}
else
{
lean_dec_ref(v___x_1844_);
lean_dec(v_ltInst_x3f_1784_);
lean_del_object(v___x_1682_);
v___y_1824_ = v___y_1842_;
v_strict_1825_ = v___y_1842_;
v___y_1826_ = v_val_1769_;
v___y_1827_ = v_a_1668_;
v___y_1828_ = v_a_1669_;
v___y_1829_ = v_a_1670_;
v___y_1830_ = v_a_1671_;
v___y_1831_ = v_a_1672_;
v___y_1832_ = v_a_1673_;
v___y_1833_ = v_a_1674_;
v___y_1834_ = v_a_1675_;
v___y_1835_ = v_a_1676_;
v___y_1836_ = v_a_1677_;
goto v___jp_1823_;
}
}
}
v___jp_1852_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1787_) == 0)
{
if (v___x_1691_ == 0)
{
lean_del_object(v___x_1776_);
v___y_1842_ = v___x_1691_;
goto v___jp_1841_;
}
else
{
lean_dec(v_isLinearInst_x3f_1788_);
lean_dec(v_lawfulOrderLTInst_x3f_1785_);
lean_dec(v_ltInst_x3f_1784_);
lean_dec(v_leInst_x3f_1783_);
lean_del_object(v___x_1771_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
goto v___jp_1778_;
}
}
else
{
lean_dec_ref(v_orderedAddInst_x3f_1787_);
lean_del_object(v___x_1776_);
v___y_1842_ = v___y_1853_;
goto v___jp_1841_;
}
}
v___jp_1854_:
{
if (v___y_1855_ == 0)
{
v___y_1853_ = v___y_1855_;
goto v___jp_1852_;
}
else
{
lean_dec(v_isLinearInst_x3f_1788_);
lean_dec(v_orderedAddInst_x3f_1787_);
lean_dec(v_lawfulOrderLTInst_x3f_1785_);
lean_dec(v_ltInst_x3f_1784_);
lean_dec(v_leInst_x3f_1783_);
lean_del_object(v___x_1771_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
goto v___jp_1778_;
}
}
v___jp_1856_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_1786_) == 0)
{
v___y_1855_ = v___x_1691_;
goto v___jp_1854_;
}
else
{
lean_dec_ref(v_isPreorderInst_x3f_1786_);
v___y_1853_ = v___y_1857_;
goto v___jp_1852_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1771_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
v_a_1860_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1773_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1773_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec(v_a_1765_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
v___x_1869_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1869_);
v___x_1871_ = v___x_1767_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
v_a_1874_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1764_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1764_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
v___jp_1714_:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; uint8_t v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = lean_unbox(v_a_1728_);
lean_dec(v_a_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1666_, v___x_1709_, v___x_1713_, v_strict_1715_, v_eqTrue_1667_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1716_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1666_, v___x_1709_, v___x_1713_, v_strict_1715_, v_eqTrue_1667_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1716_);
return v___x_1731_;
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v___y_1716_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v_a_1732_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1727_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v___x_1698_);
lean_dec(v___x_1697_);
lean_dec(v___x_1689_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_1666_);
v_a_1883_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1699_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1699_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_e_1666_);
v_a_1892_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1679_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1679_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1900_, lean_object* v_eqTrue_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
uint8_t v_eqTrue_boxed_1913_; lean_object* v_res_1914_; 
v_eqTrue_boxed_1913_ = lean_unbox(v_eqTrue_1901_);
v_res_1914_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1900_, v_eqTrue_boxed_1913_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec(v_a_1902_);
return v_res_1914_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin) {
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
}
#ifdef __cplusplus
}
#endif
