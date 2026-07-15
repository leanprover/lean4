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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* v_val_3_; lean_object* v___x_4_; size_t v___x_5_; size_t v___x_6_; uint8_t v___x_7_; 
v_val_3_ = lean_ctor_get(v_fn_x3f_1_, 0);
v___x_4_ = l_Lean_Expr_appArg_x21(v_val_3_);
v___x_5_ = lean_ptr_addr(v___x_4_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_ptr_addr(v_inst_2_);
v___x_7_ = lean_usize_dec_eq(v___x_5_, v___x_6_);
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object* v_fn_x3f_9_, lean_object* v_inst_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_fn_x3f_9_, v_inst_10_);
lean_dec_ref(v_inst_10_);
lean_dec(v_fn_x3f_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(lean_object* v_c_13_, lean_object* v_x_14_, size_t v_x_15_, size_t v_x_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_cs_17_; size_t v_j_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v_cs_17_ = lean_ctor_get(v_x_14_, 0);
v_j_18_ = lean_usize_shift_right(v_x_15_, v_x_16_);
v___x_19_ = lean_usize_to_nat(v_j_18_);
v___x_20_ = lean_array_get_size(v_cs_17_);
v___x_21_ = lean_nat_dec_lt(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_dec(v___x_19_);
lean_dec_ref(v_c_13_);
return v_x_14_;
}
else
{
lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_39_; 
lean_inc_ref(v_cs_17_);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v_x_14_, 0);
lean_dec(v_unused_40_);
v___x_23_ = v_x_14_;
v_isShared_24_ = v_isSharedCheck_39_;
goto v_resetjp_22_;
}
else
{
lean_dec(v_x_14_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_39_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v_i_28_; size_t v___x_29_; size_t v_shift_30_; lean_object* v_v_31_; lean_object* v___x_32_; lean_object* v_xs_x27_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_25_ = ((size_t)1ULL);
v___x_26_ = lean_usize_shift_left(v___x_25_, v_x_16_);
v___x_27_ = lean_usize_sub(v___x_26_, v___x_25_);
v_i_28_ = lean_usize_land(v_x_15_, v___x_27_);
v___x_29_ = ((size_t)5ULL);
v_shift_30_ = lean_usize_sub(v_x_16_, v___x_29_);
v_v_31_ = lean_array_fget(v_cs_17_, v___x_19_);
v___x_32_ = lean_box(0);
v_xs_x27_33_ = lean_array_fset(v_cs_17_, v___x_19_, v___x_32_);
v___x_34_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_13_, v_v_31_, v_i_28_, v_shift_30_);
v___x_35_ = lean_array_fset(v_xs_x27_33_, v___x_19_, v___x_34_);
lean_dec(v___x_19_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_35_);
v___x_37_ = v___x_23_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_object* v_vs_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_vs_41_ = lean_ctor_get(v_x_14_, 0);
v___x_42_ = lean_usize_to_nat(v_x_15_);
v___x_43_ = lean_array_get_size(v_vs_41_);
v___x_44_ = lean_nat_dec_lt(v___x_42_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec(v___x_42_);
lean_dec_ref(v_c_13_);
return v_x_14_;
}
else
{
lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_56_; 
lean_inc_ref(v_vs_41_);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v_x_14_, 0);
lean_dec(v_unused_57_);
v___x_46_ = v_x_14_;
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
else
{
lean_dec(v_x_14_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_56_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_v_48_; lean_object* v___x_49_; lean_object* v_xs_x27_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v_v_48_ = lean_array_fget(v_vs_41_, v___x_42_);
v___x_49_ = lean_box(0);
v_xs_x27_50_ = lean_array_fset(v_vs_41_, v___x_42_, v___x_49_);
v___x_51_ = l_Lean_PersistentArray_push___redArg(v_v_48_, v_c_13_);
v___x_52_ = lean_array_fset(v_xs_x27_50_, v___x_42_, v___x_51_);
lean_dec(v___x_42_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_52_);
v___x_54_ = v___x_46_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4___boxed(lean_object* v_c_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
size_t v_x_84417__boxed_62_; size_t v_x_84418__boxed_63_; lean_object* v_res_64_; 
v_x_84417__boxed_62_ = lean_unbox_usize(v_x_60_);
lean_dec(v_x_60_);
v_x_84418__boxed_63_ = lean_unbox_usize(v_x_61_);
lean_dec(v_x_61_);
v_res_64_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_58_, v_x_59_, v_x_84417__boxed_62_, v_x_84418__boxed_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object* v_c_65_, lean_object* v_t_66_, lean_object* v_i_67_){
_start:
{
lean_object* v_root_68_; lean_object* v_tail_69_; lean_object* v_size_70_; size_t v_shift_71_; lean_object* v_tailOff_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_96_; 
v_root_68_ = lean_ctor_get(v_t_66_, 0);
v_tail_69_ = lean_ctor_get(v_t_66_, 1);
v_size_70_ = lean_ctor_get(v_t_66_, 2);
v_shift_71_ = lean_ctor_get_usize(v_t_66_, 4);
v_tailOff_72_ = lean_ctor_get(v_t_66_, 3);
v_isSharedCheck_96_ = !lean_is_exclusive(v_t_66_);
if (v_isSharedCheck_96_ == 0)
{
v___x_74_ = v_t_66_;
v_isShared_75_ = v_isSharedCheck_96_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tailOff_72_);
lean_inc(v_size_70_);
lean_inc(v_tail_69_);
lean_inc(v_root_68_);
lean_dec(v_t_66_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_96_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint8_t v___x_76_; 
v___x_76_ = lean_nat_dec_le(v_tailOff_72_, v_i_67_);
if (v___x_76_ == 0)
{
size_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_usize_of_nat(v_i_67_);
v___x_78_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_65_, v_root_68_, v___x_77_, v_shift_71_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_78_);
v___x_80_ = v___x_74_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_tail_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_size_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_tailOff_72_);
lean_ctor_set_usize(v_reuseFailAlloc_81_, 4, v_shift_71_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lean_nat_sub(v_i_67_, v_tailOff_72_);
v___x_83_ = lean_array_get_size(v_tail_69_);
v___x_84_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v___x_82_);
lean_dec_ref(v_c_65_);
if (v_isShared_75_ == 0)
{
v___x_86_ = v___x_74_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_root_68_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_tail_69_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_size_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v_tailOff_72_);
lean_ctor_set_usize(v_reuseFailAlloc_87_, 4, v_shift_71_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v_v_88_; lean_object* v___x_89_; lean_object* v_xs_x27_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_v_88_ = lean_array_fget(v_tail_69_, v___x_82_);
v___x_89_ = lean_box(0);
v_xs_x27_90_ = lean_array_fset(v_tail_69_, v___x_82_, v___x_89_);
v___x_91_ = l_Lean_PersistentArray_push___redArg(v_v_88_, v_c_65_);
v___x_92_ = lean_array_fset(v_xs_x27_90_, v___x_82_, v___x_91_);
lean_dec(v___x_82_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_92_);
v___x_94_ = v___x_74_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_root_68_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_size_70_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_tailOff_72_);
lean_ctor_set_usize(v_reuseFailAlloc_95_, 4, v_shift_71_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object* v_c_97_, lean_object* v_t_98_, lean_object* v_i_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_97_, v_t_98_, v_i_99_);
lean_dec(v_i_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object* v___y_101_, lean_object* v_c_102_, lean_object* v_v_103_, lean_object* v_s_104_){
_start:
{
lean_object* v_structs_105_; lean_object* v_typeIdOf_106_; lean_object* v_exprToStructId_107_; lean_object* v_exprToStructIdEntries_108_; lean_object* v_forbiddenNatModules_109_; lean_object* v_natStructs_110_; lean_object* v_natTypeIdOf_111_; lean_object* v_exprToNatStructId_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_structs_105_ = lean_ctor_get(v_s_104_, 0);
v_typeIdOf_106_ = lean_ctor_get(v_s_104_, 1);
v_exprToStructId_107_ = lean_ctor_get(v_s_104_, 2);
v_exprToStructIdEntries_108_ = lean_ctor_get(v_s_104_, 3);
v_forbiddenNatModules_109_ = lean_ctor_get(v_s_104_, 4);
v_natStructs_110_ = lean_ctor_get(v_s_104_, 5);
v_natTypeIdOf_111_ = lean_ctor_get(v_s_104_, 6);
v_exprToNatStructId_112_ = lean_ctor_get(v_s_104_, 7);
v___x_113_ = lean_array_get_size(v_structs_105_);
v___x_114_ = lean_nat_dec_lt(v___y_101_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec_ref(v_c_102_);
return v_s_104_;
}
else
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_176_; 
lean_inc_ref(v_exprToNatStructId_112_);
lean_inc_ref(v_natTypeIdOf_111_);
lean_inc_ref(v_natStructs_110_);
lean_inc_ref(v_forbiddenNatModules_109_);
lean_inc_ref(v_exprToStructIdEntries_108_);
lean_inc_ref(v_exprToStructId_107_);
lean_inc_ref(v_typeIdOf_106_);
lean_inc_ref(v_structs_105_);
v_isSharedCheck_176_ = !lean_is_exclusive(v_s_104_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; 
v_unused_177_ = lean_ctor_get(v_s_104_, 7);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_s_104_, 6);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_s_104_, 5);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_s_104_, 4);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_s_104_, 3);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_s_104_, 2);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_s_104_, 1);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_s_104_, 0);
lean_dec(v_unused_184_);
v___x_116_ = v_s_104_;
v_isShared_117_ = v_isSharedCheck_176_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_s_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_176_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_v_118_; lean_object* v_id_119_; lean_object* v_ringId_x3f_120_; lean_object* v_type_121_; lean_object* v_u_122_; lean_object* v_intModuleInst_123_; lean_object* v_leInst_x3f_124_; lean_object* v_ltInst_x3f_125_; lean_object* v_lawfulOrderLTInst_x3f_126_; lean_object* v_isPreorderInst_x3f_127_; lean_object* v_orderedAddInst_x3f_128_; lean_object* v_isLinearInst_x3f_129_; lean_object* v_noNatDivInst_x3f_130_; lean_object* v_ringInst_x3f_131_; lean_object* v_commRingInst_x3f_132_; lean_object* v_orderedRingInst_x3f_133_; lean_object* v_fieldInst_x3f_134_; lean_object* v_charInst_x3f_135_; lean_object* v_zero_136_; lean_object* v_ofNatZero_137_; lean_object* v_one_x3f_138_; lean_object* v_leFn_x3f_139_; lean_object* v_ltFn_x3f_140_; lean_object* v_addFn_141_; lean_object* v_zsmulFn_142_; lean_object* v_nsmulFn_143_; lean_object* v_zsmulFn_x3f_144_; lean_object* v_nsmulFn_x3f_145_; lean_object* v_homomulFn_x3f_146_; lean_object* v_subFn_147_; lean_object* v_negFn_148_; lean_object* v_vars_149_; lean_object* v_varMap_150_; lean_object* v_lowers_151_; lean_object* v_uppers_152_; lean_object* v_diseqs_153_; lean_object* v_assignment_154_; uint8_t v_caseSplits_155_; lean_object* v_conflict_x3f_156_; lean_object* v_diseqSplits_157_; lean_object* v_elimEqs_158_; lean_object* v_elimStack_159_; lean_object* v_occurs_160_; lean_object* v_ignored_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_175_; 
v_v_118_ = lean_array_fget(v_structs_105_, v___y_101_);
v_id_119_ = lean_ctor_get(v_v_118_, 0);
v_ringId_x3f_120_ = lean_ctor_get(v_v_118_, 1);
v_type_121_ = lean_ctor_get(v_v_118_, 2);
v_u_122_ = lean_ctor_get(v_v_118_, 3);
v_intModuleInst_123_ = lean_ctor_get(v_v_118_, 4);
v_leInst_x3f_124_ = lean_ctor_get(v_v_118_, 5);
v_ltInst_x3f_125_ = lean_ctor_get(v_v_118_, 6);
v_lawfulOrderLTInst_x3f_126_ = lean_ctor_get(v_v_118_, 7);
v_isPreorderInst_x3f_127_ = lean_ctor_get(v_v_118_, 8);
v_orderedAddInst_x3f_128_ = lean_ctor_get(v_v_118_, 9);
v_isLinearInst_x3f_129_ = lean_ctor_get(v_v_118_, 10);
v_noNatDivInst_x3f_130_ = lean_ctor_get(v_v_118_, 11);
v_ringInst_x3f_131_ = lean_ctor_get(v_v_118_, 12);
v_commRingInst_x3f_132_ = lean_ctor_get(v_v_118_, 13);
v_orderedRingInst_x3f_133_ = lean_ctor_get(v_v_118_, 14);
v_fieldInst_x3f_134_ = lean_ctor_get(v_v_118_, 15);
v_charInst_x3f_135_ = lean_ctor_get(v_v_118_, 16);
v_zero_136_ = lean_ctor_get(v_v_118_, 17);
v_ofNatZero_137_ = lean_ctor_get(v_v_118_, 18);
v_one_x3f_138_ = lean_ctor_get(v_v_118_, 19);
v_leFn_x3f_139_ = lean_ctor_get(v_v_118_, 20);
v_ltFn_x3f_140_ = lean_ctor_get(v_v_118_, 21);
v_addFn_141_ = lean_ctor_get(v_v_118_, 22);
v_zsmulFn_142_ = lean_ctor_get(v_v_118_, 23);
v_nsmulFn_143_ = lean_ctor_get(v_v_118_, 24);
v_zsmulFn_x3f_144_ = lean_ctor_get(v_v_118_, 25);
v_nsmulFn_x3f_145_ = lean_ctor_get(v_v_118_, 26);
v_homomulFn_x3f_146_ = lean_ctor_get(v_v_118_, 27);
v_subFn_147_ = lean_ctor_get(v_v_118_, 28);
v_negFn_148_ = lean_ctor_get(v_v_118_, 29);
v_vars_149_ = lean_ctor_get(v_v_118_, 30);
v_varMap_150_ = lean_ctor_get(v_v_118_, 31);
v_lowers_151_ = lean_ctor_get(v_v_118_, 32);
v_uppers_152_ = lean_ctor_get(v_v_118_, 33);
v_diseqs_153_ = lean_ctor_get(v_v_118_, 34);
v_assignment_154_ = lean_ctor_get(v_v_118_, 35);
v_caseSplits_155_ = lean_ctor_get_uint8(v_v_118_, sizeof(void*)*42);
v_conflict_x3f_156_ = lean_ctor_get(v_v_118_, 36);
v_diseqSplits_157_ = lean_ctor_get(v_v_118_, 37);
v_elimEqs_158_ = lean_ctor_get(v_v_118_, 38);
v_elimStack_159_ = lean_ctor_get(v_v_118_, 39);
v_occurs_160_ = lean_ctor_get(v_v_118_, 40);
v_ignored_161_ = lean_ctor_get(v_v_118_, 41);
v_isSharedCheck_175_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_175_ == 0)
{
v___x_163_ = v_v_118_;
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_ignored_161_);
lean_inc(v_occurs_160_);
lean_inc(v_elimStack_159_);
lean_inc(v_elimEqs_158_);
lean_inc(v_diseqSplits_157_);
lean_inc(v_conflict_x3f_156_);
lean_inc(v_assignment_154_);
lean_inc(v_diseqs_153_);
lean_inc(v_uppers_152_);
lean_inc(v_lowers_151_);
lean_inc(v_varMap_150_);
lean_inc(v_vars_149_);
lean_inc(v_negFn_148_);
lean_inc(v_subFn_147_);
lean_inc(v_homomulFn_x3f_146_);
lean_inc(v_nsmulFn_x3f_145_);
lean_inc(v_zsmulFn_x3f_144_);
lean_inc(v_nsmulFn_143_);
lean_inc(v_zsmulFn_142_);
lean_inc(v_addFn_141_);
lean_inc(v_ltFn_x3f_140_);
lean_inc(v_leFn_x3f_139_);
lean_inc(v_one_x3f_138_);
lean_inc(v_ofNatZero_137_);
lean_inc(v_zero_136_);
lean_inc(v_charInst_x3f_135_);
lean_inc(v_fieldInst_x3f_134_);
lean_inc(v_orderedRingInst_x3f_133_);
lean_inc(v_commRingInst_x3f_132_);
lean_inc(v_ringInst_x3f_131_);
lean_inc(v_noNatDivInst_x3f_130_);
lean_inc(v_isLinearInst_x3f_129_);
lean_inc(v_orderedAddInst_x3f_128_);
lean_inc(v_isPreorderInst_x3f_127_);
lean_inc(v_lawfulOrderLTInst_x3f_126_);
lean_inc(v_ltInst_x3f_125_);
lean_inc(v_leInst_x3f_124_);
lean_inc(v_intModuleInst_123_);
lean_inc(v_u_122_);
lean_inc(v_type_121_);
lean_inc(v_ringId_x3f_120_);
lean_inc(v_id_119_);
lean_dec(v_v_118_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v_xs_x27_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_165_ = lean_box(0);
v_xs_x27_166_ = lean_array_fset(v_structs_105_, v___y_101_, v___x_165_);
v___x_167_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_102_, v_uppers_152_, v_v_103_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 33, v___x_167_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_id_119_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_ringId_x3f_120_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_type_121_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_u_122_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v_intModuleInst_123_);
lean_ctor_set(v_reuseFailAlloc_174_, 5, v_leInst_x3f_124_);
lean_ctor_set(v_reuseFailAlloc_174_, 6, v_ltInst_x3f_125_);
lean_ctor_set(v_reuseFailAlloc_174_, 7, v_lawfulOrderLTInst_x3f_126_);
lean_ctor_set(v_reuseFailAlloc_174_, 8, v_isPreorderInst_x3f_127_);
lean_ctor_set(v_reuseFailAlloc_174_, 9, v_orderedAddInst_x3f_128_);
lean_ctor_set(v_reuseFailAlloc_174_, 10, v_isLinearInst_x3f_129_);
lean_ctor_set(v_reuseFailAlloc_174_, 11, v_noNatDivInst_x3f_130_);
lean_ctor_set(v_reuseFailAlloc_174_, 12, v_ringInst_x3f_131_);
lean_ctor_set(v_reuseFailAlloc_174_, 13, v_commRingInst_x3f_132_);
lean_ctor_set(v_reuseFailAlloc_174_, 14, v_orderedRingInst_x3f_133_);
lean_ctor_set(v_reuseFailAlloc_174_, 15, v_fieldInst_x3f_134_);
lean_ctor_set(v_reuseFailAlloc_174_, 16, v_charInst_x3f_135_);
lean_ctor_set(v_reuseFailAlloc_174_, 17, v_zero_136_);
lean_ctor_set(v_reuseFailAlloc_174_, 18, v_ofNatZero_137_);
lean_ctor_set(v_reuseFailAlloc_174_, 19, v_one_x3f_138_);
lean_ctor_set(v_reuseFailAlloc_174_, 20, v_leFn_x3f_139_);
lean_ctor_set(v_reuseFailAlloc_174_, 21, v_ltFn_x3f_140_);
lean_ctor_set(v_reuseFailAlloc_174_, 22, v_addFn_141_);
lean_ctor_set(v_reuseFailAlloc_174_, 23, v_zsmulFn_142_);
lean_ctor_set(v_reuseFailAlloc_174_, 24, v_nsmulFn_143_);
lean_ctor_set(v_reuseFailAlloc_174_, 25, v_zsmulFn_x3f_144_);
lean_ctor_set(v_reuseFailAlloc_174_, 26, v_nsmulFn_x3f_145_);
lean_ctor_set(v_reuseFailAlloc_174_, 27, v_homomulFn_x3f_146_);
lean_ctor_set(v_reuseFailAlloc_174_, 28, v_subFn_147_);
lean_ctor_set(v_reuseFailAlloc_174_, 29, v_negFn_148_);
lean_ctor_set(v_reuseFailAlloc_174_, 30, v_vars_149_);
lean_ctor_set(v_reuseFailAlloc_174_, 31, v_varMap_150_);
lean_ctor_set(v_reuseFailAlloc_174_, 32, v_lowers_151_);
lean_ctor_set(v_reuseFailAlloc_174_, 33, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_174_, 34, v_diseqs_153_);
lean_ctor_set(v_reuseFailAlloc_174_, 35, v_assignment_154_);
lean_ctor_set(v_reuseFailAlloc_174_, 36, v_conflict_x3f_156_);
lean_ctor_set(v_reuseFailAlloc_174_, 37, v_diseqSplits_157_);
lean_ctor_set(v_reuseFailAlloc_174_, 38, v_elimEqs_158_);
lean_ctor_set(v_reuseFailAlloc_174_, 39, v_elimStack_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 40, v_occurs_160_);
lean_ctor_set(v_reuseFailAlloc_174_, 41, v_ignored_161_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*42, v_caseSplits_155_);
v___x_169_ = v_reuseFailAlloc_174_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_array_fset(v_xs_x27_166_, v___y_101_, v___x_169_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_170_);
v___x_172_ = v___x_116_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_typeIdOf_106_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_exprToStructId_107_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_exprToStructIdEntries_108_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_forbiddenNatModules_109_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v_natStructs_110_);
lean_ctor_set(v_reuseFailAlloc_173_, 6, v_natTypeIdOf_111_);
lean_ctor_set(v_reuseFailAlloc_173_, 7, v_exprToNatStructId_112_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object* v___y_185_, lean_object* v_c_186_, lean_object* v_v_187_, lean_object* v_s_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(v___y_185_, v_c_186_, v_v_187_, v_s_188_);
lean_dec(v_v_187_);
lean_dec(v___y_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object* v___y_190_, lean_object* v_c_191_, lean_object* v_v_192_, lean_object* v_s_193_){
_start:
{
lean_object* v_structs_194_; lean_object* v_typeIdOf_195_; lean_object* v_exprToStructId_196_; lean_object* v_exprToStructIdEntries_197_; lean_object* v_forbiddenNatModules_198_; lean_object* v_natStructs_199_; lean_object* v_natTypeIdOf_200_; lean_object* v_exprToNatStructId_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_structs_194_ = lean_ctor_get(v_s_193_, 0);
v_typeIdOf_195_ = lean_ctor_get(v_s_193_, 1);
v_exprToStructId_196_ = lean_ctor_get(v_s_193_, 2);
v_exprToStructIdEntries_197_ = lean_ctor_get(v_s_193_, 3);
v_forbiddenNatModules_198_ = lean_ctor_get(v_s_193_, 4);
v_natStructs_199_ = lean_ctor_get(v_s_193_, 5);
v_natTypeIdOf_200_ = lean_ctor_get(v_s_193_, 6);
v_exprToNatStructId_201_ = lean_ctor_get(v_s_193_, 7);
v___x_202_ = lean_array_get_size(v_structs_194_);
v___x_203_ = lean_nat_dec_lt(v___y_190_, v___x_202_);
if (v___x_203_ == 0)
{
lean_dec_ref(v_c_191_);
return v_s_193_;
}
else
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_265_; 
lean_inc_ref(v_exprToNatStructId_201_);
lean_inc_ref(v_natTypeIdOf_200_);
lean_inc_ref(v_natStructs_199_);
lean_inc_ref(v_forbiddenNatModules_198_);
lean_inc_ref(v_exprToStructIdEntries_197_);
lean_inc_ref(v_exprToStructId_196_);
lean_inc_ref(v_typeIdOf_195_);
lean_inc_ref(v_structs_194_);
v_isSharedCheck_265_ = !lean_is_exclusive(v_s_193_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_266_ = lean_ctor_get(v_s_193_, 7);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_s_193_, 6);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_s_193_, 5);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_s_193_, 4);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_s_193_, 3);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_s_193_, 2);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_s_193_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_s_193_, 0);
lean_dec(v_unused_273_);
v___x_205_ = v_s_193_;
v_isShared_206_ = v_isSharedCheck_265_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_s_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_265_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_v_207_; lean_object* v_id_208_; lean_object* v_ringId_x3f_209_; lean_object* v_type_210_; lean_object* v_u_211_; lean_object* v_intModuleInst_212_; lean_object* v_leInst_x3f_213_; lean_object* v_ltInst_x3f_214_; lean_object* v_lawfulOrderLTInst_x3f_215_; lean_object* v_isPreorderInst_x3f_216_; lean_object* v_orderedAddInst_x3f_217_; lean_object* v_isLinearInst_x3f_218_; lean_object* v_noNatDivInst_x3f_219_; lean_object* v_ringInst_x3f_220_; lean_object* v_commRingInst_x3f_221_; lean_object* v_orderedRingInst_x3f_222_; lean_object* v_fieldInst_x3f_223_; lean_object* v_charInst_x3f_224_; lean_object* v_zero_225_; lean_object* v_ofNatZero_226_; lean_object* v_one_x3f_227_; lean_object* v_leFn_x3f_228_; lean_object* v_ltFn_x3f_229_; lean_object* v_addFn_230_; lean_object* v_zsmulFn_231_; lean_object* v_nsmulFn_232_; lean_object* v_zsmulFn_x3f_233_; lean_object* v_nsmulFn_x3f_234_; lean_object* v_homomulFn_x3f_235_; lean_object* v_subFn_236_; lean_object* v_negFn_237_; lean_object* v_vars_238_; lean_object* v_varMap_239_; lean_object* v_lowers_240_; lean_object* v_uppers_241_; lean_object* v_diseqs_242_; lean_object* v_assignment_243_; uint8_t v_caseSplits_244_; lean_object* v_conflict_x3f_245_; lean_object* v_diseqSplits_246_; lean_object* v_elimEqs_247_; lean_object* v_elimStack_248_; lean_object* v_occurs_249_; lean_object* v_ignored_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_264_; 
v_v_207_ = lean_array_fget(v_structs_194_, v___y_190_);
v_id_208_ = lean_ctor_get(v_v_207_, 0);
v_ringId_x3f_209_ = lean_ctor_get(v_v_207_, 1);
v_type_210_ = lean_ctor_get(v_v_207_, 2);
v_u_211_ = lean_ctor_get(v_v_207_, 3);
v_intModuleInst_212_ = lean_ctor_get(v_v_207_, 4);
v_leInst_x3f_213_ = lean_ctor_get(v_v_207_, 5);
v_ltInst_x3f_214_ = lean_ctor_get(v_v_207_, 6);
v_lawfulOrderLTInst_x3f_215_ = lean_ctor_get(v_v_207_, 7);
v_isPreorderInst_x3f_216_ = lean_ctor_get(v_v_207_, 8);
v_orderedAddInst_x3f_217_ = lean_ctor_get(v_v_207_, 9);
v_isLinearInst_x3f_218_ = lean_ctor_get(v_v_207_, 10);
v_noNatDivInst_x3f_219_ = lean_ctor_get(v_v_207_, 11);
v_ringInst_x3f_220_ = lean_ctor_get(v_v_207_, 12);
v_commRingInst_x3f_221_ = lean_ctor_get(v_v_207_, 13);
v_orderedRingInst_x3f_222_ = lean_ctor_get(v_v_207_, 14);
v_fieldInst_x3f_223_ = lean_ctor_get(v_v_207_, 15);
v_charInst_x3f_224_ = lean_ctor_get(v_v_207_, 16);
v_zero_225_ = lean_ctor_get(v_v_207_, 17);
v_ofNatZero_226_ = lean_ctor_get(v_v_207_, 18);
v_one_x3f_227_ = lean_ctor_get(v_v_207_, 19);
v_leFn_x3f_228_ = lean_ctor_get(v_v_207_, 20);
v_ltFn_x3f_229_ = lean_ctor_get(v_v_207_, 21);
v_addFn_230_ = lean_ctor_get(v_v_207_, 22);
v_zsmulFn_231_ = lean_ctor_get(v_v_207_, 23);
v_nsmulFn_232_ = lean_ctor_get(v_v_207_, 24);
v_zsmulFn_x3f_233_ = lean_ctor_get(v_v_207_, 25);
v_nsmulFn_x3f_234_ = lean_ctor_get(v_v_207_, 26);
v_homomulFn_x3f_235_ = lean_ctor_get(v_v_207_, 27);
v_subFn_236_ = lean_ctor_get(v_v_207_, 28);
v_negFn_237_ = lean_ctor_get(v_v_207_, 29);
v_vars_238_ = lean_ctor_get(v_v_207_, 30);
v_varMap_239_ = lean_ctor_get(v_v_207_, 31);
v_lowers_240_ = lean_ctor_get(v_v_207_, 32);
v_uppers_241_ = lean_ctor_get(v_v_207_, 33);
v_diseqs_242_ = lean_ctor_get(v_v_207_, 34);
v_assignment_243_ = lean_ctor_get(v_v_207_, 35);
v_caseSplits_244_ = lean_ctor_get_uint8(v_v_207_, sizeof(void*)*42);
v_conflict_x3f_245_ = lean_ctor_get(v_v_207_, 36);
v_diseqSplits_246_ = lean_ctor_get(v_v_207_, 37);
v_elimEqs_247_ = lean_ctor_get(v_v_207_, 38);
v_elimStack_248_ = lean_ctor_get(v_v_207_, 39);
v_occurs_249_ = lean_ctor_get(v_v_207_, 40);
v_ignored_250_ = lean_ctor_get(v_v_207_, 41);
v_isSharedCheck_264_ = !lean_is_exclusive(v_v_207_);
if (v_isSharedCheck_264_ == 0)
{
v___x_252_ = v_v_207_;
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_ignored_250_);
lean_inc(v_occurs_249_);
lean_inc(v_elimStack_248_);
lean_inc(v_elimEqs_247_);
lean_inc(v_diseqSplits_246_);
lean_inc(v_conflict_x3f_245_);
lean_inc(v_assignment_243_);
lean_inc(v_diseqs_242_);
lean_inc(v_uppers_241_);
lean_inc(v_lowers_240_);
lean_inc(v_varMap_239_);
lean_inc(v_vars_238_);
lean_inc(v_negFn_237_);
lean_inc(v_subFn_236_);
lean_inc(v_homomulFn_x3f_235_);
lean_inc(v_nsmulFn_x3f_234_);
lean_inc(v_zsmulFn_x3f_233_);
lean_inc(v_nsmulFn_232_);
lean_inc(v_zsmulFn_231_);
lean_inc(v_addFn_230_);
lean_inc(v_ltFn_x3f_229_);
lean_inc(v_leFn_x3f_228_);
lean_inc(v_one_x3f_227_);
lean_inc(v_ofNatZero_226_);
lean_inc(v_zero_225_);
lean_inc(v_charInst_x3f_224_);
lean_inc(v_fieldInst_x3f_223_);
lean_inc(v_orderedRingInst_x3f_222_);
lean_inc(v_commRingInst_x3f_221_);
lean_inc(v_ringInst_x3f_220_);
lean_inc(v_noNatDivInst_x3f_219_);
lean_inc(v_isLinearInst_x3f_218_);
lean_inc(v_orderedAddInst_x3f_217_);
lean_inc(v_isPreorderInst_x3f_216_);
lean_inc(v_lawfulOrderLTInst_x3f_215_);
lean_inc(v_ltInst_x3f_214_);
lean_inc(v_leInst_x3f_213_);
lean_inc(v_intModuleInst_212_);
lean_inc(v_u_211_);
lean_inc(v_type_210_);
lean_inc(v_ringId_x3f_209_);
lean_inc(v_id_208_);
lean_dec(v_v_207_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v_xs_x27_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_254_ = lean_box(0);
v_xs_x27_255_ = lean_array_fset(v_structs_194_, v___y_190_, v___x_254_);
v___x_256_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_191_, v_lowers_240_, v_v_192_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 32, v___x_256_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_id_208_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_ringId_x3f_209_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_type_210_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_u_211_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_intModuleInst_212_);
lean_ctor_set(v_reuseFailAlloc_263_, 5, v_leInst_x3f_213_);
lean_ctor_set(v_reuseFailAlloc_263_, 6, v_ltInst_x3f_214_);
lean_ctor_set(v_reuseFailAlloc_263_, 7, v_lawfulOrderLTInst_x3f_215_);
lean_ctor_set(v_reuseFailAlloc_263_, 8, v_isPreorderInst_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_263_, 9, v_orderedAddInst_x3f_217_);
lean_ctor_set(v_reuseFailAlloc_263_, 10, v_isLinearInst_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_263_, 11, v_noNatDivInst_x3f_219_);
lean_ctor_set(v_reuseFailAlloc_263_, 12, v_ringInst_x3f_220_);
lean_ctor_set(v_reuseFailAlloc_263_, 13, v_commRingInst_x3f_221_);
lean_ctor_set(v_reuseFailAlloc_263_, 14, v_orderedRingInst_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_263_, 15, v_fieldInst_x3f_223_);
lean_ctor_set(v_reuseFailAlloc_263_, 16, v_charInst_x3f_224_);
lean_ctor_set(v_reuseFailAlloc_263_, 17, v_zero_225_);
lean_ctor_set(v_reuseFailAlloc_263_, 18, v_ofNatZero_226_);
lean_ctor_set(v_reuseFailAlloc_263_, 19, v_one_x3f_227_);
lean_ctor_set(v_reuseFailAlloc_263_, 20, v_leFn_x3f_228_);
lean_ctor_set(v_reuseFailAlloc_263_, 21, v_ltFn_x3f_229_);
lean_ctor_set(v_reuseFailAlloc_263_, 22, v_addFn_230_);
lean_ctor_set(v_reuseFailAlloc_263_, 23, v_zsmulFn_231_);
lean_ctor_set(v_reuseFailAlloc_263_, 24, v_nsmulFn_232_);
lean_ctor_set(v_reuseFailAlloc_263_, 25, v_zsmulFn_x3f_233_);
lean_ctor_set(v_reuseFailAlloc_263_, 26, v_nsmulFn_x3f_234_);
lean_ctor_set(v_reuseFailAlloc_263_, 27, v_homomulFn_x3f_235_);
lean_ctor_set(v_reuseFailAlloc_263_, 28, v_subFn_236_);
lean_ctor_set(v_reuseFailAlloc_263_, 29, v_negFn_237_);
lean_ctor_set(v_reuseFailAlloc_263_, 30, v_vars_238_);
lean_ctor_set(v_reuseFailAlloc_263_, 31, v_varMap_239_);
lean_ctor_set(v_reuseFailAlloc_263_, 32, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 33, v_uppers_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 34, v_diseqs_242_);
lean_ctor_set(v_reuseFailAlloc_263_, 35, v_assignment_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 36, v_conflict_x3f_245_);
lean_ctor_set(v_reuseFailAlloc_263_, 37, v_diseqSplits_246_);
lean_ctor_set(v_reuseFailAlloc_263_, 38, v_elimEqs_247_);
lean_ctor_set(v_reuseFailAlloc_263_, 39, v_elimStack_248_);
lean_ctor_set(v_reuseFailAlloc_263_, 40, v_occurs_249_);
lean_ctor_set(v_reuseFailAlloc_263_, 41, v_ignored_250_);
lean_ctor_set_uint8(v_reuseFailAlloc_263_, sizeof(void*)*42, v_caseSplits_244_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_array_fset(v_xs_x27_255_, v___y_190_, v___x_258_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_259_);
v___x_261_ = v___x_205_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_typeIdOf_195_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_exprToStructId_196_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_exprToStructIdEntries_197_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_forbiddenNatModules_198_);
lean_ctor_set(v_reuseFailAlloc_262_, 5, v_natStructs_199_);
lean_ctor_set(v_reuseFailAlloc_262_, 6, v_natTypeIdOf_200_);
lean_ctor_set(v_reuseFailAlloc_262_, 7, v_exprToNatStructId_201_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object* v___y_274_, lean_object* v_c_275_, lean_object* v_v_276_, lean_object* v_s_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(v___y_274_, v_c_275_, v_v_276_, v_s_277_);
lean_dec(v_v_276_);
lean_dec(v___y_274_);
return v_res_278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_to_int(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(lean_object* v_k_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0);
v___x_296_ = lean_int_dec_eq(v_k_281_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_318_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_318_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_318_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_318_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_vars_304_; lean_object* v_zsmulFn_305_; lean_object* v_size_306_; lean_object* v___x_307_; lean_object* v___y_309_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_vars_304_ = lean_ctor_get(v_a_300_, 30);
lean_inc_ref(v_vars_304_);
lean_dec(v_a_300_);
v_zsmulFn_305_ = lean_ctor_get(v_a_298_, 23);
lean_inc_ref(v_zsmulFn_305_);
lean_dec(v_a_298_);
v_size_306_ = lean_ctor_get(v_vars_304_, 2);
v___x_307_ = l_Lean_mkIntLit(v_k_281_);
v___x_314_ = l_Lean_instInhabitedExpr;
v___x_315_ = lean_nat_dec_lt(v_x_282_, v_size_306_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_vars_304_);
v___x_316_ = l_outOfBounds___redArg(v___x_314_);
v___y_309_ = v___x_316_;
goto v___jp_308_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_PersistentArray_get_x21___redArg(v___x_314_, v_vars_304_, v_x_282_);
lean_dec_ref(v_vars_304_);
v___y_309_ = v___x_317_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_mkAppB(v_zsmulFn_305_, v___x_307_, v___y_309_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_a_298_);
v_a_319_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_299_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_299_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_297_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_297_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_352_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_352_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_352_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_352_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_vars_340_; lean_object* v_size_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_vars_340_ = lean_ctor_get(v_a_336_, 30);
lean_inc_ref(v_vars_340_);
lean_dec(v_a_336_);
v_size_341_ = lean_ctor_get(v_vars_340_, 2);
v___x_342_ = l_Lean_instInhabitedExpr;
v___x_343_ = lean_nat_dec_lt(v_x_282_, v_size_341_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_346_; 
lean_dec_ref(v_vars_340_);
v___x_344_ = l_outOfBounds___redArg(v___x_342_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_344_);
v___x_346_ = v___x_338_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l_Lean_PersistentArray_get_x21___redArg(v___x_342_, v_vars_340_, v_x_282_);
lean_dec_ref(v_vars_340_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_348_);
v___x_350_ = v___x_338_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_335_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_335_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_k_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_361_, v_x_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v_x_362_);
lean_dec(v_k_361_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(lean_object* v_p_376_, lean_object* v_acc_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
if (lean_obj_tag(v_p_376_) == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_acc_377_);
return v___x_390_;
}
else
{
lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_p_393_; lean_object* v___x_394_; 
v_k_391_ = lean_ctor_get(v_p_376_, 0);
v_v_392_ = lean_ctor_get(v_p_376_, 1);
v_p_393_ = lean_ctor_get(v_p_376_, 2);
v___x_394_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_391_, v_v_392_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_addFn_398_; lean_object* v___x_399_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_addFn_398_ = lean_ctor_get(v_a_395_, 22);
lean_inc_ref(v_addFn_398_);
lean_dec(v_a_395_);
v___x_399_ = l_Lean_mkAppB(v_addFn_398_, v_acc_377_, v_a_397_);
v_p_376_ = v_p_393_;
v_acc_377_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v_a_395_);
lean_dec_ref(v_acc_377_);
return v___x_396_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_acc_377_);
v_a_401_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_394_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_394_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(lean_object* v_p_409_, lean_object* v_acc_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_409_, v_acc_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec(v___y_412_);
lean_dec(v___y_411_);
lean_dec(v_p_409_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(lean_object* v_p_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
if (lean_obj_tag(v_p_424_) == 0)
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_zero_442_; lean_object* v___x_444_; 
v_zero_442_ = lean_ctor_get(v_a_438_, 17);
lean_inc_ref(v_zero_442_);
lean_dec(v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_zero_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_zero_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_437_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
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
else
{
lean_object* v_k_455_; lean_object* v_v_456_; lean_object* v_p_457_; lean_object* v___x_458_; 
v_k_455_ = lean_ctor_get(v_p_424_, 0);
v_v_456_ = lean_ctor_get(v_p_424_, 1);
v_p_457_ = lean_ctor_get(v_p_424_, 2);
v___x_458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_455_, v_v_456_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_457_, v_a_459_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_460_;
}
else
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_p_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_p_461_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_env_482_; lean_object* v___x_483_; lean_object* v_mctx_484_; lean_object* v_lctx_485_; lean_object* v_options_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_481_ = lean_st_ref_get(v___y_479_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_env_482_);
lean_dec(v___x_481_);
v___x_483_ = lean_st_ref_get(v___y_477_);
v_mctx_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_mctx_484_);
lean_dec(v___x_483_);
v_lctx_485_ = lean_ctor_get(v___y_476_, 2);
v_options_486_ = lean_ctor_get(v___y_478_, 2);
lean_inc_ref(v_options_486_);
lean_inc_ref(v_lctx_485_);
v___x_487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_487_, 0, v_env_482_);
lean_ctor_set(v___x_487_, 1, v_mctx_484_);
lean_ctor_set(v___x_487_, 2, v_lctx_485_);
lean_ctor_set(v___x_487_, 3, v_options_486_);
v___x_488_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_msgData_475_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object* v_msgData_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_ref_503_; lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_513_; 
v_ref_503_ = lean_ctor_get(v___y_500_, 5);
v___x_504_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_513_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_inc(v_ref_503_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_ref_503_);
lean_ctor_set(v___x_509_, 1, v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 1);
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_msg_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_520_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0));
v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_548_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_ltFn_x3f_541_; 
v_ltFn_x3f_541_ = lean_ctor_get(v_a_537_, 21);
lean_inc(v_ltFn_x3f_541_);
lean_dec(v_a_537_);
if (lean_obj_tag(v_ltFn_x3f_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; 
v_val_542_ = lean_ctor_get(v_ltFn_x3f_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_ltFn_x3f_541_, 1);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_val_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_val_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_ltFn_x3f_541_);
lean_del_object(v___x_539_);
v___x_546_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
v___x_547_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_546_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_547_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_536_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_536_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
lean_dec(v___y_557_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_597_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_leFn_x3f_590_; 
v_leFn_x3f_590_ = lean_ctor_get(v_a_586_, 20);
lean_inc(v_leFn_x3f_590_);
lean_dec(v_a_586_);
if (lean_obj_tag(v_leFn_x3f_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_593_; 
v_val_591_ = lean_ctor_get(v_leFn_x3f_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v_leFn_x3f_590_, 1);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_val_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_leFn_x3f_590_);
lean_del_object(v___x_588_);
v___x_595_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
v___x_596_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_595_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_596_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_585_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_585_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object* v_p_619_, uint8_t v_strict_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
if (v_strict_620_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_619_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_647_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_ofNatZero_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v_ofNatZero_642_ = lean_ctor_get(v_a_638_, 18);
lean_inc_ref(v_ofNatZero_642_);
lean_dec(v_a_638_);
v___x_643_ = l_Lean_mkAppB(v_a_634_, v_a_636_, v_ofNatZero_642_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_a_636_);
lean_dec(v_a_634_);
v_a_648_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_637_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_637_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_dec(v_a_634_);
return v___x_635_;
}
}
else
{
return v___x_633_;
}
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_619_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_ofNatZero_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v_ofNatZero_665_ = lean_ctor_get(v_a_661_, 18);
lean_inc_ref(v_ofNatZero_665_);
lean_dec(v_a_661_);
v___x_666_ = l_Lean_mkAppB(v_a_657_, v_a_659_, v_ofNatZero_665_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_a_659_);
lean_dec(v_a_657_);
v_a_671_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_660_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_660_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_dec(v_a_657_);
return v___x_658_;
}
}
else
{
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_p_679_, lean_object* v_strict_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v_strict_boxed_693_; lean_object* v_res_694_; 
v_strict_boxed_693_ = lean_unbox(v_strict_680_);
v_res_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_679_, v_strict_boxed_693_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_p_679_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_c_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_p_708_; uint8_t v_strict_709_; lean_object* v___x_710_; 
v_p_708_ = lean_ctor_get(v_c_695_, 0);
v_strict_709_ = lean_ctor_get_uint8(v_c_695_, sizeof(void*)*2);
v___x_710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_708_, v_strict_709_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_c_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v_c_711_);
return v_res_724_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_725_; double v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_float_of_nat(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object* v_cls_730_, lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_ref_737_; lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_783_; 
v_ref_737_ = lean_ctor_get(v___y_734_, 5);
v___x_738_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_783_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_783_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_783_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v_traceState_744_; lean_object* v_env_745_; lean_object* v_nextMacroScope_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_cache_749_; lean_object* v_messages_750_; lean_object* v_infoState_751_; lean_object* v_snapshotTasks_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_782_; 
v___x_743_ = lean_st_ref_take(v___y_735_);
v_traceState_744_ = lean_ctor_get(v___x_743_, 4);
v_env_745_ = lean_ctor_get(v___x_743_, 0);
v_nextMacroScope_746_ = lean_ctor_get(v___x_743_, 1);
v_ngen_747_ = lean_ctor_get(v___x_743_, 2);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_743_, 3);
v_cache_749_ = lean_ctor_get(v___x_743_, 5);
v_messages_750_ = lean_ctor_get(v___x_743_, 6);
v_infoState_751_ = lean_ctor_get(v___x_743_, 7);
v_snapshotTasks_752_ = lean_ctor_get(v___x_743_, 8);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_782_ == 0)
{
v___x_754_ = v___x_743_;
v_isShared_755_ = v_isSharedCheck_782_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snapshotTasks_752_);
lean_inc(v_infoState_751_);
lean_inc(v_messages_750_);
lean_inc(v_cache_749_);
lean_inc(v_traceState_744_);
lean_inc(v_auxDeclNGen_748_);
lean_inc(v_ngen_747_);
lean_inc(v_nextMacroScope_746_);
lean_inc(v_env_745_);
lean_dec(v___x_743_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_782_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
uint64_t v_tid_756_; lean_object* v_traces_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_781_; 
v_tid_756_ = lean_ctor_get_uint64(v_traceState_744_, sizeof(void*)*1);
v_traces_757_ = lean_ctor_get(v_traceState_744_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_traceState_744_);
if (v_isSharedCheck_781_ == 0)
{
v___x_759_ = v_traceState_744_;
v_isShared_760_ = v_isSharedCheck_781_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_traces_757_);
lean_dec(v_traceState_744_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_781_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; double v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_761_ = lean_box(0);
v___x_762_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0);
v___x_763_ = 0;
v___x_764_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1));
v___x_765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_765_, 0, v_cls_730_);
lean_ctor_set(v___x_765_, 1, v___x_761_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set_float(v___x_765_, sizeof(void*)*3, v___x_762_);
lean_ctor_set_float(v___x_765_, sizeof(void*)*3 + 8, v___x_762_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*3 + 16, v___x_763_);
v___x_766_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2));
v___x_767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v_a_739_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
lean_inc(v_ref_737_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_ref_737_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_PersistentArray_push___redArg(v_traces_757_, v___x_768_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_769_);
v___x_771_ = v___x_759_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_769_);
lean_ctor_set_uint64(v_reuseFailAlloc_780_, sizeof(void*)*1, v_tid_756_);
v___x_771_ = v_reuseFailAlloc_780_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 4, v___x_771_);
v___x_773_ = v___x_754_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_env_745_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_nextMacroScope_746_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_ngen_747_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_auxDeclNGen_748_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v_cache_749_);
lean_ctor_set(v_reuseFailAlloc_779_, 6, v_messages_750_);
lean_ctor_set(v_reuseFailAlloc_779_, 7, v_infoState_751_);
lean_ctor_set(v_reuseFailAlloc_779_, 8, v_snapshotTasks_752_);
v___x_773_ = v_reuseFailAlloc_779_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_st_ref_set(v___y_735_, v___x_773_);
v___x_775_ = lean_box(0);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_775_);
v___x_777_ = v___x_741_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(lean_object* v_cls_784_, lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_784_, v_msg_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_nat_to_int(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_806_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_807_ = l_Lean_Name_append(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_814_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_815_ = l_Lean_Name_append(v___x_814_, v___x_813_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_823_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_824_ = l_Lean_Name_append(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16(void){
_start:
{
lean_object* v_cls_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_cls_829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_830_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_831_ = l_Lean_Name_append(v___x_830_, v_cls_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* v_c_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v_options_922_; lean_object* v_inheritedTraceOptions_923_; uint8_t v_hasTrace_924_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; 
v_options_922_ = lean_ctor_get(v_a_842_, 2);
v_inheritedTraceOptions_923_ = lean_ctor_get(v_a_842_, 13);
v_hasTrace_924_ = lean_ctor_get_uint8(v_options_922_, sizeof(void*)*1);
if (v_hasTrace_924_ == 0)
{
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
v___y_936_ = v_a_843_;
goto v___jp_925_;
}
else
{
lean_object* v_cls_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_cls_997_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_998_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_999_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_923_, v_options_922_, v___x_998_);
if (v___x_999_ == 0)
{
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
v___y_936_ = v_a_843_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_MessageData_ofExpr(v_a_1001_);
v___x_1003_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_997_, v___x_1002_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref_known(v___x_1003_, 1);
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
v___y_936_ = v_a_843_;
goto v___jp_925_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_1003_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_c_832_);
v_a_1004_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1000_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1000_);
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
}
v___jp_845_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
v___jp_848_:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_c_832_);
v___x_861_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_860_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
v___jp_862_:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_832_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_888_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v___x_880_; uint8_t v___x_881_; uint8_t v___x_882_; 
v___x_880_ = 0;
v___x_881_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___x_882_ = l_Lean_instBEqLBool_beq(v___x_881_, v___x_880_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_885_; 
lean_dec(v___y_863_);
v___x_883_ = lean_box(0);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_883_);
v___x_885_ = v___x_878_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_887_; 
lean_del_object(v___x_878_);
v___x_887_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_863_, v___y_864_, v___y_865_);
return v___x_887_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v___y_863_);
v_a_889_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_875_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_875_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_897_:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_900_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; uint8_t v___x_915_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_915_ = lean_int_dec_lt(v___y_899_, v___x_914_);
lean_dec(v___y_899_);
if (v___x_915_ == 0)
{
lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc_ref(v_c_832_);
lean_inc(v___y_902_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_916_, 0, v___y_902_);
lean_closure_set(v___f_916_, 1, v_c_832_);
lean_closure_set(v___f_916_, 2, v___y_898_);
v___x_917_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_918_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_917_, v___f_916_, v___y_903_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_dec_ref_known(v___x_918_, 1);
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
v___y_874_ = v___y_912_;
goto v___jp_862_;
}
else
{
lean_dec(v___y_901_);
lean_dec_ref(v_c_832_);
return v___x_918_;
}
}
else
{
lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc_ref(v_c_832_);
lean_inc(v___y_902_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(v___f_919_, 0, v___y_902_);
lean_closure_set(v___f_919_, 1, v_c_832_);
lean_closure_set(v___f_919_, 2, v___y_898_);
v___x_920_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_921_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_920_, v___f_919_, v___y_903_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref_known(v___x_921_, 1);
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
v___y_874_ = v___y_912_;
goto v___jp_862_;
}
else
{
lean_dec(v___y_901_);
lean_dec_ref(v_c_832_);
return v___x_921_;
}
}
}
else
{
lean_dec(v___y_901_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v_c_832_);
return v___x_913_;
}
}
v___jp_925_:
{
lean_object* v_p_937_; 
v_p_937_ = lean_ctor_get(v_c_832_, 0);
if (lean_obj_tag(v_p_937_) == 0)
{
uint8_t v_strict_938_; 
v_strict_938_ = lean_ctor_get_uint8(v_c_832_, sizeof(void*)*2);
if (v_strict_938_ == 0)
{
lean_object* v_options_939_; uint8_t v_hasTrace_940_; 
v_options_939_ = lean_ctor_get(v___y_935_, 2);
v_hasTrace_940_ = lean_ctor_get_uint8(v_options_939_, sizeof(void*)*1);
if (v_hasTrace_940_ == 0)
{
lean_dec_ref(v_c_832_);
goto v___jp_845_;
}
else
{
lean_object* v_inheritedTraceOptions_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_inheritedTraceOptions_941_ = lean_ctor_get(v___y_935_, 13);
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_941_, v_options_939_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_c_832_);
goto v___jp_845_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec_ref(v_c_832_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l_Lean_MessageData_ofExpr(v_a_946_);
v___x_948_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_942_, v___x_947_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_948_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_945_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_945_);
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
}
}
else
{
lean_object* v_options_957_; uint8_t v_hasTrace_958_; 
v_options_957_ = lean_ctor_get(v___y_935_, 2);
v_hasTrace_958_ = lean_ctor_get_uint8(v_options_957_, sizeof(void*)*1);
if (v_hasTrace_958_ == 0)
{
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
v___y_859_ = v___y_936_;
goto v___jp_848_;
}
else
{
lean_object* v_inheritedTraceOptions_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_inheritedTraceOptions_959_ = lean_ctor_get(v___y_935_, 13);
v___x_960_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_961_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_959_, v_options_957_, v___x_961_);
if (v___x_962_ == 0)
{
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
v___y_859_ = v___y_936_;
goto v___jp_848_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = l_Lean_MessageData_ofExpr(v_a_964_);
v___x_966_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_960_, v___x_965_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_dec_ref_known(v___x_966_, 1);
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
v___y_859_ = v___y_936_;
goto v___jp_848_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_966_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_c_832_);
v_a_967_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_963_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_963_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_975_; uint8_t v_hasTrace_976_; 
v_options_975_ = lean_ctor_get(v___y_935_, 2);
v_hasTrace_976_ = lean_ctor_get_uint8(v_options_975_, sizeof(void*)*1);
if (v_hasTrace_976_ == 0)
{
lean_object* v_k_977_; lean_object* v_v_978_; 
v_k_977_ = lean_ctor_get(v_p_937_, 0);
v_v_978_ = lean_ctor_get(v_p_937_, 1);
lean_inc_ref(v_p_937_);
lean_inc(v_k_977_);
lean_inc_n(v_v_978_, 2);
v___y_898_ = v_v_978_;
v___y_899_ = v_k_977_;
v___y_900_ = v_p_937_;
v___y_901_ = v_v_978_;
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
v___y_912_ = v___y_936_;
goto v___jp_897_;
}
else
{
lean_object* v_k_979_; lean_object* v_v_980_; lean_object* v_inheritedTraceOptions_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_k_979_ = lean_ctor_get(v_p_937_, 0);
v_v_980_ = lean_ctor_get(v_p_937_, 1);
v_inheritedTraceOptions_981_ = lean_ctor_get(v___y_935_, 13);
v___x_982_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_983_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_981_, v_options_975_, v___x_983_);
if (v___x_984_ == 0)
{
lean_inc_ref(v_p_937_);
lean_inc(v_k_979_);
lean_inc_n(v_v_980_, 2);
v___y_898_ = v_v_980_;
v___y_899_ = v_k_979_;
v___y_900_ = v_p_937_;
v___y_901_ = v_v_980_;
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
v___y_912_ = v___y_936_;
goto v___jp_897_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_MessageData_ofExpr(v_a_986_);
v___x_988_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_982_, v___x_987_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_dec_ref_known(v___x_988_, 1);
lean_inc_ref(v_p_937_);
lean_inc(v_k_979_);
lean_inc_n(v_v_980_, 2);
v___y_898_ = v_v_980_;
v___y_899_ = v_k_979_;
v___y_900_ = v_p_937_;
v___y_901_ = v_v_980_;
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
v___y_912_ = v___y_936_;
goto v___jp_897_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_988_;
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v_c_832_);
v_a_989_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_985_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec(v_a_1013_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1026_, v_msg_1027_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1041_, lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1041_, v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec(v___y_1043_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1057_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1071_, v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1086_, lean_object* v_e_1087_, lean_object* v_s_1088_){
_start:
{
lean_object* v_structs_1089_; lean_object* v_typeIdOf_1090_; lean_object* v_exprToStructId_1091_; lean_object* v_exprToStructIdEntries_1092_; lean_object* v_forbiddenNatModules_1093_; lean_object* v_natStructs_1094_; lean_object* v_natTypeIdOf_1095_; lean_object* v_exprToNatStructId_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_structs_1089_ = lean_ctor_get(v_s_1088_, 0);
v_typeIdOf_1090_ = lean_ctor_get(v_s_1088_, 1);
v_exprToStructId_1091_ = lean_ctor_get(v_s_1088_, 2);
v_exprToStructIdEntries_1092_ = lean_ctor_get(v_s_1088_, 3);
v_forbiddenNatModules_1093_ = lean_ctor_get(v_s_1088_, 4);
v_natStructs_1094_ = lean_ctor_get(v_s_1088_, 5);
v_natTypeIdOf_1095_ = lean_ctor_get(v_s_1088_, 6);
v_exprToNatStructId_1096_ = lean_ctor_get(v_s_1088_, 7);
v___x_1097_ = lean_array_get_size(v_structs_1089_);
v___x_1098_ = lean_nat_dec_lt(v_a_1086_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_dec_ref(v_e_1087_);
return v_s_1088_;
}
else
{
lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1160_; 
lean_inc_ref(v_exprToNatStructId_1096_);
lean_inc_ref(v_natTypeIdOf_1095_);
lean_inc_ref(v_natStructs_1094_);
lean_inc_ref(v_forbiddenNatModules_1093_);
lean_inc_ref(v_exprToStructIdEntries_1092_);
lean_inc_ref(v_exprToStructId_1091_);
lean_inc_ref(v_typeIdOf_1090_);
lean_inc_ref(v_structs_1089_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_s_1088_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; 
v_unused_1161_ = lean_ctor_get(v_s_1088_, 7);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_s_1088_, 6);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_s_1088_, 5);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_s_1088_, 4);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_s_1088_, 3);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_s_1088_, 2);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_s_1088_, 1);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_s_1088_, 0);
lean_dec(v_unused_1168_);
v___x_1100_ = v_s_1088_;
v_isShared_1101_ = v_isSharedCheck_1160_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v_s_1088_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1160_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_v_1102_; lean_object* v_id_1103_; lean_object* v_ringId_x3f_1104_; lean_object* v_type_1105_; lean_object* v_u_1106_; lean_object* v_intModuleInst_1107_; lean_object* v_leInst_x3f_1108_; lean_object* v_ltInst_x3f_1109_; lean_object* v_lawfulOrderLTInst_x3f_1110_; lean_object* v_isPreorderInst_x3f_1111_; lean_object* v_orderedAddInst_x3f_1112_; lean_object* v_isLinearInst_x3f_1113_; lean_object* v_noNatDivInst_x3f_1114_; lean_object* v_ringInst_x3f_1115_; lean_object* v_commRingInst_x3f_1116_; lean_object* v_orderedRingInst_x3f_1117_; lean_object* v_fieldInst_x3f_1118_; lean_object* v_charInst_x3f_1119_; lean_object* v_zero_1120_; lean_object* v_ofNatZero_1121_; lean_object* v_one_x3f_1122_; lean_object* v_leFn_x3f_1123_; lean_object* v_ltFn_x3f_1124_; lean_object* v_addFn_1125_; lean_object* v_zsmulFn_1126_; lean_object* v_nsmulFn_1127_; lean_object* v_zsmulFn_x3f_1128_; lean_object* v_nsmulFn_x3f_1129_; lean_object* v_homomulFn_x3f_1130_; lean_object* v_subFn_1131_; lean_object* v_negFn_1132_; lean_object* v_vars_1133_; lean_object* v_varMap_1134_; lean_object* v_lowers_1135_; lean_object* v_uppers_1136_; lean_object* v_diseqs_1137_; lean_object* v_assignment_1138_; uint8_t v_caseSplits_1139_; lean_object* v_conflict_x3f_1140_; lean_object* v_diseqSplits_1141_; lean_object* v_elimEqs_1142_; lean_object* v_elimStack_1143_; lean_object* v_occurs_1144_; lean_object* v_ignored_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1159_; 
v_v_1102_ = lean_array_fget(v_structs_1089_, v_a_1086_);
v_id_1103_ = lean_ctor_get(v_v_1102_, 0);
v_ringId_x3f_1104_ = lean_ctor_get(v_v_1102_, 1);
v_type_1105_ = lean_ctor_get(v_v_1102_, 2);
v_u_1106_ = lean_ctor_get(v_v_1102_, 3);
v_intModuleInst_1107_ = lean_ctor_get(v_v_1102_, 4);
v_leInst_x3f_1108_ = lean_ctor_get(v_v_1102_, 5);
v_ltInst_x3f_1109_ = lean_ctor_get(v_v_1102_, 6);
v_lawfulOrderLTInst_x3f_1110_ = lean_ctor_get(v_v_1102_, 7);
v_isPreorderInst_x3f_1111_ = lean_ctor_get(v_v_1102_, 8);
v_orderedAddInst_x3f_1112_ = lean_ctor_get(v_v_1102_, 9);
v_isLinearInst_x3f_1113_ = lean_ctor_get(v_v_1102_, 10);
v_noNatDivInst_x3f_1114_ = lean_ctor_get(v_v_1102_, 11);
v_ringInst_x3f_1115_ = lean_ctor_get(v_v_1102_, 12);
v_commRingInst_x3f_1116_ = lean_ctor_get(v_v_1102_, 13);
v_orderedRingInst_x3f_1117_ = lean_ctor_get(v_v_1102_, 14);
v_fieldInst_x3f_1118_ = lean_ctor_get(v_v_1102_, 15);
v_charInst_x3f_1119_ = lean_ctor_get(v_v_1102_, 16);
v_zero_1120_ = lean_ctor_get(v_v_1102_, 17);
v_ofNatZero_1121_ = lean_ctor_get(v_v_1102_, 18);
v_one_x3f_1122_ = lean_ctor_get(v_v_1102_, 19);
v_leFn_x3f_1123_ = lean_ctor_get(v_v_1102_, 20);
v_ltFn_x3f_1124_ = lean_ctor_get(v_v_1102_, 21);
v_addFn_1125_ = lean_ctor_get(v_v_1102_, 22);
v_zsmulFn_1126_ = lean_ctor_get(v_v_1102_, 23);
v_nsmulFn_1127_ = lean_ctor_get(v_v_1102_, 24);
v_zsmulFn_x3f_1128_ = lean_ctor_get(v_v_1102_, 25);
v_nsmulFn_x3f_1129_ = lean_ctor_get(v_v_1102_, 26);
v_homomulFn_x3f_1130_ = lean_ctor_get(v_v_1102_, 27);
v_subFn_1131_ = lean_ctor_get(v_v_1102_, 28);
v_negFn_1132_ = lean_ctor_get(v_v_1102_, 29);
v_vars_1133_ = lean_ctor_get(v_v_1102_, 30);
v_varMap_1134_ = lean_ctor_get(v_v_1102_, 31);
v_lowers_1135_ = lean_ctor_get(v_v_1102_, 32);
v_uppers_1136_ = lean_ctor_get(v_v_1102_, 33);
v_diseqs_1137_ = lean_ctor_get(v_v_1102_, 34);
v_assignment_1138_ = lean_ctor_get(v_v_1102_, 35);
v_caseSplits_1139_ = lean_ctor_get_uint8(v_v_1102_, sizeof(void*)*42);
v_conflict_x3f_1140_ = lean_ctor_get(v_v_1102_, 36);
v_diseqSplits_1141_ = lean_ctor_get(v_v_1102_, 37);
v_elimEqs_1142_ = lean_ctor_get(v_v_1102_, 38);
v_elimStack_1143_ = lean_ctor_get(v_v_1102_, 39);
v_occurs_1144_ = lean_ctor_get(v_v_1102_, 40);
v_ignored_1145_ = lean_ctor_get(v_v_1102_, 41);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_v_1102_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1147_ = v_v_1102_;
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_ignored_1145_);
lean_inc(v_occurs_1144_);
lean_inc(v_elimStack_1143_);
lean_inc(v_elimEqs_1142_);
lean_inc(v_diseqSplits_1141_);
lean_inc(v_conflict_x3f_1140_);
lean_inc(v_assignment_1138_);
lean_inc(v_diseqs_1137_);
lean_inc(v_uppers_1136_);
lean_inc(v_lowers_1135_);
lean_inc(v_varMap_1134_);
lean_inc(v_vars_1133_);
lean_inc(v_negFn_1132_);
lean_inc(v_subFn_1131_);
lean_inc(v_homomulFn_x3f_1130_);
lean_inc(v_nsmulFn_x3f_1129_);
lean_inc(v_zsmulFn_x3f_1128_);
lean_inc(v_nsmulFn_1127_);
lean_inc(v_zsmulFn_1126_);
lean_inc(v_addFn_1125_);
lean_inc(v_ltFn_x3f_1124_);
lean_inc(v_leFn_x3f_1123_);
lean_inc(v_one_x3f_1122_);
lean_inc(v_ofNatZero_1121_);
lean_inc(v_zero_1120_);
lean_inc(v_charInst_x3f_1119_);
lean_inc(v_fieldInst_x3f_1118_);
lean_inc(v_orderedRingInst_x3f_1117_);
lean_inc(v_commRingInst_x3f_1116_);
lean_inc(v_ringInst_x3f_1115_);
lean_inc(v_noNatDivInst_x3f_1114_);
lean_inc(v_isLinearInst_x3f_1113_);
lean_inc(v_orderedAddInst_x3f_1112_);
lean_inc(v_isPreorderInst_x3f_1111_);
lean_inc(v_lawfulOrderLTInst_x3f_1110_);
lean_inc(v_ltInst_x3f_1109_);
lean_inc(v_leInst_x3f_1108_);
lean_inc(v_intModuleInst_1107_);
lean_inc(v_u_1106_);
lean_inc(v_type_1105_);
lean_inc(v_ringId_x3f_1104_);
lean_inc(v_id_1103_);
lean_dec(v_v_1102_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v_xs_x27_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = lean_box(0);
v_xs_x27_1150_ = lean_array_fset(v_structs_1089_, v_a_1086_, v___x_1149_);
v___x_1151_ = l_Lean_PersistentArray_push___redArg(v_ignored_1145_, v_e_1087_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 41, v___x_1151_);
v___x_1153_ = v___x_1147_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_id_1103_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_ringId_x3f_1104_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_type_1105_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_u_1106_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_intModuleInst_1107_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_leInst_x3f_1108_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_ltInst_x3f_1109_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_lawfulOrderLTInst_x3f_1110_);
lean_ctor_set(v_reuseFailAlloc_1158_, 8, v_isPreorderInst_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1158_, 9, v_orderedAddInst_x3f_1112_);
lean_ctor_set(v_reuseFailAlloc_1158_, 10, v_isLinearInst_x3f_1113_);
lean_ctor_set(v_reuseFailAlloc_1158_, 11, v_noNatDivInst_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1158_, 12, v_ringInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1158_, 13, v_commRingInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1158_, 14, v_orderedRingInst_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1158_, 15, v_fieldInst_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1158_, 16, v_charInst_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1158_, 17, v_zero_1120_);
lean_ctor_set(v_reuseFailAlloc_1158_, 18, v_ofNatZero_1121_);
lean_ctor_set(v_reuseFailAlloc_1158_, 19, v_one_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1158_, 20, v_leFn_x3f_1123_);
lean_ctor_set(v_reuseFailAlloc_1158_, 21, v_ltFn_x3f_1124_);
lean_ctor_set(v_reuseFailAlloc_1158_, 22, v_addFn_1125_);
lean_ctor_set(v_reuseFailAlloc_1158_, 23, v_zsmulFn_1126_);
lean_ctor_set(v_reuseFailAlloc_1158_, 24, v_nsmulFn_1127_);
lean_ctor_set(v_reuseFailAlloc_1158_, 25, v_zsmulFn_x3f_1128_);
lean_ctor_set(v_reuseFailAlloc_1158_, 26, v_nsmulFn_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1158_, 27, v_homomulFn_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1158_, 28, v_subFn_1131_);
lean_ctor_set(v_reuseFailAlloc_1158_, 29, v_negFn_1132_);
lean_ctor_set(v_reuseFailAlloc_1158_, 30, v_vars_1133_);
lean_ctor_set(v_reuseFailAlloc_1158_, 31, v_varMap_1134_);
lean_ctor_set(v_reuseFailAlloc_1158_, 32, v_lowers_1135_);
lean_ctor_set(v_reuseFailAlloc_1158_, 33, v_uppers_1136_);
lean_ctor_set(v_reuseFailAlloc_1158_, 34, v_diseqs_1137_);
lean_ctor_set(v_reuseFailAlloc_1158_, 35, v_assignment_1138_);
lean_ctor_set(v_reuseFailAlloc_1158_, 36, v_conflict_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1158_, 37, v_diseqSplits_1141_);
lean_ctor_set(v_reuseFailAlloc_1158_, 38, v_elimEqs_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 39, v_elimStack_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 40, v_occurs_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 41, v___x_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1158_, sizeof(void*)*42, v_caseSplits_1139_);
v___x_1153_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_array_fset(v_xs_x27_1150_, v_a_1086_, v___x_1153_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1154_);
v___x_1156_ = v___x_1100_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_typeIdOf_1090_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_exprToStructId_1091_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_exprToStructIdEntries_1092_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_forbiddenNatModules_1093_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_natStructs_1094_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_natTypeIdOf_1095_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_exprToNatStructId_1096_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1169_, lean_object* v_e_1170_, lean_object* v_s_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1169_, v_e_1170_, v_s_1171_);
lean_dec(v_a_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1173_, lean_object* v_lhs_1174_, lean_object* v_rhs_1175_, uint8_t v_strict_1176_, uint8_t v_eqTrue_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1190_ = 0;
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_box(v___x_1190_);
v___x_1193_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1193_, 0, v_lhs_1174_);
lean_closure_set(v___x_1193_, 1, v___x_1192_);
lean_closure_set(v___x_1193_, 2, v___x_1191_);
v___x_1194_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1193_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1349_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1349_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1349_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
if (lean_obj_tag(v_a_1195_) == 1)
{
lean_object* v_val_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1197_);
v_val_1199_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_a_1195_, 1);
v___x_1200_ = lean_box(v___x_1190_);
v___x_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1201_, 0, v_rhs_1175_);
lean_closure_set(v___x_1201_, 1, v___x_1200_);
lean_closure_set(v___x_1201_, 2, v___x_1191_);
v___x_1202_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1201_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1336_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1336_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1336_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
if (lean_obj_tag(v_a_1203_) == 1)
{
lean_object* v_val_1207_; lean_object* v___x_1208_; 
lean_del_object(v___x_1205_);
v_val_1207_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v_a_1203_, 1);
v___x_1208_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1173_, v_a_1179_);
if (lean_obj_tag(v___x_1208_) == 0)
{
if (v_eqTrue_1177_ == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; uint8_t v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_unbox(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_a_1211_);
lean_dec(v_a_1209_);
lean_dec(v_val_1207_);
lean_dec(v_val_1199_);
lean_inc(v_a_1178_);
v___f_1213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1213_, 0, v_a_1178_);
lean_closure_set(v___f_1213_, 1, v_e_1173_);
v___x_1214_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1215_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1214_, v___f_1213_, v_a_1179_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___y_1219_; 
lean_inc(v_val_1199_);
lean_inc(v_val_1207_);
v___x_1216_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_val_1207_);
lean_ctor_set(v___x_1216_, 1, v_val_1199_);
v___x_1217_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1216_);
if (v_strict_1176_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
v___y_1219_ = v___x_1266_;
goto v___jp_1218_;
}
else
{
lean_dec(v_a_1211_);
v___y_1219_ = v_eqTrue_1177_;
goto v___jp_1218_;
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v_e_1173_);
lean_ctor_set(v___x_1220_, 1, v_val_1199_);
lean_ctor_set(v___x_1220_, 2, v_val_1207_);
v___x_1221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1217_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*2, v___y_1219_);
v___x_1222_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1221_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v_p_1224_; lean_object* v___x_1225_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_p_1224_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_a_1209_);
lean_inc_ref(v_p_1224_);
v___x_1225_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1224_, v_a_1209_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1226_, v___x_1190_, v_a_1209_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1241_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1241_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1241_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
if (lean_obj_tag(v_a_1228_) == 1)
{
lean_object* v_val_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_del_object(v___x_1230_);
v_val_1232_ = lean_ctor_get(v_a_1228_, 0);
lean_inc_n(v_val_1232_, 2);
lean_dec_ref_known(v_a_1228_, 1);
v___x_1233_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1232_);
v___x_1234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_a_1223_);
lean_ctor_set(v___x_1234_, 1, v_val_1232_);
v___x_1235_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*2, v___y_1219_);
v___x_1236_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1235_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec(v_a_1228_);
lean_dec(v_a_1223_);
v___x_1237_ = lean_box(0);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1237_);
v___x_1239_ = v___x_1230_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1223_);
v_a_1242_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1227_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1227_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1223_);
lean_dec(v_a_1209_);
v_a_1250_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1225_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1225_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1209_);
v_a_1258_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1222_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1222_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1209_);
lean_dec(v_val_1207_);
lean_dec(v_val_1199_);
lean_dec_ref(v_e_1173_);
v_a_1267_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1210_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1210_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1275_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1208_, 1);
lean_inc(v_val_1207_);
lean_inc(v_val_1199_);
v___x_1276_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_val_1199_);
lean_ctor_set(v___x_1276_, 1, v_val_1207_);
v___x_1277_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1278_, 0, v_e_1173_);
lean_ctor_set(v___x_1278_, 1, v_val_1199_);
lean_ctor_set(v___x_1278_, 2, v_val_1207_);
v___x_1279_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*2, v_strict_1176_);
v___x_1280_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1279_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_p_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_p_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_a_1275_);
lean_inc_ref(v_p_1282_);
v___x_1283_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1282_, v_a_1275_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1284_, v___x_1190_, v_a_1275_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1299_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1299_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1299_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
if (lean_obj_tag(v_a_1286_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_del_object(v___x_1288_);
v_val_1290_ = lean_ctor_get(v_a_1286_, 0);
lean_inc_n(v_val_1290_, 2);
lean_dec_ref_known(v_a_1286_, 1);
v___x_1291_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1290_);
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1281_);
lean_ctor_set(v___x_1292_, 1, v_val_1290_);
v___x_1293_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*2, v_strict_1176_);
v___x_1294_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1293_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec(v_a_1286_);
lean_dec(v_a_1281_);
v___x_1295_ = lean_box(0);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1295_);
v___x_1297_ = v___x_1288_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1281_);
v_a_1300_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1285_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1285_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1281_);
lean_dec(v_a_1275_);
v_a_1308_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1283_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1283_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_a_1275_);
v_a_1316_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1280_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1280_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_val_1207_);
lean_dec(v_val_1199_);
lean_dec_ref(v_e_1173_);
v_a_1324_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1208_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1208_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_a_1203_);
lean_dec(v_val_1199_);
lean_dec_ref(v_e_1173_);
v___x_1332_ = lean_box(0);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1332_);
v___x_1334_ = v___x_1205_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_val_1199_);
lean_dec_ref(v_e_1173_);
v_a_1337_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1202_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1202_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_a_1195_);
lean_dec_ref(v_rhs_1175_);
lean_dec_ref(v_e_1173_);
v___x_1345_ = lean_box(0);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1345_);
v___x_1347_ = v___x_1197_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_rhs_1175_);
lean_dec_ref(v_e_1173_);
v_a_1350_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1194_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1194_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1358_ = _args[0];
lean_object* v_lhs_1359_ = _args[1];
lean_object* v_rhs_1360_ = _args[2];
lean_object* v_strict_1361_ = _args[3];
lean_object* v_eqTrue_1362_ = _args[4];
lean_object* v_a_1363_ = _args[5];
lean_object* v_a_1364_ = _args[6];
lean_object* v_a_1365_ = _args[7];
lean_object* v_a_1366_ = _args[8];
lean_object* v_a_1367_ = _args[9];
lean_object* v_a_1368_ = _args[10];
lean_object* v_a_1369_ = _args[11];
lean_object* v_a_1370_ = _args[12];
lean_object* v_a_1371_ = _args[13];
lean_object* v_a_1372_ = _args[14];
lean_object* v_a_1373_ = _args[15];
lean_object* v_a_1374_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1375_; uint8_t v_eqTrue_boxed_1376_; lean_object* v_res_1377_; 
v_strict_boxed_1375_ = lean_unbox(v_strict_1361_);
v_eqTrue_boxed_1376_ = lean_unbox(v_eqTrue_1362_);
v_res_1377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1358_, v_lhs_1359_, v_rhs_1360_, v_strict_boxed_1375_, v_eqTrue_boxed_1376_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1378_, lean_object* v_lhs_1379_, lean_object* v_rhs_1380_, uint8_t v_strict_1381_, uint8_t v_eqTrue_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1379_, v_a_1384_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = 0;
v___x_1398_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1379_, v___x_1397_, v_a_1396_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1465_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1465_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1465_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
if (lean_obj_tag(v_a_1399_) == 1)
{
lean_object* v_val_1403_; lean_object* v___x_1404_; 
lean_del_object(v___x_1401_);
v_val_1403_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v_a_1399_, 1);
v___x_1404_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1380_, v_a_1384_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1380_, v___x_1397_, v_a_1405_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1444_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1444_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1444_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
if (lean_obj_tag(v_a_1407_) == 1)
{
lean_del_object(v___x_1409_);
if (v_eqTrue_1382_ == 0)
{
lean_object* v_val_1411_; lean_object* v___x_1412_; 
v_val_1411_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_a_1407_, 1);
v___x_1412_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; uint8_t v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = lean_unbox(v_a_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v_a_1413_);
lean_dec(v_val_1411_);
lean_dec(v_val_1403_);
lean_inc(v_a_1383_);
v___f_1415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1415_, 0, v_a_1383_);
lean_closure_set(v___f_1415_, 1, v_e_1378_);
v___x_1416_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1417_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1416_, v___f_1415_, v_a_1384_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___y_1421_; 
lean_inc(v_val_1403_);
lean_inc(v_val_1411_);
v___x_1418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_val_1411_);
lean_ctor_set(v___x_1418_, 1, v_val_1403_);
v___x_1419_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1418_);
if (v_strict_1381_ == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_unbox(v_a_1413_);
lean_dec(v_a_1413_);
v___y_1421_ = v___x_1425_;
goto v___jp_1420_;
}
else
{
lean_dec(v_a_1413_);
v___y_1421_ = v_eqTrue_1382_;
goto v___jp_1420_;
}
v___jp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1422_, 0, v_e_1378_);
lean_ctor_set(v___x_1422_, 1, v_val_1403_);
lean_ctor_set(v___x_1422_, 2, v_val_1411_);
v___x_1423_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1423_, 0, v___x_1419_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*2, v___y_1421_);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1423_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_val_1411_);
lean_dec(v_val_1403_);
lean_dec_ref(v_e_1378_);
v_a_1426_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1412_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1412_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_val_1434_ = lean_ctor_get(v_a_1407_, 0);
lean_inc_n(v_val_1434_, 2);
lean_dec_ref_known(v_a_1407_, 1);
lean_inc(v_val_1403_);
v___x_1435_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_val_1403_);
lean_ctor_set(v___x_1435_, 1, v_val_1434_);
v___x_1436_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1437_, 0, v_e_1378_);
lean_ctor_set(v___x_1437_, 1, v_val_1403_);
lean_ctor_set(v___x_1437_, 2, v_val_1434_);
v___x_1438_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*2, v_strict_1381_);
v___x_1439_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1438_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1439_;
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec(v_a_1407_);
lean_dec(v_val_1403_);
lean_dec_ref(v_e_1378_);
v___x_1440_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1440_);
v___x_1442_ = v___x_1409_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
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
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_val_1403_);
lean_dec_ref(v_e_1378_);
v_a_1445_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1406_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1406_);
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
lean_dec(v_val_1403_);
lean_dec_ref(v_rhs_1380_);
lean_dec_ref(v_e_1378_);
v_a_1453_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1404_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1404_);
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
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec(v_a_1399_);
lean_dec_ref(v_rhs_1380_);
lean_dec_ref(v_e_1378_);
v___x_1461_ = lean_box(0);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1461_);
v___x_1463_ = v___x_1401_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
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
lean_dec_ref(v_rhs_1380_);
lean_dec_ref(v_e_1378_);
v_a_1466_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1398_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1398_);
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
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_rhs_1380_);
lean_dec_ref(v_lhs_1379_);
lean_dec_ref(v_e_1378_);
v_a_1474_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1395_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1395_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1482_ = _args[0];
lean_object* v_lhs_1483_ = _args[1];
lean_object* v_rhs_1484_ = _args[2];
lean_object* v_strict_1485_ = _args[3];
lean_object* v_eqTrue_1486_ = _args[4];
lean_object* v_a_1487_ = _args[5];
lean_object* v_a_1488_ = _args[6];
lean_object* v_a_1489_ = _args[7];
lean_object* v_a_1490_ = _args[8];
lean_object* v_a_1491_ = _args[9];
lean_object* v_a_1492_ = _args[10];
lean_object* v_a_1493_ = _args[11];
lean_object* v_a_1494_ = _args[12];
lean_object* v_a_1495_ = _args[13];
lean_object* v_a_1496_ = _args[14];
lean_object* v_a_1497_ = _args[15];
lean_object* v_a_1498_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1499_; uint8_t v_eqTrue_boxed_1500_; lean_object* v_res_1501_; 
v_strict_boxed_1499_ = lean_unbox(v_strict_1485_);
v_eqTrue_boxed_1500_ = lean_unbox(v_eqTrue_1486_);
v_res_1501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1482_, v_lhs_1483_, v_rhs_1484_, v_strict_boxed_1499_, v_eqTrue_boxed_1500_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1502_, lean_object* v_lhs_1503_, lean_object* v_rhs_1504_, uint8_t v_strict_1505_, uint8_t v_eqTrue_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
lean_inc_ref(v_lhs_1503_);
v___x_1521_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1503_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_fst_1523_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_fst_1523_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_fst_1523_);
lean_dec(v_a_1522_);
lean_inc_ref(v_rhs_1504_);
v___x_1524_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1504_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_fst_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1609_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_fst_1526_ = lean_ctor_get(v_a_1525_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_a_1525_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_a_1525_, 1);
lean_dec(v_unused_1610_);
v___x_1528_ = v_a_1525_;
v_isShared_1529_ = v_isSharedCheck_1609_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_fst_1526_);
lean_dec(v_a_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1609_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1503_, v_a_1508_);
lean_dec_ref(v_lhs_1503_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_id_1532_; lean_object* v_structId_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_id_1532_ = lean_ctor_get(v_a_1520_, 0);
lean_inc(v_id_1532_);
v_structId_1533_ = lean_ctor_get(v_a_1520_, 1);
lean_inc(v_structId_1533_);
lean_dec(v_a_1520_);
v___x_1534_ = 0;
v___x_1535_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1523_, v___x_1534_, v_a_1531_, v_structId_1533_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1592_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1592_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1592_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
if (lean_obj_tag(v_a_1536_) == 1)
{
lean_object* v_val_1540_; lean_object* v___x_1541_; 
lean_del_object(v___x_1538_);
v_val_1540_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v_a_1536_, 1);
v___x_1541_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1504_, v_a_1508_);
lean_dec_ref(v_rhs_1504_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1526_, v___x_1534_, v_a_1542_, v_structId_1533_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1571_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1571_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1571_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
if (lean_obj_tag(v_a_1544_) == 1)
{
lean_del_object(v___x_1546_);
if (v_eqTrue_1506_ == 0)
{
lean_object* v_val_1548_; lean_object* v___x_1550_; 
v_val_1548_ = lean_ctor_get(v_a_1544_, 0);
lean_inc_n(v_val_1548_, 2);
lean_dec_ref_known(v_a_1544_, 1);
lean_inc(v_val_1540_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 3);
lean_ctor_set(v___x_1528_, 1, v_val_1540_);
lean_ctor_set(v___x_1528_, 0, v_val_1548_);
v___x_1550_ = v___x_1528_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_val_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_val_1540_);
v___x_1550_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; uint8_t v___y_1553_; 
v___x_1551_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1550_);
if (v_strict_1505_ == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = 1;
v___y_1553_ = v___x_1557_;
goto v___jp_1552_;
}
else
{
v___y_1553_ = v_eqTrue_1506_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1554_, 0, v_e_1502_);
lean_ctor_set(v___x_1554_, 1, v_id_1532_);
lean_ctor_set(v___x_1554_, 2, v_val_1540_);
lean_ctor_set(v___x_1554_, 3, v_val_1548_);
v___x_1555_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*2, v___y_1553_);
v___x_1556_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1555_, v_structId_1533_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_structId_1533_);
return v___x_1556_;
}
}
}
else
{
lean_object* v_val_1559_; lean_object* v___x_1561_; 
v_val_1559_ = lean_ctor_get(v_a_1544_, 0);
lean_inc_n(v_val_1559_, 2);
lean_dec_ref_known(v_a_1544_, 1);
lean_inc(v_val_1540_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 3);
lean_ctor_set(v___x_1528_, 1, v_val_1559_);
lean_ctor_set(v___x_1528_, 0, v_val_1540_);
v___x_1561_ = v___x_1528_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1540_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_val_1559_);
v___x_1561_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1561_);
v___x_1563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1563_, 0, v_e_1502_);
lean_ctor_set(v___x_1563_, 1, v_id_1532_);
lean_ctor_set(v___x_1563_, 2, v_val_1540_);
lean_ctor_set(v___x_1563_, 3, v_val_1559_);
v___x_1564_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_ctor_set_uint8(v___x_1564_, sizeof(void*)*2, v_strict_1505_);
v___x_1565_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1564_, v_structId_1533_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_structId_1533_);
return v___x_1565_;
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec(v_a_1544_);
lean_dec(v_val_1540_);
lean_dec(v_structId_1533_);
lean_dec(v_id_1532_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_e_1502_);
v___x_1567_ = lean_box(0);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1567_);
v___x_1569_ = v___x_1546_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_val_1540_);
lean_dec(v_structId_1533_);
lean_dec(v_id_1532_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_e_1502_);
v_a_1572_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1543_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1543_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_val_1540_);
lean_dec(v_structId_1533_);
lean_dec(v_id_1532_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1526_);
lean_dec_ref(v_e_1502_);
v_a_1580_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1541_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1541_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec(v_a_1536_);
lean_dec(v_structId_1533_);
lean_dec(v_id_1532_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1526_);
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_e_1502_);
v___x_1588_ = lean_box(0);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1588_);
v___x_1590_ = v___x_1538_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_structId_1533_);
lean_dec(v_id_1532_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1526_);
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_e_1502_);
v_a_1593_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1535_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1535_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_del_object(v___x_1528_);
lean_dec(v_fst_1526_);
lean_dec(v_fst_1523_);
lean_dec(v_a_1520_);
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_e_1502_);
v_a_1601_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1530_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1530_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_fst_1523_);
lean_dec(v_a_1520_);
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_lhs_1503_);
lean_dec_ref(v_e_1502_);
v_a_1611_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1524_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1524_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_lhs_1503_);
lean_dec_ref(v_e_1502_);
v_a_1619_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1521_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1521_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_rhs_1504_);
lean_dec_ref(v_lhs_1503_);
lean_dec_ref(v_e_1502_);
v_a_1627_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1519_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1519_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1635_ = _args[0];
lean_object* v_lhs_1636_ = _args[1];
lean_object* v_rhs_1637_ = _args[2];
lean_object* v_strict_1638_ = _args[3];
lean_object* v_eqTrue_1639_ = _args[4];
lean_object* v_a_1640_ = _args[5];
lean_object* v_a_1641_ = _args[6];
lean_object* v_a_1642_ = _args[7];
lean_object* v_a_1643_ = _args[8];
lean_object* v_a_1644_ = _args[9];
lean_object* v_a_1645_ = _args[10];
lean_object* v_a_1646_ = _args[11];
lean_object* v_a_1647_ = _args[12];
lean_object* v_a_1648_ = _args[13];
lean_object* v_a_1649_ = _args[14];
lean_object* v_a_1650_ = _args[15];
lean_object* v_a_1651_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1652_; uint8_t v_eqTrue_boxed_1653_; lean_object* v_res_1654_; 
v_strict_boxed_1652_ = lean_unbox(v_strict_1638_);
v_eqTrue_boxed_1653_ = lean_unbox(v_eqTrue_1639_);
v_res_1654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1635_, v_lhs_1636_, v_rhs_1637_, v_strict_boxed_1652_, v_eqTrue_boxed_1653_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
return v_res_1654_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
if (lean_obj_tag(v_x_1656_) == 0)
{
uint8_t v___x_1657_; 
v___x_1657_ = 1;
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = 0;
return v___x_1658_;
}
}
else
{
if (lean_obj_tag(v_x_1656_) == 0)
{
uint8_t v___x_1659_; 
v___x_1659_ = 0;
return v___x_1659_;
}
else
{
lean_object* v_val_1660_; lean_object* v_val_1661_; uint8_t v___x_1662_; 
v_val_1660_ = lean_ctor_get(v_x_1655_, 0);
v_val_1661_ = lean_ctor_get(v_x_1656_, 0);
v___x_1662_ = lean_expr_eqv(v_val_1660_, v_val_1661_);
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1663_, v_x_1664_);
lean_dec(v_x_1664_);
lean_dec(v_x_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1667_, uint8_t v_eqTrue_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1671_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1892_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1892_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1892_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint8_t v_linarith_1685_; 
v_linarith_1685_ = lean_ctor_get_uint8(v_a_1681_, sizeof(void*)*13 + 22);
lean_dec(v_a_1681_);
if (v_linarith_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_dec_ref(v_e_1667_);
v___x_1686_ = lean_box(0);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = l_Lean_Expr_getAppNumArgs(v_e_1667_);
v___x_1691_ = lean_unsigned_to_nat(4u);
v___x_1692_ = lean_nat_dec_eq(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_dec(v___x_1690_);
lean_dec_ref(v_e_1667_);
v___x_1693_ = lean_box(0);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1693_);
v___x_1695_ = v___x_1683_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_sub(v___x_1690_, v___x_1697_);
lean_inc(v___x_1698_);
v___x_1699_ = l_Lean_Expr_getRevArg_x21(v_e_1667_, v___x_1698_);
lean_inc_ref(v___x_1699_);
v___x_1700_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1699_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1883_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1883_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1883_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v_strict_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; 
v___x_1705_ = lean_nat_sub(v___x_1698_, v___x_1697_);
lean_dec(v___x_1698_);
v___x_1706_ = l_Lean_Expr_getRevArg_x21(v_e_1667_, v___x_1705_);
v___x_1707_ = lean_unsigned_to_nat(2u);
v___x_1708_ = lean_nat_sub(v___x_1690_, v___x_1707_);
v___x_1709_ = lean_nat_sub(v___x_1708_, v___x_1697_);
lean_dec(v___x_1708_);
v___x_1710_ = l_Lean_Expr_getRevArg_x21(v_e_1667_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(3u);
v___x_1712_ = lean_nat_sub(v___x_1690_, v___x_1711_);
lean_dec(v___x_1690_);
v___x_1713_ = lean_nat_sub(v___x_1712_, v___x_1697_);
lean_dec(v___x_1712_);
v___x_1714_ = l_Lean_Expr_getRevArg_x21(v_e_1667_, v___x_1713_);
if (lean_obj_tag(v_a_1701_) == 1)
{
lean_object* v_val_1741_; lean_object* v___x_1742_; 
lean_del_object(v___x_1703_);
lean_dec_ref(v___x_1699_);
lean_del_object(v___x_1683_);
v_val_1741_ = lean_ctor_get(v_a_1701_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v_a_1701_, 1);
v___x_1742_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1741_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1756_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1756_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1756_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_leFn_x3f_1747_; lean_object* v_ltFn_x3f_1748_; uint8_t v___x_1749_; 
v_leFn_x3f_1747_ = lean_ctor_get(v_a_1743_, 20);
lean_inc(v_leFn_x3f_1747_);
v_ltFn_x3f_1748_ = lean_ctor_get(v_a_1743_, 21);
lean_inc(v_ltFn_x3f_1748_);
lean_dec(v_a_1743_);
v___x_1749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1747_, v___x_1706_);
lean_dec(v_leFn_x3f_1747_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
v___x_1750_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1748_, v___x_1706_);
lean_dec_ref(v___x_1706_);
lean_dec(v_ltFn_x3f_1748_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_dec(v_val_1741_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_e_1667_);
v___x_1751_ = lean_box(0);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1751_);
v___x_1753_ = v___x_1745_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
else
{
lean_del_object(v___x_1745_);
v_strict_1716_ = v___x_1692_;
v___y_1717_ = v_val_1741_;
v___y_1718_ = v_a_1669_;
v___y_1719_ = v_a_1670_;
v___y_1720_ = v_a_1671_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
goto v___jp_1715_;
}
}
else
{
uint8_t v___x_1755_; 
lean_dec(v_ltFn_x3f_1748_);
lean_del_object(v___x_1745_);
lean_dec_ref(v___x_1706_);
v___x_1755_ = 0;
v_strict_1716_ = v___x_1755_;
v___y_1717_ = v_val_1741_;
v___y_1718_ = v_a_1669_;
v___y_1719_ = v_a_1670_;
v___y_1720_ = v_a_1671_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_val_1741_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_dec_ref(v_e_1667_);
v_a_1757_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1742_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1742_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v___x_1765_; 
lean_dec(v_a_1701_);
v___x_1765_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1699_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1874_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1874_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1874_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1869_; 
v_val_1770_ = lean_ctor_get(v_a_1766_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1772_ = v_a_1766_;
v_isShared_1773_ = v_isSharedCheck_1869_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_val_1770_);
lean_dec(v_a_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1869_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1770_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1860_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1860_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1860_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_leInst_x3f_1784_; lean_object* v_ltInst_x3f_1785_; lean_object* v_lawfulOrderLTInst_x3f_1786_; lean_object* v_isPreorderInst_x3f_1787_; lean_object* v_orderedAddInst_x3f_1788_; lean_object* v_isLinearInst_x3f_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; uint8_t v___y_1825_; uint8_t v_strict_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; uint8_t v___y_1843_; uint8_t v___y_1854_; uint8_t v___y_1856_; uint8_t v___y_1858_; 
v_leInst_x3f_1784_ = lean_ctor_get(v_a_1775_, 5);
lean_inc(v_leInst_x3f_1784_);
v_ltInst_x3f_1785_ = lean_ctor_get(v_a_1775_, 6);
lean_inc(v_ltInst_x3f_1785_);
v_lawfulOrderLTInst_x3f_1786_ = lean_ctor_get(v_a_1775_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1786_);
v_isPreorderInst_x3f_1787_ = lean_ctor_get(v_a_1775_, 8);
lean_inc(v_isPreorderInst_x3f_1787_);
v_orderedAddInst_x3f_1788_ = lean_ctor_get(v_a_1775_, 9);
lean_inc(v_orderedAddInst_x3f_1788_);
v_isLinearInst_x3f_1789_ = lean_ctor_get(v_a_1775_, 10);
lean_inc(v_isLinearInst_x3f_1789_);
lean_dec(v_a_1775_);
if (lean_obj_tag(v_leInst_x3f_1784_) == 0)
{
if (v___x_1692_ == 0)
{
v___y_1858_ = v___x_1692_;
goto v___jp_1857_;
}
else
{
lean_dec(v_isPreorderInst_x3f_1787_);
v___y_1856_ = v___x_1692_;
goto v___jp_1855_;
}
}
else
{
uint8_t v___x_1859_; 
v___x_1859_ = 0;
v___y_1858_ = v___x_1859_;
goto v___jp_1857_;
}
v___jp_1779_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1780_);
v___x_1782_ = v___x_1777_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
v___jp_1790_:
{
if (v___y_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec(v_isLinearInst_x3f_1789_);
lean_del_object(v___x_1768_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1667_, v___x_1710_, v___x_1714_, v___y_1800_, v_eqTrue_1668_, v___y_1802_, v___y_1795_, v___y_1796_, v___y_1792_, v___y_1797_, v___y_1794_, v___y_1801_, v___y_1799_, v___y_1793_, v___y_1798_, v___y_1791_);
lean_dec(v___y_1802_);
return v___x_1804_;
}
else
{
if (lean_obj_tag(v_isLinearInst_x3f_1789_) == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
lean_dec(v___y_1802_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_e_1667_);
v___x_1805_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1805_);
v___x_1807_ = v___x_1768_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
else
{
lean_object* v___x_1809_; 
lean_dec_ref_known(v_isLinearInst_x3f_1789_, 1);
lean_del_object(v___x_1768_);
v___x_1809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1667_, v___x_1710_, v___x_1714_, v___y_1800_, v_eqTrue_1668_, v___y_1802_, v___y_1795_, v___y_1796_, v___y_1792_, v___y_1797_, v___y_1794_, v___y_1801_, v___y_1799_, v___y_1793_, v___y_1798_, v___y_1791_);
lean_dec(v___y_1802_);
return v___x_1809_;
}
}
}
v___jp_1810_:
{
if (v_eqTrue_1668_ == 0)
{
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
v___y_1803_ = v___x_1692_;
goto v___jp_1790_;
}
else
{
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
v___y_1803_ = v___y_1823_;
goto v___jp_1790_;
}
}
v___jp_1824_:
{
if (v_strict_1826_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_del_object(v___x_1703_);
v___y_1811_ = v___y_1837_;
v___y_1812_ = v___y_1830_;
v___y_1813_ = v___y_1835_;
v___y_1814_ = v___y_1832_;
v___y_1815_ = v___y_1828_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1836_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v_strict_1826_;
v___y_1821_ = v___y_1833_;
v___y_1822_ = v___y_1827_;
v___y_1823_ = v_strict_1826_;
goto v___jp_1810_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1786_) == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_dec(v___y_1827_);
lean_dec(v_isLinearInst_x3f_1789_);
lean_del_object(v___x_1768_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_e_1667_);
v___x_1838_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1838_);
v___x_1840_ = v___x_1703_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1786_, 1);
lean_del_object(v___x_1703_);
v___y_1811_ = v___y_1837_;
v___y_1812_ = v___y_1830_;
v___y_1813_ = v___y_1835_;
v___y_1814_ = v___y_1832_;
v___y_1815_ = v___y_1828_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1836_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v_strict_1826_;
v___y_1821_ = v___y_1833_;
v___y_1822_ = v___y_1827_;
v___y_1823_ = v___y_1825_;
goto v___jp_1810_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1706_);
v___x_1845_ = v___x_1772_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1706_);
v___x_1845_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1845_, v_leInst_x3f_1784_);
lean_dec(v_leInst_x3f_1784_);
if (v___x_1846_ == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1845_, v_ltInst_x3f_1785_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec_ref(v___x_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_val_1770_);
lean_del_object(v___x_1768_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1703_);
lean_dec_ref(v_e_1667_);
v___x_1848_ = lean_box(0);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1848_);
v___x_1850_ = v___x_1683_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
lean_del_object(v___x_1683_);
v___y_1825_ = v___y_1843_;
v_strict_1826_ = v___x_1692_;
v___y_1827_ = v_val_1770_;
v___y_1828_ = v_a_1669_;
v___y_1829_ = v_a_1670_;
v___y_1830_ = v_a_1671_;
v___y_1831_ = v_a_1672_;
v___y_1832_ = v_a_1673_;
v___y_1833_ = v_a_1674_;
v___y_1834_ = v_a_1675_;
v___y_1835_ = v_a_1676_;
v___y_1836_ = v_a_1677_;
v___y_1837_ = v_a_1678_;
goto v___jp_1824_;
}
}
else
{
lean_dec_ref(v___x_1845_);
lean_dec(v_ltInst_x3f_1785_);
lean_del_object(v___x_1683_);
v___y_1825_ = v___y_1843_;
v_strict_1826_ = v___y_1843_;
v___y_1827_ = v_val_1770_;
v___y_1828_ = v_a_1669_;
v___y_1829_ = v_a_1670_;
v___y_1830_ = v_a_1671_;
v___y_1831_ = v_a_1672_;
v___y_1832_ = v_a_1673_;
v___y_1833_ = v_a_1674_;
v___y_1834_ = v_a_1675_;
v___y_1835_ = v_a_1676_;
v___y_1836_ = v_a_1677_;
v___y_1837_ = v_a_1678_;
goto v___jp_1824_;
}
}
}
v___jp_1853_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1788_) == 0)
{
if (v___x_1692_ == 0)
{
lean_del_object(v___x_1777_);
v___y_1843_ = v___x_1692_;
goto v___jp_1842_;
}
else
{
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec(v_leInst_x3f_1784_);
lean_del_object(v___x_1772_);
lean_dec(v_val_1770_);
lean_del_object(v___x_1768_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_del_object(v___x_1703_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
goto v___jp_1779_;
}
}
else
{
lean_dec_ref_known(v_orderedAddInst_x3f_1788_, 1);
lean_del_object(v___x_1777_);
v___y_1843_ = v___y_1854_;
goto v___jp_1842_;
}
}
v___jp_1855_:
{
if (v___y_1856_ == 0)
{
v___y_1854_ = v___y_1856_;
goto v___jp_1853_;
}
else
{
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_orderedAddInst_x3f_1788_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec(v_leInst_x3f_1784_);
lean_del_object(v___x_1772_);
lean_dec(v_val_1770_);
lean_del_object(v___x_1768_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_del_object(v___x_1703_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
goto v___jp_1779_;
}
}
v___jp_1857_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_1787_) == 0)
{
v___y_1856_ = v___x_1692_;
goto v___jp_1855_;
}
else
{
lean_dec_ref_known(v_isPreorderInst_x3f_1787_, 1);
v___y_1854_ = v___y_1858_;
goto v___jp_1853_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1772_);
lean_dec(v_val_1770_);
lean_del_object(v___x_1768_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_del_object(v___x_1703_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
v_a_1861_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1774_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1774_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v_a_1766_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_del_object(v___x_1703_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
v___x_1870_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1870_);
v___x_1872_ = v___x_1768_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v___x_1706_);
lean_del_object(v___x_1703_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
v_a_1875_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1765_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1765_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
v___jp_1715_:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; uint8_t v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = lean_unbox(v_a_1729_);
lean_dec(v_a_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1667_, v___x_1710_, v___x_1714_, v_strict_1716_, v_eqTrue_1668_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1717_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1667_, v___x_1710_, v___x_1714_, v_strict_1716_, v_eqTrue_1668_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1717_);
return v___x_1732_;
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v___y_1717_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_e_1667_);
v_a_1733_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1728_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1728_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___x_1699_);
lean_dec(v___x_1698_);
lean_dec(v___x_1690_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_e_1667_);
v_a_1884_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1700_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1700_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_e_1667_);
v_a_1893_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1680_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1680_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1901_, lean_object* v_eqTrue_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
uint8_t v_eqTrue_boxed_1914_; lean_object* v_res_1915_; 
v_eqTrue_boxed_1914_ = lean_unbox(v_eqTrue_1902_);
v_res_1915_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1901_, v_eqTrue_boxed_1914_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_a_1903_);
return v_res_1915_;
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
