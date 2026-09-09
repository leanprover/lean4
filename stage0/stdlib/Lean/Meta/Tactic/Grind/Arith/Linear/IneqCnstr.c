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
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
size_t v_x_69340__boxed_62_; size_t v_x_69341__boxed_63_; lean_object* v_res_64_; 
v_x_69340__boxed_62_ = lean_unbox_usize(v_x_60_);
lean_dec(v_x_60_);
v_x_69341__boxed_63_ = lean_unbox_usize(v_x_61_);
lean_dec(v_x_61_);
v_res_64_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_58_, v_x_59_, v_x_69340__boxed_62_, v_x_69341__boxed_63_);
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
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = l_Lean_instInhabitedExpr;
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0);
v___x_297_ = lean_int_dec_eq(v_k_281_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_318_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_318_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_318_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_318_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_vars_305_; lean_object* v_zsmulFn_306_; lean_object* v_size_307_; lean_object* v___x_308_; lean_object* v___y_310_; uint8_t v___x_315_; 
v_vars_305_ = lean_ctor_get(v_a_301_, 30);
lean_inc_ref(v_vars_305_);
lean_dec(v_a_301_);
v_zsmulFn_306_ = lean_ctor_get(v_a_299_, 23);
lean_inc_ref(v_zsmulFn_306_);
lean_dec(v_a_299_);
v_size_307_ = lean_ctor_get(v_vars_305_, 2);
v___x_308_ = l_Lean_mkIntLit(v_k_281_);
v___x_315_ = lean_nat_dec_lt(v_x_282_, v_size_307_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_vars_305_);
v___x_316_ = l_outOfBounds___redArg(v___x_295_);
v___y_310_ = v___x_316_;
goto v___jp_309_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_PersistentArray_get_x21___redArg(v___x_295_, v_vars_305_, v_x_282_);
lean_dec_ref(v_vars_305_);
v___y_310_ = v___x_317_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = l_Lean_mkAppB(v_zsmulFn_306_, v___x_308_, v___y_310_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_311_);
v___x_313_ = v___x_303_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_a_299_);
v_a_319_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_300_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_300_);
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
v_a_327_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_298_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_298_);
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
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_351_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_vars_340_; lean_object* v_size_341_; uint8_t v___x_342_; 
v_vars_340_ = lean_ctor_get(v_a_336_, 30);
lean_inc_ref(v_vars_340_);
lean_dec(v_a_336_);
v_size_341_ = lean_ctor_get(v_vars_340_, 2);
v___x_342_ = lean_nat_dec_lt(v_x_282_, v_size_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec_ref(v_vars_340_);
v___x_343_ = l_outOfBounds___redArg(v___x_295_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_343_);
v___x_345_ = v___x_338_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_PersistentArray_get_x21___redArg(v___x_295_, v_vars_340_, v_x_282_);
lean_dec_ref(v_vars_340_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_347_);
v___x_349_ = v___x_338_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_335_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_335_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_k_360_, lean_object* v_x_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_360_, v_x_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v_x_361_);
lean_dec(v_k_360_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(lean_object* v_p_375_, lean_object* v_acc_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
if (lean_obj_tag(v_p_375_) == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_acc_376_);
return v___x_389_;
}
else
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v_p_392_; lean_object* v___x_393_; 
v_k_390_ = lean_ctor_get(v_p_375_, 0);
v_v_391_ = lean_ctor_get(v_p_375_, 1);
v_p_392_ = lean_ctor_get(v_p_375_, 2);
v___x_393_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_390_, v_v_391_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v_addFn_397_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v_addFn_397_ = lean_ctor_get(v_a_394_, 22);
lean_inc_ref(v_addFn_397_);
lean_dec(v_a_394_);
v___x_398_ = l_Lean_mkAppB(v_addFn_397_, v_acc_376_, v_a_396_);
v_p_375_ = v_p_392_;
v_acc_376_ = v___x_398_;
goto _start;
}
else
{
lean_dec(v_a_394_);
lean_dec_ref(v_acc_376_);
return v___x_395_;
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_acc_376_);
v_a_400_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_393_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_393_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(lean_object* v_p_408_, lean_object* v_acc_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_408_, v_acc_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
lean_dec(v_p_408_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(lean_object* v_p_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
if (lean_obj_tag(v_p_423_) == 0)
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_zero_441_; lean_object* v___x_443_; 
v_zero_441_ = lean_ctor_get(v_a_437_, 17);
lean_inc_ref(v_zero_441_);
lean_dec(v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_zero_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_zero_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_436_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_436_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
else
{
lean_object* v_k_454_; lean_object* v_v_455_; lean_object* v_p_456_; lean_object* v___x_457_; 
v_k_454_ = lean_ctor_get(v_p_423_, 0);
v_v_455_ = lean_ctor_get(v_p_423_, 1);
v_p_456_ = lean_ctor_get(v_p_423_, 2);
v___x_457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_454_, v_v_455_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_456_, v_a_458_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_459_;
}
else
{
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_p_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v_p_460_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(lean_object* v_msgData_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v___x_482_; lean_object* v_toCold_483_; lean_object* v_mctx_484_; lean_object* v_lctx_485_; lean_object* v_options_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = lean_st_ref_get(v___y_476_);
v_toCold_483_ = lean_ctor_get(v___y_477_, 0);
v_mctx_484_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_mctx_484_);
lean_dec(v___x_482_);
v_lctx_485_ = lean_ctor_get(v___y_475_, 2);
v_options_486_ = lean_ctor_get(v_toCold_483_, 2);
lean_inc_ref(v_options_486_);
lean_inc_ref(v_lctx_485_);
v___x_487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_487_, 0, v_env_481_);
lean_ctor_set(v___x_487_, 1, v_mctx_484_);
lean_ctor_set(v___x_487_, 2, v_lctx_485_);
lean_ctor_set(v___x_487_, 3, v_options_486_);
v___x_488_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_msgData_474_);
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
v_ref_503_ = lean_ctor_get(v___y_500_, 2);
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
v_ref_737_ = lean_ctor_get(v___y_734_, 2);
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
v___x_774_ = lean_st_ref_put(v___y_735_, v___x_773_);
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
lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v_toCold_922_; lean_object* v_options_923_; lean_object* v_inheritedTraceOptions_924_; uint8_t v_hasTrace_925_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; 
v_toCold_922_ = lean_ctor_get(v_a_842_, 0);
v_options_923_ = lean_ctor_get(v_toCold_922_, 2);
v_inheritedTraceOptions_924_ = lean_ctor_get(v_toCold_922_, 11);
v_hasTrace_925_ = lean_ctor_get_uint8(v_options_923_, sizeof(void*)*1);
if (v_hasTrace_925_ == 0)
{
v___y_927_ = v_a_833_;
v___y_928_ = v_a_834_;
v___y_929_ = v_a_835_;
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
goto v___jp_926_;
}
else
{
lean_object* v_cls_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_cls_1001_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_1002_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_1003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_923_, v___x_1002_);
if (v___x_1003_ == 0)
{
v___y_927_ = v_a_833_;
v___y_928_ = v_a_834_;
v___y_929_ = v_a_835_;
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
goto v___jp_926_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = l_Lean_MessageData_ofExpr(v_a_1005_);
v___x_1007_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1001_, v___x_1006_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_dec_ref_known(v___x_1007_, 1);
v___y_927_ = v_a_833_;
v___y_928_ = v_a_834_;
v___y_929_ = v_a_835_;
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
goto v___jp_926_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_1007_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_c_832_);
v_a_1008_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1004_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1004_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
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
v___x_913_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; uint8_t v___x_915_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_915_ = lean_int_dec_lt(v___y_900_, v___x_914_);
lean_dec(v___y_900_);
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
v___y_863_ = v___y_899_;
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
lean_dec(v___y_899_);
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
v___y_863_ = v___y_899_;
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
lean_dec(v___y_899_);
lean_dec_ref(v_c_832_);
return v___x_921_;
}
}
}
else
{
lean_dec(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v_c_832_);
return v___x_913_;
}
}
v___jp_926_:
{
lean_object* v_p_938_; 
v_p_938_ = lean_ctor_get(v_c_832_, 0);
if (lean_obj_tag(v_p_938_) == 0)
{
uint8_t v_strict_939_; 
v_strict_939_ = lean_ctor_get_uint8(v_c_832_, sizeof(void*)*2);
if (v_strict_939_ == 0)
{
lean_object* v_toCold_940_; lean_object* v_options_941_; uint8_t v_hasTrace_942_; 
v_toCold_940_ = lean_ctor_get(v___y_936_, 0);
v_options_941_ = lean_ctor_get(v_toCold_940_, 2);
v_hasTrace_942_ = lean_ctor_get_uint8(v_options_941_, sizeof(void*)*1);
if (v_hasTrace_942_ == 0)
{
lean_dec_ref(v_c_832_);
goto v___jp_845_;
}
else
{
lean_object* v_inheritedTraceOptions_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_inheritedTraceOptions_943_ = lean_ctor_get(v_toCold_940_, 11);
v___x_944_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_945_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_943_, v_options_941_, v___x_945_);
if (v___x_946_ == 0)
{
lean_dec_ref(v_c_832_);
goto v___jp_845_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_c_832_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = l_Lean_MessageData_ofExpr(v_a_948_);
v___x_950_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_944_, v___x_949_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_950_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_947_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_947_);
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
}
}
else
{
lean_object* v_toCold_959_; lean_object* v_options_960_; uint8_t v_hasTrace_961_; 
v_toCold_959_ = lean_ctor_get(v___y_936_, 0);
v_options_960_ = lean_ctor_get(v_toCold_959_, 2);
v_hasTrace_961_ = lean_ctor_get_uint8(v_options_960_, sizeof(void*)*1);
if (v_hasTrace_961_ == 0)
{
v___y_849_ = v___y_927_;
v___y_850_ = v___y_928_;
v___y_851_ = v___y_929_;
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
goto v___jp_848_;
}
else
{
lean_object* v_inheritedTraceOptions_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_inheritedTraceOptions_962_ = lean_ctor_get(v_toCold_959_, 11);
v___x_963_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_964_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_962_, v_options_960_, v___x_964_);
if (v___x_965_ == 0)
{
v___y_849_ = v___y_927_;
v___y_850_ = v___y_928_;
v___y_851_ = v___y_929_;
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
goto v___jp_848_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_MessageData_ofExpr(v_a_967_);
v___x_969_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_963_, v___x_968_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_dec_ref_known(v___x_969_, 1);
v___y_849_ = v___y_927_;
v___y_850_ = v___y_928_;
v___y_851_ = v___y_929_;
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
goto v___jp_848_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_969_;
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_c_832_);
v_a_970_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_966_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_966_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
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
}
}
}
else
{
lean_object* v_toCold_978_; lean_object* v_options_979_; uint8_t v_hasTrace_980_; 
v_toCold_978_ = lean_ctor_get(v___y_936_, 0);
v_options_979_ = lean_ctor_get(v_toCold_978_, 2);
v_hasTrace_980_ = lean_ctor_get_uint8(v_options_979_, sizeof(void*)*1);
if (v_hasTrace_980_ == 0)
{
lean_object* v_k_981_; lean_object* v_v_982_; 
v_k_981_ = lean_ctor_get(v_p_938_, 0);
v_v_982_ = lean_ctor_get(v_p_938_, 1);
lean_inc_ref(v_p_938_);
lean_inc(v_k_981_);
lean_inc_n(v_v_982_, 2);
v___y_898_ = v_v_982_;
v___y_899_ = v_v_982_;
v___y_900_ = v_k_981_;
v___y_901_ = v_p_938_;
v___y_902_ = v___y_927_;
v___y_903_ = v___y_928_;
v___y_904_ = v___y_929_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
goto v___jp_897_;
}
else
{
lean_object* v_k_983_; lean_object* v_v_984_; lean_object* v_inheritedTraceOptions_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_k_983_ = lean_ctor_get(v_p_938_, 0);
v_v_984_ = lean_ctor_get(v_p_938_, 1);
v_inheritedTraceOptions_985_ = lean_ctor_get(v_toCold_978_, 11);
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_987_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_985_, v_options_979_, v___x_987_);
if (v___x_988_ == 0)
{
lean_inc_ref(v_p_938_);
lean_inc(v_k_983_);
lean_inc_n(v_v_984_, 2);
v___y_898_ = v_v_984_;
v___y_899_ = v_v_984_;
v___y_900_ = v_k_983_;
v___y_901_ = v_p_938_;
v___y_902_ = v___y_927_;
v___y_903_ = v___y_928_;
v___y_904_ = v___y_929_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
goto v___jp_897_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_832_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_MessageData_ofExpr(v_a_990_);
v___x_992_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_986_, v___x_991_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_dec_ref_known(v___x_992_, 1);
lean_inc_ref(v_p_938_);
lean_inc(v_k_983_);
lean_inc_n(v_v_984_, 2);
v___y_898_ = v_v_984_;
v___y_899_ = v_v_984_;
v___y_900_ = v_k_983_;
v___y_901_ = v_p_938_;
v___y_902_ = v___y_927_;
v___y_903_ = v___y_928_;
v___y_904_ = v___y_929_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
goto v___jp_897_;
}
else
{
lean_dec_ref(v_c_832_);
return v___x_992_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_c_832_);
v_a_993_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_989_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_989_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec(v_a_1017_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1030_, lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1030_, v_msg_1031_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1045_, lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1045_, v_msg_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1061_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1075_, v_msg_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1077_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1090_, lean_object* v_e_1091_, lean_object* v_s_1092_){
_start:
{
lean_object* v_structs_1093_; lean_object* v_typeIdOf_1094_; lean_object* v_exprToStructId_1095_; lean_object* v_exprToStructIdEntries_1096_; lean_object* v_forbiddenNatModules_1097_; lean_object* v_natStructs_1098_; lean_object* v_natTypeIdOf_1099_; lean_object* v_exprToNatStructId_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_structs_1093_ = lean_ctor_get(v_s_1092_, 0);
v_typeIdOf_1094_ = lean_ctor_get(v_s_1092_, 1);
v_exprToStructId_1095_ = lean_ctor_get(v_s_1092_, 2);
v_exprToStructIdEntries_1096_ = lean_ctor_get(v_s_1092_, 3);
v_forbiddenNatModules_1097_ = lean_ctor_get(v_s_1092_, 4);
v_natStructs_1098_ = lean_ctor_get(v_s_1092_, 5);
v_natTypeIdOf_1099_ = lean_ctor_get(v_s_1092_, 6);
v_exprToNatStructId_1100_ = lean_ctor_get(v_s_1092_, 7);
v___x_1101_ = lean_array_get_size(v_structs_1093_);
v___x_1102_ = lean_nat_dec_lt(v_a_1090_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v_e_1091_);
return v_s_1092_;
}
else
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1164_; 
lean_inc_ref(v_exprToNatStructId_1100_);
lean_inc_ref(v_natTypeIdOf_1099_);
lean_inc_ref(v_natStructs_1098_);
lean_inc_ref(v_forbiddenNatModules_1097_);
lean_inc_ref(v_exprToStructIdEntries_1096_);
lean_inc_ref(v_exprToStructId_1095_);
lean_inc_ref(v_typeIdOf_1094_);
lean_inc_ref(v_structs_1093_);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_s_1092_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1165_ = lean_ctor_get(v_s_1092_, 7);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_s_1092_, 6);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_s_1092_, 5);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_s_1092_, 4);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_s_1092_, 3);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_s_1092_, 2);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_s_1092_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_s_1092_, 0);
lean_dec(v_unused_1172_);
v___x_1104_ = v_s_1092_;
v_isShared_1105_ = v_isSharedCheck_1164_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_s_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1164_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_v_1106_; lean_object* v_id_1107_; lean_object* v_ringId_x3f_1108_; lean_object* v_type_1109_; lean_object* v_u_1110_; lean_object* v_intModuleInst_1111_; lean_object* v_leInst_x3f_1112_; lean_object* v_ltInst_x3f_1113_; lean_object* v_lawfulOrderLTInst_x3f_1114_; lean_object* v_isPreorderInst_x3f_1115_; lean_object* v_orderedAddInst_x3f_1116_; lean_object* v_isLinearInst_x3f_1117_; lean_object* v_noNatDivInst_x3f_1118_; lean_object* v_ringInst_x3f_1119_; lean_object* v_commRingInst_x3f_1120_; lean_object* v_orderedRingInst_x3f_1121_; lean_object* v_fieldInst_x3f_1122_; lean_object* v_charInst_x3f_1123_; lean_object* v_zero_1124_; lean_object* v_ofNatZero_1125_; lean_object* v_one_x3f_1126_; lean_object* v_leFn_x3f_1127_; lean_object* v_ltFn_x3f_1128_; lean_object* v_addFn_1129_; lean_object* v_zsmulFn_1130_; lean_object* v_nsmulFn_1131_; lean_object* v_zsmulFn_x3f_1132_; lean_object* v_nsmulFn_x3f_1133_; lean_object* v_homomulFn_x3f_1134_; lean_object* v_subFn_1135_; lean_object* v_negFn_1136_; lean_object* v_vars_1137_; lean_object* v_varMap_1138_; lean_object* v_lowers_1139_; lean_object* v_uppers_1140_; lean_object* v_diseqs_1141_; lean_object* v_assignment_1142_; uint8_t v_caseSplits_1143_; lean_object* v_conflict_x3f_1144_; lean_object* v_diseqSplits_1145_; lean_object* v_elimEqs_1146_; lean_object* v_elimStack_1147_; lean_object* v_occurs_1148_; lean_object* v_ignored_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1163_; 
v_v_1106_ = lean_array_fget(v_structs_1093_, v_a_1090_);
v_id_1107_ = lean_ctor_get(v_v_1106_, 0);
v_ringId_x3f_1108_ = lean_ctor_get(v_v_1106_, 1);
v_type_1109_ = lean_ctor_get(v_v_1106_, 2);
v_u_1110_ = lean_ctor_get(v_v_1106_, 3);
v_intModuleInst_1111_ = lean_ctor_get(v_v_1106_, 4);
v_leInst_x3f_1112_ = lean_ctor_get(v_v_1106_, 5);
v_ltInst_x3f_1113_ = lean_ctor_get(v_v_1106_, 6);
v_lawfulOrderLTInst_x3f_1114_ = lean_ctor_get(v_v_1106_, 7);
v_isPreorderInst_x3f_1115_ = lean_ctor_get(v_v_1106_, 8);
v_orderedAddInst_x3f_1116_ = lean_ctor_get(v_v_1106_, 9);
v_isLinearInst_x3f_1117_ = lean_ctor_get(v_v_1106_, 10);
v_noNatDivInst_x3f_1118_ = lean_ctor_get(v_v_1106_, 11);
v_ringInst_x3f_1119_ = lean_ctor_get(v_v_1106_, 12);
v_commRingInst_x3f_1120_ = lean_ctor_get(v_v_1106_, 13);
v_orderedRingInst_x3f_1121_ = lean_ctor_get(v_v_1106_, 14);
v_fieldInst_x3f_1122_ = lean_ctor_get(v_v_1106_, 15);
v_charInst_x3f_1123_ = lean_ctor_get(v_v_1106_, 16);
v_zero_1124_ = lean_ctor_get(v_v_1106_, 17);
v_ofNatZero_1125_ = lean_ctor_get(v_v_1106_, 18);
v_one_x3f_1126_ = lean_ctor_get(v_v_1106_, 19);
v_leFn_x3f_1127_ = lean_ctor_get(v_v_1106_, 20);
v_ltFn_x3f_1128_ = lean_ctor_get(v_v_1106_, 21);
v_addFn_1129_ = lean_ctor_get(v_v_1106_, 22);
v_zsmulFn_1130_ = lean_ctor_get(v_v_1106_, 23);
v_nsmulFn_1131_ = lean_ctor_get(v_v_1106_, 24);
v_zsmulFn_x3f_1132_ = lean_ctor_get(v_v_1106_, 25);
v_nsmulFn_x3f_1133_ = lean_ctor_get(v_v_1106_, 26);
v_homomulFn_x3f_1134_ = lean_ctor_get(v_v_1106_, 27);
v_subFn_1135_ = lean_ctor_get(v_v_1106_, 28);
v_negFn_1136_ = lean_ctor_get(v_v_1106_, 29);
v_vars_1137_ = lean_ctor_get(v_v_1106_, 30);
v_varMap_1138_ = lean_ctor_get(v_v_1106_, 31);
v_lowers_1139_ = lean_ctor_get(v_v_1106_, 32);
v_uppers_1140_ = lean_ctor_get(v_v_1106_, 33);
v_diseqs_1141_ = lean_ctor_get(v_v_1106_, 34);
v_assignment_1142_ = lean_ctor_get(v_v_1106_, 35);
v_caseSplits_1143_ = lean_ctor_get_uint8(v_v_1106_, sizeof(void*)*42);
v_conflict_x3f_1144_ = lean_ctor_get(v_v_1106_, 36);
v_diseqSplits_1145_ = lean_ctor_get(v_v_1106_, 37);
v_elimEqs_1146_ = lean_ctor_get(v_v_1106_, 38);
v_elimStack_1147_ = lean_ctor_get(v_v_1106_, 39);
v_occurs_1148_ = lean_ctor_get(v_v_1106_, 40);
v_ignored_1149_ = lean_ctor_get(v_v_1106_, 41);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_v_1106_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1151_ = v_v_1106_;
v_isShared_1152_ = v_isSharedCheck_1163_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_ignored_1149_);
lean_inc(v_occurs_1148_);
lean_inc(v_elimStack_1147_);
lean_inc(v_elimEqs_1146_);
lean_inc(v_diseqSplits_1145_);
lean_inc(v_conflict_x3f_1144_);
lean_inc(v_assignment_1142_);
lean_inc(v_diseqs_1141_);
lean_inc(v_uppers_1140_);
lean_inc(v_lowers_1139_);
lean_inc(v_varMap_1138_);
lean_inc(v_vars_1137_);
lean_inc(v_negFn_1136_);
lean_inc(v_subFn_1135_);
lean_inc(v_homomulFn_x3f_1134_);
lean_inc(v_nsmulFn_x3f_1133_);
lean_inc(v_zsmulFn_x3f_1132_);
lean_inc(v_nsmulFn_1131_);
lean_inc(v_zsmulFn_1130_);
lean_inc(v_addFn_1129_);
lean_inc(v_ltFn_x3f_1128_);
lean_inc(v_leFn_x3f_1127_);
lean_inc(v_one_x3f_1126_);
lean_inc(v_ofNatZero_1125_);
lean_inc(v_zero_1124_);
lean_inc(v_charInst_x3f_1123_);
lean_inc(v_fieldInst_x3f_1122_);
lean_inc(v_orderedRingInst_x3f_1121_);
lean_inc(v_commRingInst_x3f_1120_);
lean_inc(v_ringInst_x3f_1119_);
lean_inc(v_noNatDivInst_x3f_1118_);
lean_inc(v_isLinearInst_x3f_1117_);
lean_inc(v_orderedAddInst_x3f_1116_);
lean_inc(v_isPreorderInst_x3f_1115_);
lean_inc(v_lawfulOrderLTInst_x3f_1114_);
lean_inc(v_ltInst_x3f_1113_);
lean_inc(v_leInst_x3f_1112_);
lean_inc(v_intModuleInst_1111_);
lean_inc(v_u_1110_);
lean_inc(v_type_1109_);
lean_inc(v_ringId_x3f_1108_);
lean_inc(v_id_1107_);
lean_dec(v_v_1106_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1163_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v_xs_x27_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1153_ = lean_box(0);
v_xs_x27_1154_ = lean_array_fset(v_structs_1093_, v_a_1090_, v___x_1153_);
v___x_1155_ = l_Lean_PersistentArray_push___redArg(v_ignored_1149_, v_e_1091_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 41, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_id_1107_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_ringId_x3f_1108_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_type_1109_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_u_1110_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_intModuleInst_1111_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_leInst_x3f_1112_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_ltInst_x3f_1113_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_lawfulOrderLTInst_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_isPreorderInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_orderedAddInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1162_, 10, v_isLinearInst_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1162_, 11, v_noNatDivInst_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1162_, 12, v_ringInst_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1162_, 13, v_commRingInst_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1162_, 14, v_orderedRingInst_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1162_, 15, v_fieldInst_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1162_, 16, v_charInst_x3f_1123_);
lean_ctor_set(v_reuseFailAlloc_1162_, 17, v_zero_1124_);
lean_ctor_set(v_reuseFailAlloc_1162_, 18, v_ofNatZero_1125_);
lean_ctor_set(v_reuseFailAlloc_1162_, 19, v_one_x3f_1126_);
lean_ctor_set(v_reuseFailAlloc_1162_, 20, v_leFn_x3f_1127_);
lean_ctor_set(v_reuseFailAlloc_1162_, 21, v_ltFn_x3f_1128_);
lean_ctor_set(v_reuseFailAlloc_1162_, 22, v_addFn_1129_);
lean_ctor_set(v_reuseFailAlloc_1162_, 23, v_zsmulFn_1130_);
lean_ctor_set(v_reuseFailAlloc_1162_, 24, v_nsmulFn_1131_);
lean_ctor_set(v_reuseFailAlloc_1162_, 25, v_zsmulFn_x3f_1132_);
lean_ctor_set(v_reuseFailAlloc_1162_, 26, v_nsmulFn_x3f_1133_);
lean_ctor_set(v_reuseFailAlloc_1162_, 27, v_homomulFn_x3f_1134_);
lean_ctor_set(v_reuseFailAlloc_1162_, 28, v_subFn_1135_);
lean_ctor_set(v_reuseFailAlloc_1162_, 29, v_negFn_1136_);
lean_ctor_set(v_reuseFailAlloc_1162_, 30, v_vars_1137_);
lean_ctor_set(v_reuseFailAlloc_1162_, 31, v_varMap_1138_);
lean_ctor_set(v_reuseFailAlloc_1162_, 32, v_lowers_1139_);
lean_ctor_set(v_reuseFailAlloc_1162_, 33, v_uppers_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 34, v_diseqs_1141_);
lean_ctor_set(v_reuseFailAlloc_1162_, 35, v_assignment_1142_);
lean_ctor_set(v_reuseFailAlloc_1162_, 36, v_conflict_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1162_, 37, v_diseqSplits_1145_);
lean_ctor_set(v_reuseFailAlloc_1162_, 38, v_elimEqs_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 39, v_elimStack_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 40, v_occurs_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 41, v___x_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*42, v_caseSplits_1143_);
v___x_1157_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_array_fset(v_xs_x27_1154_, v_a_1090_, v___x_1157_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1158_);
v___x_1160_ = v___x_1104_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_typeIdOf_1094_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_exprToStructId_1095_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_exprToStructIdEntries_1096_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_forbiddenNatModules_1097_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_natStructs_1098_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_natTypeIdOf_1099_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v_exprToNatStructId_1100_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1173_, lean_object* v_e_1174_, lean_object* v_s_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1173_, v_e_1174_, v_s_1175_);
lean_dec(v_a_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1177_, lean_object* v_lhs_1178_, lean_object* v_rhs_1179_, uint8_t v_strict_1180_, uint8_t v_eqTrue_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1194_ = 0;
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_box(v___x_1194_);
v___x_1197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1197_, 0, v_lhs_1178_);
lean_closure_set(v___x_1197_, 1, v___x_1196_);
lean_closure_set(v___x_1197_, 2, v___x_1195_);
v___x_1198_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1197_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1353_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1353_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1353_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
if (lean_obj_tag(v_a_1199_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1201_);
v_val_1203_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v_a_1199_, 1);
v___x_1204_ = lean_box(v___x_1194_);
v___x_1205_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1205_, 0, v_rhs_1179_);
lean_closure_set(v___x_1205_, 1, v___x_1204_);
lean_closure_set(v___x_1205_, 2, v___x_1195_);
v___x_1206_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1205_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1340_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1340_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1340_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
if (lean_obj_tag(v_a_1207_) == 1)
{
lean_object* v_val_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1209_);
v_val_1211_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_a_1207_, 1);
v___x_1212_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1177_, v_a_1183_);
if (lean_obj_tag(v___x_1212_) == 0)
{
if (v_eqTrue_1181_ == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; uint8_t v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_unbox(v_a_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_a_1215_);
lean_dec(v_a_1213_);
lean_dec(v_val_1211_);
lean_dec(v_val_1203_);
lean_inc(v_a_1182_);
v___f_1217_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1217_, 0, v_a_1182_);
lean_closure_set(v___f_1217_, 1, v_e_1177_);
v___x_1218_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1219_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1218_, v___f_1217_, v_a_1183_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___y_1223_; 
lean_inc(v_val_1203_);
lean_inc(v_val_1211_);
v___x_1220_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_val_1211_);
lean_ctor_set(v___x_1220_, 1, v_val_1203_);
v___x_1221_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1220_);
if (v_strict_1180_ == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
v___y_1223_ = v___x_1270_;
goto v___jp_1222_;
}
else
{
lean_dec(v_a_1215_);
v___y_1223_ = v_eqTrue_1181_;
goto v___jp_1222_;
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1224_, 0, v_e_1177_);
lean_ctor_set(v___x_1224_, 1, v_val_1203_);
lean_ctor_set(v___x_1224_, 2, v_val_1211_);
v___x_1225_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1221_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*2, v___y_1223_);
v___x_1226_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1225_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_p_1228_; lean_object* v___x_1229_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_p_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_a_1213_);
lean_inc_ref(v_p_1228_);
v___x_1229_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1228_, v_a_1213_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1230_, v___x_1194_, v_a_1213_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1245_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1245_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1245_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
if (lean_obj_tag(v_a_1232_) == 1)
{
lean_object* v_val_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_del_object(v___x_1234_);
v_val_1236_ = lean_ctor_get(v_a_1232_, 0);
lean_inc_n(v_val_1236_, 2);
lean_dec_ref_known(v_a_1232_, 1);
v___x_1237_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1236_);
v___x_1238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1227_);
lean_ctor_set(v___x_1238_, 1, v_val_1236_);
v___x_1239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*2, v___y_1223_);
v___x_1240_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1239_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_dec(v_a_1232_);
lean_dec(v_a_1227_);
v___x_1241_ = lean_box(0);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1241_);
v___x_1243_ = v___x_1234_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_a_1227_);
v_a_1246_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1231_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1231_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1227_);
lean_dec(v_a_1213_);
v_a_1254_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1229_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1229_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_a_1213_);
v_a_1262_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1226_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1226_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_a_1213_);
lean_dec(v_val_1211_);
lean_dec(v_val_1203_);
lean_dec_ref(v_e_1177_);
v_a_1271_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1214_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1214_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_a_1279_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1212_, 1);
lean_inc(v_val_1211_);
lean_inc(v_val_1203_);
v___x_1280_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_val_1203_);
lean_ctor_set(v___x_1280_, 1, v_val_1211_);
v___x_1281_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1282_, 0, v_e_1177_);
lean_ctor_set(v___x_1282_, 1, v_val_1203_);
lean_ctor_set(v___x_1282_, 2, v_val_1211_);
v___x_1283_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*2, v_strict_1180_);
v___x_1284_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1283_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_p_1286_; lean_object* v___x_1287_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_p_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_a_1279_);
lean_inc_ref(v_p_1286_);
v___x_1287_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1286_, v_a_1279_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1288_, v___x_1194_, v_a_1279_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1303_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1303_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1303_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
if (lean_obj_tag(v_a_1290_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_del_object(v___x_1292_);
v_val_1294_ = lean_ctor_get(v_a_1290_, 0);
lean_inc_n(v_val_1294_, 2);
lean_dec_ref_known(v_a_1290_, 1);
v___x_1295_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1294_);
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_a_1285_);
lean_ctor_set(v___x_1296_, 1, v_val_1294_);
v___x_1297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*2, v_strict_1180_);
v___x_1298_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1297_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec(v_a_1290_);
lean_dec(v_a_1285_);
v___x_1299_ = lean_box(0);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1299_);
v___x_1301_ = v___x_1292_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1285_);
v_a_1304_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1289_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1289_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1285_);
lean_dec(v_a_1279_);
v_a_1312_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1287_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1287_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_a_1279_);
v_a_1320_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1284_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1284_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_val_1211_);
lean_dec(v_val_1203_);
lean_dec_ref(v_e_1177_);
v_a_1328_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1212_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1212_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
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
lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec(v_a_1207_);
lean_dec(v_val_1203_);
lean_dec_ref(v_e_1177_);
v___x_1336_ = lean_box(0);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1336_);
v___x_1338_ = v___x_1209_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_val_1203_);
lean_dec_ref(v_e_1177_);
v_a_1341_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1206_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1206_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
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
lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_dec(v_a_1199_);
lean_dec_ref(v_rhs_1179_);
lean_dec_ref(v_e_1177_);
v___x_1349_ = lean_box(0);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1349_);
v___x_1351_ = v___x_1201_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_rhs_1179_);
lean_dec_ref(v_e_1177_);
v_a_1354_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1198_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1198_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1362_ = _args[0];
lean_object* v_lhs_1363_ = _args[1];
lean_object* v_rhs_1364_ = _args[2];
lean_object* v_strict_1365_ = _args[3];
lean_object* v_eqTrue_1366_ = _args[4];
lean_object* v_a_1367_ = _args[5];
lean_object* v_a_1368_ = _args[6];
lean_object* v_a_1369_ = _args[7];
lean_object* v_a_1370_ = _args[8];
lean_object* v_a_1371_ = _args[9];
lean_object* v_a_1372_ = _args[10];
lean_object* v_a_1373_ = _args[11];
lean_object* v_a_1374_ = _args[12];
lean_object* v_a_1375_ = _args[13];
lean_object* v_a_1376_ = _args[14];
lean_object* v_a_1377_ = _args[15];
lean_object* v_a_1378_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1379_; uint8_t v_eqTrue_boxed_1380_; lean_object* v_res_1381_; 
v_strict_boxed_1379_ = lean_unbox(v_strict_1365_);
v_eqTrue_boxed_1380_ = lean_unbox(v_eqTrue_1366_);
v_res_1381_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1362_, v_lhs_1363_, v_rhs_1364_, v_strict_boxed_1379_, v_eqTrue_boxed_1380_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec(v_a_1367_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1382_, lean_object* v_lhs_1383_, lean_object* v_rhs_1384_, uint8_t v_strict_1385_, uint8_t v_eqTrue_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1383_, v_a_1388_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = 0;
v___x_1402_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1383_, v___x_1401_, v_a_1400_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1469_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1469_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1469_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
if (lean_obj_tag(v_a_1403_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1408_; 
lean_del_object(v___x_1405_);
v_val_1407_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v_a_1403_, 1);
v___x_1408_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1384_, v_a_1388_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1384_, v___x_1401_, v_a_1409_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1448_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1448_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1448_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
if (lean_obj_tag(v_a_1411_) == 1)
{
lean_del_object(v___x_1413_);
if (v_eqTrue_1386_ == 0)
{
lean_object* v_val_1415_; lean_object* v___x_1416_; 
v_val_1415_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v_a_1411_, 1);
v___x_1416_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = lean_unbox(v_a_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___f_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v_a_1417_);
lean_dec(v_val_1415_);
lean_dec(v_val_1407_);
lean_inc(v_a_1387_);
v___f_1419_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1419_, 0, v_a_1387_);
lean_closure_set(v___f_1419_, 1, v_e_1382_);
v___x_1420_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1420_, v___f_1419_, v_a_1388_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___y_1425_; 
lean_inc(v_val_1407_);
lean_inc(v_val_1415_);
v___x_1422_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_val_1415_);
lean_ctor_set(v___x_1422_, 1, v_val_1407_);
v___x_1423_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1422_);
if (v_strict_1385_ == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_unbox(v_a_1417_);
lean_dec(v_a_1417_);
v___y_1425_ = v___x_1429_;
goto v___jp_1424_;
}
else
{
lean_dec(v_a_1417_);
v___y_1425_ = v_eqTrue_1386_;
goto v___jp_1424_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1426_, 0, v_e_1382_);
lean_ctor_set(v___x_1426_, 1, v_val_1407_);
lean_ctor_set(v___x_1426_, 2, v_val_1415_);
v___x_1427_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1427_, 0, v___x_1423_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*2, v___y_1425_);
v___x_1428_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1427_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1428_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_val_1415_);
lean_dec(v_val_1407_);
lean_dec_ref(v_e_1382_);
v_a_1430_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1416_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1416_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_val_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_val_1438_ = lean_ctor_get(v_a_1411_, 0);
lean_inc_n(v_val_1438_, 2);
lean_dec_ref_known(v_a_1411_, 1);
lean_inc(v_val_1407_);
v___x_1439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_val_1407_);
lean_ctor_set(v___x_1439_, 1, v_val_1438_);
v___x_1440_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_e_1382_);
lean_ctor_set(v___x_1441_, 1, v_val_1407_);
lean_ctor_set(v___x_1441_, 2, v_val_1438_);
v___x_1442_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*2, v_strict_1385_);
v___x_1443_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1442_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1443_;
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec(v_a_1411_);
lean_dec(v_val_1407_);
lean_dec_ref(v_e_1382_);
v___x_1444_ = lean_box(0);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1444_);
v___x_1446_ = v___x_1413_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
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
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_val_1407_);
lean_dec_ref(v_e_1382_);
v_a_1449_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1410_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1410_);
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
lean_dec(v_val_1407_);
lean_dec_ref(v_rhs_1384_);
lean_dec_ref(v_e_1382_);
v_a_1457_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1408_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1408_);
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
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec(v_a_1403_);
lean_dec_ref(v_rhs_1384_);
lean_dec_ref(v_e_1382_);
v___x_1465_ = lean_box(0);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1465_);
v___x_1467_ = v___x_1405_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_rhs_1384_);
lean_dec_ref(v_e_1382_);
v_a_1470_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1402_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1402_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
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
lean_dec_ref(v_rhs_1384_);
lean_dec_ref(v_lhs_1383_);
lean_dec_ref(v_e_1382_);
v_a_1478_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1399_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1399_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1486_ = _args[0];
lean_object* v_lhs_1487_ = _args[1];
lean_object* v_rhs_1488_ = _args[2];
lean_object* v_strict_1489_ = _args[3];
lean_object* v_eqTrue_1490_ = _args[4];
lean_object* v_a_1491_ = _args[5];
lean_object* v_a_1492_ = _args[6];
lean_object* v_a_1493_ = _args[7];
lean_object* v_a_1494_ = _args[8];
lean_object* v_a_1495_ = _args[9];
lean_object* v_a_1496_ = _args[10];
lean_object* v_a_1497_ = _args[11];
lean_object* v_a_1498_ = _args[12];
lean_object* v_a_1499_ = _args[13];
lean_object* v_a_1500_ = _args[14];
lean_object* v_a_1501_ = _args[15];
lean_object* v_a_1502_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1503_; uint8_t v_eqTrue_boxed_1504_; lean_object* v_res_1505_; 
v_strict_boxed_1503_ = lean_unbox(v_strict_1489_);
v_eqTrue_boxed_1504_ = lean_unbox(v_eqTrue_1490_);
v_res_1505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1486_, v_lhs_1487_, v_rhs_1488_, v_strict_boxed_1503_, v_eqTrue_boxed_1504_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1506_, lean_object* v_lhs_1507_, lean_object* v_rhs_1508_, uint8_t v_strict_1509_, uint8_t v_eqTrue_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
lean_inc_ref(v_lhs_1507_);
v___x_1525_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1507_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v_fst_1527_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v_fst_1527_ = lean_ctor_get(v_a_1526_, 0);
lean_inc(v_fst_1527_);
lean_dec(v_a_1526_);
lean_inc_ref(v_rhs_1508_);
v___x_1528_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1508_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_fst_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1613_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_fst_1530_ = lean_ctor_get(v_a_1529_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_a_1529_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_a_1529_, 1);
lean_dec(v_unused_1614_);
v___x_1532_ = v_a_1529_;
v_isShared_1533_ = v_isSharedCheck_1613_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_fst_1530_);
lean_dec(v_a_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1613_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1507_, v_a_1512_);
lean_dec_ref(v_lhs_1507_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_id_1536_; lean_object* v_structId_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_id_1536_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_id_1536_);
v_structId_1537_ = lean_ctor_get(v_a_1524_, 1);
lean_inc(v_structId_1537_);
lean_dec(v_a_1524_);
v___x_1538_ = 0;
v___x_1539_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1527_, v___x_1538_, v_a_1535_, v_structId_1537_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1596_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1596_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1596_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
if (lean_obj_tag(v_a_1540_) == 1)
{
lean_object* v_val_1544_; lean_object* v___x_1545_; 
lean_del_object(v___x_1542_);
v_val_1544_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v_a_1540_, 1);
v___x_1545_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1508_, v_a_1512_);
lean_dec_ref(v_rhs_1508_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1530_, v___x_1538_, v_a_1546_, v_structId_1537_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1575_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1575_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1575_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
if (lean_obj_tag(v_a_1548_) == 1)
{
lean_del_object(v___x_1550_);
if (v_eqTrue_1510_ == 0)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; 
v_val_1552_ = lean_ctor_get(v_a_1548_, 0);
lean_inc_n(v_val_1552_, 2);
lean_dec_ref_known(v_a_1548_, 1);
lean_inc(v_val_1544_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
lean_ctor_set(v___x_1532_, 1, v_val_1544_);
lean_ctor_set(v___x_1532_, 0, v_val_1552_);
v___x_1554_ = v___x_1532_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_val_1552_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_val_1544_);
v___x_1554_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; uint8_t v___y_1557_; 
v___x_1555_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1554_);
if (v_strict_1509_ == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = 1;
v___y_1557_ = v___x_1561_;
goto v___jp_1556_;
}
else
{
v___y_1557_ = v_eqTrue_1510_;
goto v___jp_1556_;
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1558_, 0, v_e_1506_);
lean_ctor_set(v___x_1558_, 1, v_id_1536_);
lean_ctor_set(v___x_1558_, 2, v_val_1544_);
lean_ctor_set(v___x_1558_, 3, v_val_1552_);
v___x_1559_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1559_, 0, v___x_1555_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*2, v___y_1557_);
v___x_1560_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1559_, v_structId_1537_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_structId_1537_);
return v___x_1560_;
}
}
}
else
{
lean_object* v_val_1563_; lean_object* v___x_1565_; 
v_val_1563_ = lean_ctor_get(v_a_1548_, 0);
lean_inc_n(v_val_1563_, 2);
lean_dec_ref_known(v_a_1548_, 1);
lean_inc(v_val_1544_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
lean_ctor_set(v___x_1532_, 1, v_val_1563_);
lean_ctor_set(v___x_1532_, 0, v_val_1544_);
v___x_1565_ = v___x_1532_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_val_1544_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_val_1563_);
v___x_1565_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1566_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1567_, 0, v_e_1506_);
lean_ctor_set(v___x_1567_, 1, v_id_1536_);
lean_ctor_set(v___x_1567_, 2, v_val_1544_);
lean_ctor_set(v___x_1567_, 3, v_val_1563_);
v___x_1568_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*2, v_strict_1509_);
v___x_1569_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1568_, v_structId_1537_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_structId_1537_);
return v___x_1569_;
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec(v_a_1548_);
lean_dec(v_val_1544_);
lean_dec(v_structId_1537_);
lean_dec(v_id_1536_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_e_1506_);
v___x_1571_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1571_);
v___x_1573_ = v___x_1550_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_val_1544_);
lean_dec(v_structId_1537_);
lean_dec(v_id_1536_);
lean_del_object(v___x_1532_);
lean_dec_ref(v_e_1506_);
v_a_1576_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1547_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1547_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_val_1544_);
lean_dec(v_structId_1537_);
lean_dec(v_id_1536_);
lean_del_object(v___x_1532_);
lean_dec(v_fst_1530_);
lean_dec_ref(v_e_1506_);
v_a_1584_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1545_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1545_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
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
lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_dec(v_a_1540_);
lean_dec(v_structId_1537_);
lean_dec(v_id_1536_);
lean_del_object(v___x_1532_);
lean_dec(v_fst_1530_);
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_e_1506_);
v___x_1592_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1592_);
v___x_1594_ = v___x_1542_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_structId_1537_);
lean_dec(v_id_1536_);
lean_del_object(v___x_1532_);
lean_dec(v_fst_1530_);
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_e_1506_);
v_a_1597_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1539_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1539_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_del_object(v___x_1532_);
lean_dec(v_fst_1530_);
lean_dec(v_fst_1527_);
lean_dec(v_a_1524_);
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_e_1506_);
v_a_1605_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1534_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1534_);
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
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_fst_1527_);
lean_dec(v_a_1524_);
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_lhs_1507_);
lean_dec_ref(v_e_1506_);
v_a_1615_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1528_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1528_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_a_1524_);
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_lhs_1507_);
lean_dec_ref(v_e_1506_);
v_a_1623_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1525_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1525_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_rhs_1508_);
lean_dec_ref(v_lhs_1507_);
lean_dec_ref(v_e_1506_);
v_a_1631_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1523_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1523_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1639_ = _args[0];
lean_object* v_lhs_1640_ = _args[1];
lean_object* v_rhs_1641_ = _args[2];
lean_object* v_strict_1642_ = _args[3];
lean_object* v_eqTrue_1643_ = _args[4];
lean_object* v_a_1644_ = _args[5];
lean_object* v_a_1645_ = _args[6];
lean_object* v_a_1646_ = _args[7];
lean_object* v_a_1647_ = _args[8];
lean_object* v_a_1648_ = _args[9];
lean_object* v_a_1649_ = _args[10];
lean_object* v_a_1650_ = _args[11];
lean_object* v_a_1651_ = _args[12];
lean_object* v_a_1652_ = _args[13];
lean_object* v_a_1653_ = _args[14];
lean_object* v_a_1654_ = _args[15];
lean_object* v_a_1655_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1656_; uint8_t v_eqTrue_boxed_1657_; lean_object* v_res_1658_; 
v_strict_boxed_1656_ = lean_unbox(v_strict_1642_);
v_eqTrue_boxed_1657_ = lean_unbox(v_eqTrue_1643_);
v_res_1658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1639_, v_lhs_1640_, v_rhs_1641_, v_strict_boxed_1656_, v_eqTrue_boxed_1657_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
return v_res_1658_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
if (lean_obj_tag(v_x_1660_) == 0)
{
uint8_t v___x_1661_; 
v___x_1661_ = 1;
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = 0;
return v___x_1662_;
}
}
else
{
if (lean_obj_tag(v_x_1660_) == 0)
{
uint8_t v___x_1663_; 
v___x_1663_ = 0;
return v___x_1663_;
}
else
{
lean_object* v_val_1664_; lean_object* v_val_1665_; uint8_t v___x_1666_; 
v_val_1664_ = lean_ctor_get(v_x_1659_, 0);
v_val_1665_ = lean_ctor_get(v_x_1660_, 0);
v___x_1666_ = lean_expr_eqv(v_val_1664_, v_val_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1667_, v_x_1668_);
lean_dec(v_x_1668_);
lean_dec(v_x_1667_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1671_, uint8_t v_eqTrue_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1675_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1878_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1878_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1878_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
uint8_t v_linarith_1689_; 
v_linarith_1689_ = lean_ctor_get_uint8(v_a_1685_, sizeof(void*)*14 + 22);
lean_dec(v_a_1685_);
if (v_linarith_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
lean_dec_ref(v_e_1671_);
v___x_1690_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = l_Lean_Expr_getAppNumArgs(v_e_1671_);
v___x_1695_ = lean_unsigned_to_nat(4u);
v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec(v___x_1694_);
lean_dec_ref(v_e_1671_);
v___x_1697_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1697_);
v___x_1699_ = v___x_1687_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1687_);
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_nat_sub(v___x_1694_, v___x_1701_);
lean_inc(v___x_1702_);
v___x_1703_ = l_Lean_Expr_getRevArg_x21(v_e_1671_, v___x_1702_);
lean_inc_ref(v___x_1703_);
v___x_1704_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1703_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1869_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1869_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1869_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v_strict_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; 
v___x_1709_ = lean_nat_sub(v___x_1702_, v___x_1701_);
lean_dec(v___x_1702_);
v___x_1710_ = l_Lean_Expr_getRevArg_x21(v_e_1671_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(2u);
v___x_1712_ = lean_nat_sub(v___x_1694_, v___x_1711_);
v___x_1713_ = lean_nat_sub(v___x_1712_, v___x_1701_);
lean_dec(v___x_1712_);
v___x_1714_ = l_Lean_Expr_getRevArg_x21(v_e_1671_, v___x_1713_);
v___x_1715_ = lean_unsigned_to_nat(3u);
v___x_1716_ = lean_nat_sub(v___x_1694_, v___x_1715_);
lean_dec(v___x_1694_);
v___x_1717_ = lean_nat_sub(v___x_1716_, v___x_1701_);
lean_dec(v___x_1716_);
v___x_1718_ = l_Lean_Expr_getRevArg_x21(v_e_1671_, v___x_1717_);
if (lean_obj_tag(v_a_1705_) == 1)
{
lean_object* v_val_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1707_);
lean_dec_ref(v___x_1703_);
v_val_1745_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v_a_1705_, 1);
v___x_1746_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1745_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_leFn_x3f_1751_; lean_object* v_ltFn_x3f_1752_; uint8_t v___x_1753_; 
v_leFn_x3f_1751_ = lean_ctor_get(v_a_1747_, 20);
lean_inc(v_leFn_x3f_1751_);
v_ltFn_x3f_1752_ = lean_ctor_get(v_a_1747_, 21);
lean_inc(v_ltFn_x3f_1752_);
lean_dec(v_a_1747_);
v___x_1753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1751_, v___x_1710_);
lean_dec(v_leFn_x3f_1751_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1752_, v___x_1710_);
lean_dec_ref(v___x_1710_);
lean_dec(v_ltFn_x3f_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec(v_val_1745_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_e_1671_);
v___x_1755_ = lean_box(0);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1755_);
v___x_1757_ = v___x_1749_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_del_object(v___x_1749_);
v_strict_1720_ = v___x_1696_;
v___y_1721_ = v_val_1745_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
v___y_1728_ = v_a_1679_;
v___y_1729_ = v_a_1680_;
v___y_1730_ = v_a_1681_;
v___y_1731_ = v_a_1682_;
goto v___jp_1719_;
}
}
else
{
uint8_t v___x_1759_; 
lean_dec(v_ltFn_x3f_1752_);
lean_del_object(v___x_1749_);
lean_dec_ref(v___x_1710_);
v___x_1759_ = 0;
v_strict_1720_ = v___x_1759_;
v___y_1721_ = v_val_1745_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
v___y_1728_ = v_a_1679_;
v___y_1729_ = v_a_1680_;
v___y_1730_ = v_a_1681_;
v___y_1731_ = v_a_1682_;
goto v___jp_1719_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_val_1745_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_e_1671_);
v_a_1761_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1746_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1746_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v___x_1769_; 
lean_dec(v_a_1705_);
v___x_1769_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1703_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1860_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1860_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1860_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
if (lean_obj_tag(v_a_1770_) == 1)
{
lean_object* v_val_1774_; lean_object* v___x_1775_; 
v_val_1774_ = lean_ctor_get(v_a_1770_, 0);
lean_inc(v_val_1774_);
lean_dec_ref_known(v_a_1770_, 1);
v___x_1775_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1774_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1847_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1847_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1847_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_leInst_x3f_1785_; lean_object* v_ltInst_x3f_1786_; lean_object* v_lawfulOrderLTInst_x3f_1787_; lean_object* v_isPreorderInst_x3f_1788_; lean_object* v_orderedAddInst_x3f_1789_; lean_object* v_isLinearInst_x3f_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; uint8_t v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1825_; uint8_t v___y_1845_; 
v_leInst_x3f_1785_ = lean_ctor_get(v_a_1776_, 5);
lean_inc(v_leInst_x3f_1785_);
v_ltInst_x3f_1786_ = lean_ctor_get(v_a_1776_, 6);
lean_inc(v_ltInst_x3f_1786_);
v_lawfulOrderLTInst_x3f_1787_ = lean_ctor_get(v_a_1776_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1787_);
v_isPreorderInst_x3f_1788_ = lean_ctor_get(v_a_1776_, 8);
lean_inc(v_isPreorderInst_x3f_1788_);
v_orderedAddInst_x3f_1789_ = lean_ctor_get(v_a_1776_, 9);
lean_inc(v_orderedAddInst_x3f_1789_);
v_isLinearInst_x3f_1790_ = lean_ctor_get(v_a_1776_, 10);
lean_inc(v_isLinearInst_x3f_1790_);
lean_dec(v_a_1776_);
if (lean_obj_tag(v_leInst_x3f_1785_) == 0)
{
lean_dec(v_isPreorderInst_x3f_1788_);
v___y_1845_ = v___x_1696_;
goto v___jp_1844_;
}
else
{
if (lean_obj_tag(v_isPreorderInst_x3f_1788_) == 0)
{
v___y_1845_ = v___x_1696_;
goto v___jp_1844_;
}
else
{
uint8_t v___x_1846_; 
lean_dec_ref_known(v_isPreorderInst_x3f_1788_, 1);
v___x_1846_ = 0;
v___y_1825_ = v___x_1846_;
goto v___jp_1824_;
}
}
v___jp_1780_:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = lean_box(0);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
v___jp_1791_:
{
if (lean_obj_tag(v_isLinearInst_x3f_1790_) == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
lean_dec(v___y_1793_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_e_1671_);
v___x_1804_ = lean_box(0);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1804_);
v___x_1806_ = v___x_1772_;
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
lean_dec_ref_known(v_isLinearInst_x3f_1790_, 1);
lean_del_object(v___x_1772_);
v___x_1808_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1671_, v___x_1714_, v___x_1718_, v___y_1798_, v_eqTrue_1672_, v___y_1793_, v___y_1796_, v___y_1802_, v___y_1794_, v___y_1792_, v___y_1799_, v___y_1795_, v___y_1803_, v___y_1800_, v___y_1797_, v___y_1801_);
lean_dec(v___y_1793_);
return v___x_1808_;
}
}
v___jp_1809_:
{
if (v_eqTrue_1672_ == 0)
{
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___y_1813_;
v___y_1796_ = v___y_1814_;
v___y_1797_ = v___y_1815_;
v___y_1798_ = v___y_1816_;
v___y_1799_ = v___y_1817_;
v___y_1800_ = v___y_1818_;
v___y_1801_ = v___y_1819_;
v___y_1802_ = v___y_1820_;
v___y_1803_ = v___y_1821_;
goto v___jp_1791_;
}
else
{
if (v___y_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_dec(v_isLinearInst_x3f_1790_);
lean_del_object(v___x_1772_);
v___x_1823_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1671_, v___x_1714_, v___x_1718_, v___y_1816_, v_eqTrue_1672_, v___y_1811_, v___y_1814_, v___y_1820_, v___y_1812_, v___y_1810_, v___y_1817_, v___y_1813_, v___y_1821_, v___y_1818_, v___y_1815_, v___y_1819_);
lean_dec(v___y_1811_);
return v___x_1823_;
}
else
{
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___y_1813_;
v___y_1796_ = v___y_1814_;
v___y_1797_ = v___y_1815_;
v___y_1798_ = v___y_1816_;
v___y_1799_ = v___y_1817_;
v___y_1800_ = v___y_1818_;
v___y_1801_ = v___y_1819_;
v___y_1802_ = v___y_1820_;
v___y_1803_ = v___y_1821_;
goto v___jp_1791_;
}
}
}
v___jp_1824_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1789_) == 0)
{
lean_dec(v_isLinearInst_x3f_1790_);
lean_dec(v_lawfulOrderLTInst_x3f_1787_);
lean_dec(v_ltInst_x3f_1786_);
lean_dec(v_leInst_x3f_1785_);
lean_dec(v_val_1774_);
lean_del_object(v___x_1772_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1671_);
goto v___jp_1780_;
}
else
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1842_; 
lean_del_object(v___x_1778_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_orderedAddInst_x3f_1789_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_orderedAddInst_x3f_1789_, 0);
lean_dec(v_unused_1843_);
v___x_1827_ = v_orderedAddInst_x3f_1789_;
v_isShared_1828_ = v_isSharedCheck_1842_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v_orderedAddInst_x3f_1789_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1842_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1710_);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1710_);
v___x_1830_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1830_, v_leInst_x3f_1785_);
lean_dec(v_leInst_x3f_1785_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1830_, v_ltInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1786_);
lean_dec_ref(v___x_1830_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec(v_isLinearInst_x3f_1790_);
lean_dec(v_lawfulOrderLTInst_x3f_1787_);
lean_dec(v_val_1774_);
lean_del_object(v___x_1772_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_e_1671_);
v___x_1833_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1833_);
v___x_1835_ = v___x_1707_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
if (v___x_1696_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1787_);
lean_del_object(v___x_1707_);
v___y_1810_ = v_a_1676_;
v___y_1811_ = v_val_1774_;
v___y_1812_ = v_a_1675_;
v___y_1813_ = v_a_1678_;
v___y_1814_ = v_a_1673_;
v___y_1815_ = v_a_1681_;
v___y_1816_ = v___x_1696_;
v___y_1817_ = v_a_1677_;
v___y_1818_ = v_a_1680_;
v___y_1819_ = v_a_1682_;
v___y_1820_ = v_a_1674_;
v___y_1821_ = v_a_1679_;
v___y_1822_ = v___y_1825_;
goto v___jp_1809_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1787_) == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_isLinearInst_x3f_1790_);
lean_dec(v_val_1774_);
lean_del_object(v___x_1772_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_e_1671_);
v___x_1837_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1837_);
v___x_1839_ = v___x_1707_;
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
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1787_, 1);
lean_del_object(v___x_1707_);
v___y_1810_ = v_a_1676_;
v___y_1811_ = v_val_1774_;
v___y_1812_ = v_a_1675_;
v___y_1813_ = v_a_1678_;
v___y_1814_ = v_a_1673_;
v___y_1815_ = v_a_1681_;
v___y_1816_ = v___x_1696_;
v___y_1817_ = v_a_1677_;
v___y_1818_ = v_a_1680_;
v___y_1819_ = v_a_1682_;
v___y_1820_ = v_a_1674_;
v___y_1821_ = v_a_1679_;
v___y_1822_ = v___y_1825_;
goto v___jp_1809_;
}
}
}
}
else
{
lean_dec_ref(v___x_1830_);
lean_dec(v_lawfulOrderLTInst_x3f_1787_);
lean_dec(v_ltInst_x3f_1786_);
lean_del_object(v___x_1707_);
v___y_1810_ = v_a_1676_;
v___y_1811_ = v_val_1774_;
v___y_1812_ = v_a_1675_;
v___y_1813_ = v_a_1678_;
v___y_1814_ = v_a_1673_;
v___y_1815_ = v_a_1681_;
v___y_1816_ = v___y_1825_;
v___y_1817_ = v_a_1677_;
v___y_1818_ = v_a_1680_;
v___y_1819_ = v_a_1682_;
v___y_1820_ = v_a_1674_;
v___y_1821_ = v_a_1679_;
v___y_1822_ = v___y_1825_;
goto v___jp_1809_;
}
}
}
}
}
v___jp_1844_:
{
if (v___y_1845_ == 0)
{
v___y_1825_ = v___y_1845_;
goto v___jp_1824_;
}
else
{
lean_dec(v_isLinearInst_x3f_1790_);
lean_dec(v_orderedAddInst_x3f_1789_);
lean_dec(v_lawfulOrderLTInst_x3f_1787_);
lean_dec(v_ltInst_x3f_1786_);
lean_dec(v_leInst_x3f_1785_);
lean_dec(v_val_1774_);
lean_del_object(v___x_1772_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1671_);
goto v___jp_1780_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_val_1774_);
lean_del_object(v___x_1772_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1671_);
v_a_1848_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1775_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1775_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec(v_a_1770_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1671_);
v___x_1856_ = lean_box(0);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1856_);
v___x_1858_ = v___x_1772_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1671_);
v_a_1861_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1769_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1769_);
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
v___jp_1719_:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; uint8_t v___x_1734_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_unbox(v_a_1733_);
lean_dec(v_a_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1671_, v___x_1714_, v___x_1718_, v_strict_1720_, v_eqTrue_1672_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1721_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1671_, v___x_1714_, v___x_1718_, v_strict_1720_, v_eqTrue_1672_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1721_);
return v___x_1736_;
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v___y_1721_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_e_1671_);
v_a_1737_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1732_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1732_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v___x_1703_);
lean_dec(v___x_1702_);
lean_dec(v___x_1694_);
lean_dec_ref(v_e_1671_);
v_a_1870_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1704_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1704_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_e_1671_);
v_a_1879_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1684_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1684_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1887_, lean_object* v_eqTrue_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
uint8_t v_eqTrue_boxed_1900_; lean_object* v_res_1901_; 
v_eqTrue_boxed_1900_ = lean_unbox(v_eqTrue_1888_);
v_res_1901_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1887_, v_eqTrue_boxed_1900_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec(v_a_1889_);
return v_res_1901_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin) {
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
