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
size_t v_x_69240__boxed_62_; size_t v_x_69241__boxed_63_; lean_object* v_res_64_; 
v_x_69240__boxed_62_ = lean_unbox_usize(v_x_60_);
lean_dec(v_x_60_);
v_x_69241__boxed_63_ = lean_unbox_usize(v_x_61_);
lean_dec(v_x_61_);
v_res_64_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_58_, v_x_59_, v_x_69240__boxed_62_, v_x_69241__boxed_63_);
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
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v___x_482_; lean_object* v_mctx_483_; lean_object* v_lctx_484_; lean_object* v_options_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = lean_st_ref_get(v___y_476_);
v_mctx_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_mctx_483_);
lean_dec(v___x_482_);
v_lctx_484_ = lean_ctor_get(v___y_475_, 2);
v_options_485_ = lean_ctor_get(v___y_477_, 2);
lean_inc_ref(v_options_485_);
lean_inc_ref(v_lctx_484_);
v___x_486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_486_, 0, v_env_481_);
lean_ctor_set(v___x_486_, 1, v_mctx_483_);
lean_ctor_set(v___x_486_, 2, v_lctx_484_);
lean_ctor_set(v___x_486_, 3, v_options_485_);
v___x_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_msgData_474_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_ref_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_ref_502_ = lean_ctor_get(v___y_499_, 5);
v___x_503_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_inc(v_ref_502_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_ref_502_);
lean_ctor_set(v___x_508_, 1, v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 1);
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_msg_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0));
v___x_522_ = l_Lean_stringToMessageData(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_547_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_ltFn_x3f_540_; 
v_ltFn_x3f_540_ = lean_ctor_get(v_a_536_, 21);
lean_inc(v_ltFn_x3f_540_);
lean_dec(v_a_536_);
if (lean_obj_tag(v_ltFn_x3f_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; 
v_val_541_ = lean_ctor_get(v_ltFn_x3f_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v_ltFn_x3f_540_, 1);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v_val_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_val_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_ltFn_x3f_540_);
lean_del_object(v___x_538_);
v___x_545_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
v___x_546_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_545_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_546_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_535_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_535_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec(v___y_557_);
lean_dec(v___y_556_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_leFn_x3f_589_; 
v_leFn_x3f_589_ = lean_ctor_get(v_a_585_, 20);
lean_inc(v_leFn_x3f_589_);
lean_dec(v_a_585_);
if (lean_obj_tag(v_leFn_x3f_589_) == 1)
{
lean_object* v_val_590_; lean_object* v___x_592_; 
v_val_590_ = lean_ctor_get(v_leFn_x3f_589_, 0);
lean_inc(v_val_590_);
lean_dec_ref_known(v_leFn_x3f_589_, 1);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_val_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_leFn_x3f_589_);
lean_del_object(v___x_587_);
v___x_594_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
v___x_595_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_594_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_595_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_584_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_584_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object* v_p_618_, uint8_t v_strict_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (v_strict_619_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_618_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_ofNatZero_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v_ofNatZero_641_ = lean_ctor_get(v_a_637_, 18);
lean_inc_ref(v_ofNatZero_641_);
lean_dec(v_a_637_);
v___x_642_ = l_Lean_mkAppB(v_a_633_, v_a_635_, v_ofNatZero_641_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_642_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_635_);
lean_dec(v_a_633_);
v_a_647_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec(v_a_633_);
return v___x_634_;
}
}
else
{
return v___x_632_;
}
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_618_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_ofNatZero_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_ofNatZero_664_ = lean_ctor_get(v_a_660_, 18);
lean_inc_ref(v_ofNatZero_664_);
lean_dec(v_a_660_);
v___x_665_ = l_Lean_mkAppB(v_a_656_, v_a_658_, v_ofNatZero_664_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_658_);
lean_dec(v_a_656_);
v_a_670_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_659_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_659_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_dec(v_a_656_);
return v___x_657_;
}
}
else
{
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_p_678_, lean_object* v_strict_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_strict_boxed_692_; lean_object* v_res_693_; 
v_strict_boxed_692_ = lean_unbox(v_strict_679_);
v_res_693_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_678_, v_strict_boxed_692_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v___y_680_);
lean_dec(v_p_678_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_c_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_p_707_; uint8_t v_strict_708_; lean_object* v___x_709_; 
v_p_707_ = lean_ctor_get(v_c_694_, 0);
v_strict_708_ = lean_ctor_get_uint8(v_c_694_, sizeof(void*)*2);
v___x_709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_707_, v_strict_708_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_c_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v_c_710_);
return v_res_723_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_724_; double v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_float_of_nat(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object* v_cls_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_ref_736_; lean_object* v___x_737_; lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_782_; 
v_ref_736_ = lean_ctor_get(v___y_733_, 5);
v___x_737_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_782_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_782_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_782_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v_traceState_743_; lean_object* v_env_744_; lean_object* v_nextMacroScope_745_; lean_object* v_ngen_746_; lean_object* v_auxDeclNGen_747_; lean_object* v_cache_748_; lean_object* v_messages_749_; lean_object* v_infoState_750_; lean_object* v_snapshotTasks_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_781_; 
v___x_742_ = lean_st_ref_take(v___y_734_);
v_traceState_743_ = lean_ctor_get(v___x_742_, 4);
v_env_744_ = lean_ctor_get(v___x_742_, 0);
v_nextMacroScope_745_ = lean_ctor_get(v___x_742_, 1);
v_ngen_746_ = lean_ctor_get(v___x_742_, 2);
v_auxDeclNGen_747_ = lean_ctor_get(v___x_742_, 3);
v_cache_748_ = lean_ctor_get(v___x_742_, 5);
v_messages_749_ = lean_ctor_get(v___x_742_, 6);
v_infoState_750_ = lean_ctor_get(v___x_742_, 7);
v_snapshotTasks_751_ = lean_ctor_get(v___x_742_, 8);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_781_ == 0)
{
v___x_753_ = v___x_742_;
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_snapshotTasks_751_);
lean_inc(v_infoState_750_);
lean_inc(v_messages_749_);
lean_inc(v_cache_748_);
lean_inc(v_traceState_743_);
lean_inc(v_auxDeclNGen_747_);
lean_inc(v_ngen_746_);
lean_inc(v_nextMacroScope_745_);
lean_inc(v_env_744_);
lean_dec(v___x_742_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint64_t v_tid_755_; lean_object* v_traces_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_780_; 
v_tid_755_ = lean_ctor_get_uint64(v_traceState_743_, sizeof(void*)*1);
v_traces_756_ = lean_ctor_get(v_traceState_743_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_traceState_743_);
if (v_isSharedCheck_780_ == 0)
{
v___x_758_ = v_traceState_743_;
v_isShared_759_ = v_isSharedCheck_780_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_traces_756_);
lean_dec(v_traceState_743_);
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
lean_ctor_set(v___x_764_, 0, v_cls_729_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3, v___x_761_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3 + 8, v___x_761_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*3 + 16, v___x_762_);
v___x_765_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2));
v___x_766_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v_a_738_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_inc(v_ref_736_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_736_);
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
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_env_744_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_nextMacroScope_745_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_ngen_746_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_auxDeclNGen_747_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_778_, 5, v_cache_748_);
lean_ctor_set(v_reuseFailAlloc_778_, 6, v_messages_749_);
lean_ctor_set(v_reuseFailAlloc_778_, 7, v_infoState_750_);
lean_ctor_set(v_reuseFailAlloc_778_, 8, v_snapshotTasks_751_);
v___x_772_ = v_reuseFailAlloc_778_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_st_ref_put(v___y_734_, v___x_772_);
v___x_774_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_774_);
v___x_776_ = v___x_740_;
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
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_MessageData_ofExpr(v_a_1000_);
v___x_1002_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_996_, v___x_1001_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_dec_ref_known(v___x_1002_, 1);
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
v___x_912_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; uint8_t v___x_914_; 
lean_dec_ref_known(v___x_912_, 1);
v___x_913_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_914_ = lean_int_dec_lt(v___y_899_, v___x_913_);
lean_dec(v___y_899_);
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
lean_dec_ref_known(v___x_917_, 1);
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
lean_dec_ref_known(v___x_920_, 1);
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
lean_dec(v___y_899_);
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
lean_dec_ref_known(v___x_944_, 1);
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
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = l_Lean_MessageData_ofExpr(v_a_963_);
v___x_965_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_959_, v___x_964_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref_known(v___x_965_, 1);
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
lean_inc_ref(v_p_936_);
lean_inc(v_k_976_);
lean_inc_n(v_v_977_, 2);
v___y_897_ = v_v_977_;
v___y_898_ = v_v_977_;
v___y_899_ = v_k_976_;
v___y_900_ = v_p_936_;
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
lean_inc_ref(v_p_936_);
lean_inc(v_k_978_);
lean_inc_n(v_v_979_, 2);
v___y_897_ = v_v_979_;
v___y_898_ = v_v_979_;
v___y_899_ = v_k_978_;
v___y_900_ = v_p_936_;
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
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_MessageData_ofExpr(v_a_985_);
v___x_987_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_981_, v___x_986_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref_known(v___x_987_, 1);
lean_inc_ref(v_p_936_);
lean_inc(v_k_978_);
lean_inc_n(v_v_979_, 2);
v___y_897_ = v_v_979_;
v___y_898_ = v_v_979_;
v___y_899_ = v_k_978_;
v___y_900_ = v_p_936_;
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
lean_dec_ref_known(v_a_1194_, 1);
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
lean_dec_ref_known(v_a_1202_, 1);
v___x_1207_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1172_, v_a_1178_);
if (lean_obj_tag(v___x_1207_) == 0)
{
if (v_eqTrue_1176_ == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; uint8_t v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
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
lean_dec_ref_known(v___x_1221_, 1);
v_p_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_a_1208_);
lean_inc_ref(v_p_1223_);
v___x_1224_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1223_, v_a_1208_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
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
lean_dec_ref_known(v_a_1227_, 1);
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
lean_dec_ref_known(v___x_1207_, 1);
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
lean_dec_ref_known(v___x_1279_, 1);
v_p_1281_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_a_1274_);
lean_inc_ref(v_p_1281_);
v___x_1282_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1281_, v_a_1274_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
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
lean_dec_ref_known(v_a_1285_, 1);
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
lean_dec_ref_known(v___x_1394_, 1);
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
lean_dec_ref_known(v_a_1398_, 1);
v___x_1403_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1379_, v_a_1383_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
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
lean_dec_ref_known(v_a_1406_, 1);
v___x_1411_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; uint8_t v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
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
lean_dec_ref_known(v_a_1406_, 1);
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
lean_dec_ref_known(v___x_1518_, 1);
lean_inc_ref(v_lhs_1502_);
v___x_1520_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1502_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_fst_1522_; lean_object* v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
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
lean_dec_ref_known(v___x_1523_, 1);
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
lean_dec_ref_known(v___x_1529_, 1);
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
lean_dec_ref_known(v_a_1535_, 1);
v___x_1540_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1503_, v_a_1507_);
lean_dec_ref(v_rhs_1503_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
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
lean_dec_ref_known(v_a_1543_, 1);
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
lean_dec_ref_known(v_a_1543_, 1);
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
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1873_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1873_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1873_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
uint8_t v_linarith_1684_; 
v_linarith_1684_ = lean_ctor_get_uint8(v_a_1680_, sizeof(void*)*14 + 22);
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
lean_del_object(v___x_1682_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v___x_1689_, v___x_1696_);
lean_inc(v___x_1697_);
v___x_1698_ = l_Lean_Expr_getRevArg_x21(v_e_1666_, v___x_1697_);
lean_inc_ref(v___x_1698_);
v___x_1699_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1698_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1864_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1864_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1864_;
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
v_val_1740_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_val_1740_);
lean_dec_ref_known(v_a_1700_, 1);
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
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1855_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1855_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1855_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
if (lean_obj_tag(v_a_1765_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
v_val_1769_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v_a_1765_, 1);
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1769_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1842_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1842_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1842_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_leInst_x3f_1780_; lean_object* v_ltInst_x3f_1781_; lean_object* v_lawfulOrderLTInst_x3f_1782_; lean_object* v_isPreorderInst_x3f_1783_; lean_object* v_orderedAddInst_x3f_1784_; lean_object* v_isLinearInst_x3f_1785_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; uint8_t v___y_1820_; uint8_t v___y_1840_; 
v_leInst_x3f_1780_ = lean_ctor_get(v_a_1771_, 5);
lean_inc(v_leInst_x3f_1780_);
v_ltInst_x3f_1781_ = lean_ctor_get(v_a_1771_, 6);
lean_inc(v_ltInst_x3f_1781_);
v_lawfulOrderLTInst_x3f_1782_ = lean_ctor_get(v_a_1771_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1782_);
v_isPreorderInst_x3f_1783_ = lean_ctor_get(v_a_1771_, 8);
lean_inc(v_isPreorderInst_x3f_1783_);
v_orderedAddInst_x3f_1784_ = lean_ctor_get(v_a_1771_, 9);
lean_inc(v_orderedAddInst_x3f_1784_);
v_isLinearInst_x3f_1785_ = lean_ctor_get(v_a_1771_, 10);
lean_inc(v_isLinearInst_x3f_1785_);
lean_dec(v_a_1771_);
if (lean_obj_tag(v_leInst_x3f_1780_) == 0)
{
lean_dec(v_isPreorderInst_x3f_1783_);
v___y_1840_ = v___x_1691_;
goto v___jp_1839_;
}
else
{
if (lean_obj_tag(v_isPreorderInst_x3f_1783_) == 0)
{
v___y_1840_ = v___x_1691_;
goto v___jp_1839_;
}
else
{
uint8_t v___x_1841_; 
lean_dec_ref_known(v_isPreorderInst_x3f_1783_, 1);
v___x_1841_ = 0;
v___y_1820_ = v___x_1841_;
goto v___jp_1819_;
}
}
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
v___jp_1786_:
{
if (lean_obj_tag(v_isLinearInst_x3f_1785_) == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_dec(v___y_1788_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1799_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1799_);
v___x_1801_ = v___x_1767_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
else
{
lean_object* v___x_1803_; 
lean_dec_ref_known(v_isLinearInst_x3f_1785_, 1);
lean_del_object(v___x_1767_);
v___x_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1666_, v___x_1709_, v___x_1713_, v___y_1793_, v_eqTrue_1667_, v___y_1788_, v___y_1791_, v___y_1797_, v___y_1789_, v___y_1787_, v___y_1794_, v___y_1790_, v___y_1798_, v___y_1795_, v___y_1792_, v___y_1796_);
lean_dec(v___y_1788_);
return v___x_1803_;
}
}
v___jp_1804_:
{
if (v_eqTrue_1667_ == 0)
{
v___y_1787_ = v___y_1805_;
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___y_1813_;
v___y_1796_ = v___y_1814_;
v___y_1797_ = v___y_1815_;
v___y_1798_ = v___y_1816_;
goto v___jp_1786_;
}
else
{
if (v___y_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v_isLinearInst_x3f_1785_);
lean_del_object(v___x_1767_);
v___x_1818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1666_, v___x_1709_, v___x_1713_, v___y_1811_, v_eqTrue_1667_, v___y_1806_, v___y_1809_, v___y_1815_, v___y_1807_, v___y_1805_, v___y_1812_, v___y_1808_, v___y_1816_, v___y_1813_, v___y_1810_, v___y_1814_);
lean_dec(v___y_1806_);
return v___x_1818_;
}
else
{
v___y_1787_ = v___y_1805_;
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___y_1813_;
v___y_1796_ = v___y_1814_;
v___y_1797_ = v___y_1815_;
v___y_1798_ = v___y_1816_;
goto v___jp_1786_;
}
}
}
v___jp_1819_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1784_) == 0)
{
lean_dec(v_isLinearInst_x3f_1785_);
lean_dec(v_lawfulOrderLTInst_x3f_1782_);
lean_dec(v_ltInst_x3f_1781_);
lean_dec(v_leInst_x3f_1780_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1837_; 
lean_del_object(v___x_1773_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_orderedAddInst_x3f_1784_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_orderedAddInst_x3f_1784_, 0);
lean_dec(v_unused_1838_);
v___x_1822_ = v_orderedAddInst_x3f_1784_;
v_isShared_1823_ = v_isSharedCheck_1837_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v_orderedAddInst_x3f_1784_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1837_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1705_);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1705_);
v___x_1825_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1825_, v_leInst_x3f_1780_);
lean_dec(v_leInst_x3f_1780_);
if (v___x_1826_ == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1825_, v_ltInst_x3f_1781_);
lean_dec(v_ltInst_x3f_1781_);
lean_dec_ref(v___x_1825_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec(v_isLinearInst_x3f_1785_);
lean_dec(v_lawfulOrderLTInst_x3f_1782_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1828_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1828_);
v___x_1830_ = v___x_1702_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
if (v___x_1691_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1782_);
lean_del_object(v___x_1702_);
v___y_1805_ = v_a_1671_;
v___y_1806_ = v_val_1769_;
v___y_1807_ = v_a_1670_;
v___y_1808_ = v_a_1673_;
v___y_1809_ = v_a_1668_;
v___y_1810_ = v_a_1676_;
v___y_1811_ = v___x_1691_;
v___y_1812_ = v_a_1672_;
v___y_1813_ = v_a_1675_;
v___y_1814_ = v_a_1677_;
v___y_1815_ = v_a_1669_;
v___y_1816_ = v_a_1674_;
v___y_1817_ = v___y_1820_;
goto v___jp_1804_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1782_) == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec(v_isLinearInst_x3f_1785_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1666_);
v___x_1832_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1832_);
v___x_1834_ = v___x_1702_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1782_, 1);
lean_del_object(v___x_1702_);
v___y_1805_ = v_a_1671_;
v___y_1806_ = v_val_1769_;
v___y_1807_ = v_a_1670_;
v___y_1808_ = v_a_1673_;
v___y_1809_ = v_a_1668_;
v___y_1810_ = v_a_1676_;
v___y_1811_ = v___x_1691_;
v___y_1812_ = v_a_1672_;
v___y_1813_ = v_a_1675_;
v___y_1814_ = v_a_1677_;
v___y_1815_ = v_a_1669_;
v___y_1816_ = v_a_1674_;
v___y_1817_ = v___y_1820_;
goto v___jp_1804_;
}
}
}
}
else
{
lean_dec_ref(v___x_1825_);
lean_dec(v_lawfulOrderLTInst_x3f_1782_);
lean_dec(v_ltInst_x3f_1781_);
lean_del_object(v___x_1702_);
v___y_1805_ = v_a_1671_;
v___y_1806_ = v_val_1769_;
v___y_1807_ = v_a_1670_;
v___y_1808_ = v_a_1673_;
v___y_1809_ = v_a_1668_;
v___y_1810_ = v_a_1676_;
v___y_1811_ = v___y_1820_;
v___y_1812_ = v_a_1672_;
v___y_1813_ = v_a_1675_;
v___y_1814_ = v_a_1677_;
v___y_1815_ = v_a_1669_;
v___y_1816_ = v_a_1674_;
v___y_1817_ = v___y_1820_;
goto v___jp_1804_;
}
}
}
}
}
v___jp_1839_:
{
if (v___y_1840_ == 0)
{
v___y_1820_ = v___y_1840_;
goto v___jp_1819_;
}
else
{
lean_dec(v_isLinearInst_x3f_1785_);
lean_dec(v_orderedAddInst_x3f_1784_);
lean_dec(v_lawfulOrderLTInst_x3f_1782_);
lean_dec(v_ltInst_x3f_1781_);
lean_dec(v_leInst_x3f_1780_);
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
goto v___jp_1775_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_val_1769_);
lean_del_object(v___x_1767_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
v_a_1843_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1770_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1770_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_a_1765_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
v___x_1851_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1851_);
v___x_1853_ = v___x_1767_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
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
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v___x_1705_);
lean_del_object(v___x_1702_);
lean_dec_ref(v_e_1666_);
v_a_1856_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1764_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1764_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
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
lean_dec_ref_known(v___x_1727_, 1);
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
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v___x_1698_);
lean_dec(v___x_1697_);
lean_dec(v___x_1689_);
lean_dec_ref(v_e_1666_);
v_a_1865_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1699_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1699_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_e_1666_);
v_a_1874_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1679_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1679_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1882_, lean_object* v_eqTrue_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
uint8_t v_eqTrue_boxed_1895_; lean_object* v_res_1896_; 
v_eqTrue_boxed_1895_ = lean_unbox(v_eqTrue_1883_);
v_res_1896_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1882_, v_eqTrue_boxed_1895_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec(v_a_1884_);
return v_res_1896_;
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
