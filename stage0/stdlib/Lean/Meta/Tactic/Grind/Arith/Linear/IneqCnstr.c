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
size_t v_x_69243__boxed_62_; size_t v_x_69244__boxed_63_; lean_object* v_res_64_; 
v_x_69243__boxed_62_ = lean_unbox_usize(v_x_60_);
lean_dec(v_x_60_);
v_x_69244__boxed_63_ = lean_unbox_usize(v_x_61_);
lean_dec(v_x_61_);
v_res_64_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_58_, v_x_59_, v_x_69243__boxed_62_, v_x_69244__boxed_63_);
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
v_options_485_ = lean_ctor_get(v___y_477_, 1);
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
v_ref_502_ = lean_ctor_get(v___y_499_, 4);
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
v_ref_736_ = lean_ctor_get(v___y_733_, 4);
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
lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v_options_921_; lean_object* v_toCold_922_; uint8_t v_hasTrace_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; 
v_options_921_ = lean_ctor_get(v_a_841_, 1);
v_toCold_922_ = lean_ctor_get(v_a_841_, 0);
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
lean_object* v_inheritedTraceOptions_999_; lean_object* v_cls_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_inheritedTraceOptions_999_ = lean_ctor_get(v_toCold_922_, 4);
v_cls_1000_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_1001_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_1002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_999_, v_options_921_, v___x_1001_);
if (v___x_1002_ == 0)
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
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_MessageData_ofExpr(v_a_1004_);
v___x_1006_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1000_, v___x_1005_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_dec_ref_known(v___x_1006_, 1);
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
return v___x_1006_;
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_c_831_);
v_a_1007_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1003_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
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
v_options_938_ = lean_ctor_get(v___y_934_, 1);
v_hasTrace_939_ = lean_ctor_get_uint8(v_options_938_, sizeof(void*)*1);
if (v_hasTrace_939_ == 0)
{
lean_dec_ref(v_c_831_);
goto v___jp_844_;
}
else
{
lean_object* v_toCold_940_; lean_object* v_inheritedTraceOptions_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_toCold_940_ = lean_ctor_get(v___y_934_, 0);
v_inheritedTraceOptions_941_ = lean_ctor_get(v_toCold_940_, 4);
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_941_, v_options_938_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_c_831_);
goto v___jp_844_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec_ref(v_c_831_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l_Lean_MessageData_ofExpr(v_a_946_);
v___x_948_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_942_, v___x_947_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
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
v_options_957_ = lean_ctor_get(v___y_934_, 1);
v_hasTrace_958_ = lean_ctor_get_uint8(v_options_957_, sizeof(void*)*1);
if (v_hasTrace_958_ == 0)
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
lean_object* v_toCold_959_; lean_object* v_inheritedTraceOptions_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_toCold_959_ = lean_ctor_get(v___y_934_, 0);
v_inheritedTraceOptions_960_ = lean_ctor_get(v_toCold_959_, 4);
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_962_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_960_, v_options_957_, v___x_962_);
if (v___x_963_ == 0)
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
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = l_Lean_MessageData_ofExpr(v_a_965_);
v___x_967_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_961_, v___x_966_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref_known(v___x_967_, 1);
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
return v___x_967_;
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v_c_831_);
v_a_968_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_964_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
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
}
}
}
else
{
lean_object* v_options_976_; uint8_t v_hasTrace_977_; 
v_options_976_ = lean_ctor_get(v___y_934_, 1);
v_hasTrace_977_ = lean_ctor_get_uint8(v_options_976_, sizeof(void*)*1);
if (v_hasTrace_977_ == 0)
{
lean_object* v_k_978_; lean_object* v_v_979_; 
v_k_978_ = lean_ctor_get(v_p_936_, 0);
v_v_979_ = lean_ctor_get(v_p_936_, 1);
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
lean_object* v_toCold_980_; lean_object* v_k_981_; lean_object* v_v_982_; lean_object* v_inheritedTraceOptions_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_toCold_980_ = lean_ctor_get(v___y_934_, 0);
v_k_981_ = lean_ctor_get(v_p_936_, 0);
v_v_982_ = lean_ctor_get(v_p_936_, 1);
v_inheritedTraceOptions_983_ = lean_ctor_get(v_toCold_980_, 4);
v___x_984_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_985_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_986_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_983_, v_options_976_, v___x_985_);
if (v___x_986_ == 0)
{
lean_inc_ref(v_p_936_);
lean_inc(v_k_981_);
lean_inc_n(v_v_982_, 2);
v___y_897_ = v_v_982_;
v___y_898_ = v_v_982_;
v___y_899_ = v_k_981_;
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
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_831_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_MessageData_ofExpr(v_a_988_);
v___x_990_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_984_, v___x_989_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref_known(v___x_990_, 1);
lean_inc_ref(v_p_936_);
lean_inc(v_k_981_);
lean_inc_n(v_v_982_, 2);
v___y_897_ = v_v_982_;
v___y_898_ = v_v_982_;
v___y_899_ = v_k_981_;
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
return v___x_990_;
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_c_831_);
v_a_991_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_987_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec(v_a_1016_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1029_, v_msg_1030_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1044_, lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1044_, v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1059_, lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1060_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1074_, v_msg_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1089_, lean_object* v_e_1090_, lean_object* v_s_1091_){
_start:
{
lean_object* v_structs_1092_; lean_object* v_typeIdOf_1093_; lean_object* v_exprToStructId_1094_; lean_object* v_exprToStructIdEntries_1095_; lean_object* v_forbiddenNatModules_1096_; lean_object* v_natStructs_1097_; lean_object* v_natTypeIdOf_1098_; lean_object* v_exprToNatStructId_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_structs_1092_ = lean_ctor_get(v_s_1091_, 0);
v_typeIdOf_1093_ = lean_ctor_get(v_s_1091_, 1);
v_exprToStructId_1094_ = lean_ctor_get(v_s_1091_, 2);
v_exprToStructIdEntries_1095_ = lean_ctor_get(v_s_1091_, 3);
v_forbiddenNatModules_1096_ = lean_ctor_get(v_s_1091_, 4);
v_natStructs_1097_ = lean_ctor_get(v_s_1091_, 5);
v_natTypeIdOf_1098_ = lean_ctor_get(v_s_1091_, 6);
v_exprToNatStructId_1099_ = lean_ctor_get(v_s_1091_, 7);
v___x_1100_ = lean_array_get_size(v_structs_1092_);
v___x_1101_ = lean_nat_dec_lt(v_a_1089_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_e_1090_);
return v_s_1091_;
}
else
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1163_; 
lean_inc_ref(v_exprToNatStructId_1099_);
lean_inc_ref(v_natTypeIdOf_1098_);
lean_inc_ref(v_natStructs_1097_);
lean_inc_ref(v_forbiddenNatModules_1096_);
lean_inc_ref(v_exprToStructIdEntries_1095_);
lean_inc_ref(v_exprToStructId_1094_);
lean_inc_ref(v_typeIdOf_1093_);
lean_inc_ref(v_structs_1092_);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1091_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1164_ = lean_ctor_get(v_s_1091_, 7);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_s_1091_, 6);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_s_1091_, 5);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_s_1091_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_s_1091_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_s_1091_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_s_1091_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_s_1091_, 0);
lean_dec(v_unused_1171_);
v___x_1103_ = v_s_1091_;
v_isShared_1104_ = v_isSharedCheck_1163_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_s_1091_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1163_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_v_1105_; lean_object* v_id_1106_; lean_object* v_ringId_x3f_1107_; lean_object* v_type_1108_; lean_object* v_u_1109_; lean_object* v_intModuleInst_1110_; lean_object* v_leInst_x3f_1111_; lean_object* v_ltInst_x3f_1112_; lean_object* v_lawfulOrderLTInst_x3f_1113_; lean_object* v_isPreorderInst_x3f_1114_; lean_object* v_orderedAddInst_x3f_1115_; lean_object* v_isLinearInst_x3f_1116_; lean_object* v_noNatDivInst_x3f_1117_; lean_object* v_ringInst_x3f_1118_; lean_object* v_commRingInst_x3f_1119_; lean_object* v_orderedRingInst_x3f_1120_; lean_object* v_fieldInst_x3f_1121_; lean_object* v_charInst_x3f_1122_; lean_object* v_zero_1123_; lean_object* v_ofNatZero_1124_; lean_object* v_one_x3f_1125_; lean_object* v_leFn_x3f_1126_; lean_object* v_ltFn_x3f_1127_; lean_object* v_addFn_1128_; lean_object* v_zsmulFn_1129_; lean_object* v_nsmulFn_1130_; lean_object* v_zsmulFn_x3f_1131_; lean_object* v_nsmulFn_x3f_1132_; lean_object* v_homomulFn_x3f_1133_; lean_object* v_subFn_1134_; lean_object* v_negFn_1135_; lean_object* v_vars_1136_; lean_object* v_varMap_1137_; lean_object* v_lowers_1138_; lean_object* v_uppers_1139_; lean_object* v_diseqs_1140_; lean_object* v_assignment_1141_; uint8_t v_caseSplits_1142_; lean_object* v_conflict_x3f_1143_; lean_object* v_diseqSplits_1144_; lean_object* v_elimEqs_1145_; lean_object* v_elimStack_1146_; lean_object* v_occurs_1147_; lean_object* v_ignored_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1162_; 
v_v_1105_ = lean_array_fget(v_structs_1092_, v_a_1089_);
v_id_1106_ = lean_ctor_get(v_v_1105_, 0);
v_ringId_x3f_1107_ = lean_ctor_get(v_v_1105_, 1);
v_type_1108_ = lean_ctor_get(v_v_1105_, 2);
v_u_1109_ = lean_ctor_get(v_v_1105_, 3);
v_intModuleInst_1110_ = lean_ctor_get(v_v_1105_, 4);
v_leInst_x3f_1111_ = lean_ctor_get(v_v_1105_, 5);
v_ltInst_x3f_1112_ = lean_ctor_get(v_v_1105_, 6);
v_lawfulOrderLTInst_x3f_1113_ = lean_ctor_get(v_v_1105_, 7);
v_isPreorderInst_x3f_1114_ = lean_ctor_get(v_v_1105_, 8);
v_orderedAddInst_x3f_1115_ = lean_ctor_get(v_v_1105_, 9);
v_isLinearInst_x3f_1116_ = lean_ctor_get(v_v_1105_, 10);
v_noNatDivInst_x3f_1117_ = lean_ctor_get(v_v_1105_, 11);
v_ringInst_x3f_1118_ = lean_ctor_get(v_v_1105_, 12);
v_commRingInst_x3f_1119_ = lean_ctor_get(v_v_1105_, 13);
v_orderedRingInst_x3f_1120_ = lean_ctor_get(v_v_1105_, 14);
v_fieldInst_x3f_1121_ = lean_ctor_get(v_v_1105_, 15);
v_charInst_x3f_1122_ = lean_ctor_get(v_v_1105_, 16);
v_zero_1123_ = lean_ctor_get(v_v_1105_, 17);
v_ofNatZero_1124_ = lean_ctor_get(v_v_1105_, 18);
v_one_x3f_1125_ = lean_ctor_get(v_v_1105_, 19);
v_leFn_x3f_1126_ = lean_ctor_get(v_v_1105_, 20);
v_ltFn_x3f_1127_ = lean_ctor_get(v_v_1105_, 21);
v_addFn_1128_ = lean_ctor_get(v_v_1105_, 22);
v_zsmulFn_1129_ = lean_ctor_get(v_v_1105_, 23);
v_nsmulFn_1130_ = lean_ctor_get(v_v_1105_, 24);
v_zsmulFn_x3f_1131_ = lean_ctor_get(v_v_1105_, 25);
v_nsmulFn_x3f_1132_ = lean_ctor_get(v_v_1105_, 26);
v_homomulFn_x3f_1133_ = lean_ctor_get(v_v_1105_, 27);
v_subFn_1134_ = lean_ctor_get(v_v_1105_, 28);
v_negFn_1135_ = lean_ctor_get(v_v_1105_, 29);
v_vars_1136_ = lean_ctor_get(v_v_1105_, 30);
v_varMap_1137_ = lean_ctor_get(v_v_1105_, 31);
v_lowers_1138_ = lean_ctor_get(v_v_1105_, 32);
v_uppers_1139_ = lean_ctor_get(v_v_1105_, 33);
v_diseqs_1140_ = lean_ctor_get(v_v_1105_, 34);
v_assignment_1141_ = lean_ctor_get(v_v_1105_, 35);
v_caseSplits_1142_ = lean_ctor_get_uint8(v_v_1105_, sizeof(void*)*42);
v_conflict_x3f_1143_ = lean_ctor_get(v_v_1105_, 36);
v_diseqSplits_1144_ = lean_ctor_get(v_v_1105_, 37);
v_elimEqs_1145_ = lean_ctor_get(v_v_1105_, 38);
v_elimStack_1146_ = lean_ctor_get(v_v_1105_, 39);
v_occurs_1147_ = lean_ctor_get(v_v_1105_, 40);
v_ignored_1148_ = lean_ctor_get(v_v_1105_, 41);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_v_1105_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1150_ = v_v_1105_;
v_isShared_1151_ = v_isSharedCheck_1162_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_ignored_1148_);
lean_inc(v_occurs_1147_);
lean_inc(v_elimStack_1146_);
lean_inc(v_elimEqs_1145_);
lean_inc(v_diseqSplits_1144_);
lean_inc(v_conflict_x3f_1143_);
lean_inc(v_assignment_1141_);
lean_inc(v_diseqs_1140_);
lean_inc(v_uppers_1139_);
lean_inc(v_lowers_1138_);
lean_inc(v_varMap_1137_);
lean_inc(v_vars_1136_);
lean_inc(v_negFn_1135_);
lean_inc(v_subFn_1134_);
lean_inc(v_homomulFn_x3f_1133_);
lean_inc(v_nsmulFn_x3f_1132_);
lean_inc(v_zsmulFn_x3f_1131_);
lean_inc(v_nsmulFn_1130_);
lean_inc(v_zsmulFn_1129_);
lean_inc(v_addFn_1128_);
lean_inc(v_ltFn_x3f_1127_);
lean_inc(v_leFn_x3f_1126_);
lean_inc(v_one_x3f_1125_);
lean_inc(v_ofNatZero_1124_);
lean_inc(v_zero_1123_);
lean_inc(v_charInst_x3f_1122_);
lean_inc(v_fieldInst_x3f_1121_);
lean_inc(v_orderedRingInst_x3f_1120_);
lean_inc(v_commRingInst_x3f_1119_);
lean_inc(v_ringInst_x3f_1118_);
lean_inc(v_noNatDivInst_x3f_1117_);
lean_inc(v_isLinearInst_x3f_1116_);
lean_inc(v_orderedAddInst_x3f_1115_);
lean_inc(v_isPreorderInst_x3f_1114_);
lean_inc(v_lawfulOrderLTInst_x3f_1113_);
lean_inc(v_ltInst_x3f_1112_);
lean_inc(v_leInst_x3f_1111_);
lean_inc(v_intModuleInst_1110_);
lean_inc(v_u_1109_);
lean_inc(v_type_1108_);
lean_inc(v_ringId_x3f_1107_);
lean_inc(v_id_1106_);
lean_dec(v_v_1105_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1162_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v_xs_x27_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1152_ = lean_box(0);
v_xs_x27_1153_ = lean_array_fset(v_structs_1092_, v_a_1089_, v___x_1152_);
v___x_1154_ = l_Lean_PersistentArray_push___redArg(v_ignored_1148_, v_e_1090_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 41, v___x_1154_);
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_id_1106_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_ringId_x3f_1107_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_type_1108_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_u_1109_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_intModuleInst_1110_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_leInst_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_ltInst_x3f_1112_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v_lawfulOrderLTInst_x3f_1113_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_isPreorderInst_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v_orderedAddInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1161_, 10, v_isLinearInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1161_, 11, v_noNatDivInst_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1161_, 12, v_ringInst_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1161_, 13, v_commRingInst_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1161_, 14, v_orderedRingInst_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1161_, 15, v_fieldInst_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1161_, 16, v_charInst_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1161_, 17, v_zero_1123_);
lean_ctor_set(v_reuseFailAlloc_1161_, 18, v_ofNatZero_1124_);
lean_ctor_set(v_reuseFailAlloc_1161_, 19, v_one_x3f_1125_);
lean_ctor_set(v_reuseFailAlloc_1161_, 20, v_leFn_x3f_1126_);
lean_ctor_set(v_reuseFailAlloc_1161_, 21, v_ltFn_x3f_1127_);
lean_ctor_set(v_reuseFailAlloc_1161_, 22, v_addFn_1128_);
lean_ctor_set(v_reuseFailAlloc_1161_, 23, v_zsmulFn_1129_);
lean_ctor_set(v_reuseFailAlloc_1161_, 24, v_nsmulFn_1130_);
lean_ctor_set(v_reuseFailAlloc_1161_, 25, v_zsmulFn_x3f_1131_);
lean_ctor_set(v_reuseFailAlloc_1161_, 26, v_nsmulFn_x3f_1132_);
lean_ctor_set(v_reuseFailAlloc_1161_, 27, v_homomulFn_x3f_1133_);
lean_ctor_set(v_reuseFailAlloc_1161_, 28, v_subFn_1134_);
lean_ctor_set(v_reuseFailAlloc_1161_, 29, v_negFn_1135_);
lean_ctor_set(v_reuseFailAlloc_1161_, 30, v_vars_1136_);
lean_ctor_set(v_reuseFailAlloc_1161_, 31, v_varMap_1137_);
lean_ctor_set(v_reuseFailAlloc_1161_, 32, v_lowers_1138_);
lean_ctor_set(v_reuseFailAlloc_1161_, 33, v_uppers_1139_);
lean_ctor_set(v_reuseFailAlloc_1161_, 34, v_diseqs_1140_);
lean_ctor_set(v_reuseFailAlloc_1161_, 35, v_assignment_1141_);
lean_ctor_set(v_reuseFailAlloc_1161_, 36, v_conflict_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1161_, 37, v_diseqSplits_1144_);
lean_ctor_set(v_reuseFailAlloc_1161_, 38, v_elimEqs_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 39, v_elimStack_1146_);
lean_ctor_set(v_reuseFailAlloc_1161_, 40, v_occurs_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 41, v___x_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*42, v_caseSplits_1142_);
v___x_1156_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_array_fset(v_xs_x27_1153_, v_a_1089_, v___x_1156_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1157_);
v___x_1159_ = v___x_1103_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_typeIdOf_1093_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_exprToStructId_1094_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_exprToStructIdEntries_1095_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_forbiddenNatModules_1096_);
lean_ctor_set(v_reuseFailAlloc_1160_, 5, v_natStructs_1097_);
lean_ctor_set(v_reuseFailAlloc_1160_, 6, v_natTypeIdOf_1098_);
lean_ctor_set(v_reuseFailAlloc_1160_, 7, v_exprToNatStructId_1099_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1172_, lean_object* v_e_1173_, lean_object* v_s_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1172_, v_e_1173_, v_s_1174_);
lean_dec(v_a_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1176_, lean_object* v_lhs_1177_, lean_object* v_rhs_1178_, uint8_t v_strict_1179_, uint8_t v_eqTrue_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1193_ = 0;
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_box(v___x_1193_);
v___x_1196_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1196_, 0, v_lhs_1177_);
lean_closure_set(v___x_1196_, 1, v___x_1195_);
lean_closure_set(v___x_1196_, 2, v___x_1194_);
v___x_1197_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1196_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1352_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1352_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1352_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
if (lean_obj_tag(v_a_1198_) == 1)
{
lean_object* v_val_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_del_object(v___x_1200_);
v_val_1202_ = lean_ctor_get(v_a_1198_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v_a_1198_, 1);
v___x_1203_ = lean_box(v___x_1193_);
v___x_1204_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1204_, 0, v_rhs_1178_);
lean_closure_set(v___x_1204_, 1, v___x_1203_);
lean_closure_set(v___x_1204_, 2, v___x_1194_);
v___x_1205_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1204_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1339_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1339_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1339_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
if (lean_obj_tag(v_a_1206_) == 1)
{
lean_object* v_val_1210_; lean_object* v___x_1211_; 
lean_del_object(v___x_1208_);
v_val_1210_ = lean_ctor_get(v_a_1206_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_a_1206_, 1);
v___x_1211_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1176_, v_a_1182_);
if (lean_obj_tag(v___x_1211_) == 0)
{
if (v_eqTrue_1180_ == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; uint8_t v___x_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = lean_unbox(v_a_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec(v_a_1214_);
lean_dec(v_a_1212_);
lean_dec(v_val_1210_);
lean_dec(v_val_1202_);
lean_inc(v_a_1181_);
v___f_1216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1216_, 0, v_a_1181_);
lean_closure_set(v___f_1216_, 1, v_e_1176_);
v___x_1217_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1218_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1217_, v___f_1216_, v_a_1182_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___y_1222_; 
lean_inc(v_val_1202_);
lean_inc(v_val_1210_);
v___x_1219_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_val_1210_);
lean_ctor_set(v___x_1219_, 1, v_val_1202_);
v___x_1220_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1219_);
if (v_strict_1179_ == 0)
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_unbox(v_a_1214_);
lean_dec(v_a_1214_);
v___y_1222_ = v___x_1269_;
goto v___jp_1221_;
}
else
{
lean_dec(v_a_1214_);
v___y_1222_ = v_eqTrue_1180_;
goto v___jp_1221_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1223_, 0, v_e_1176_);
lean_ctor_set(v___x_1223_, 1, v_val_1202_);
lean_ctor_set(v___x_1223_, 2, v_val_1210_);
v___x_1224_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1224_, 0, v___x_1220_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*2, v___y_1222_);
v___x_1225_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1224_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_p_1227_; lean_object* v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_p_1227_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_a_1212_);
lean_inc_ref(v_p_1227_);
v___x_1228_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1227_, v_a_1212_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1229_, v___x_1193_, v_a_1212_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1244_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
if (lean_obj_tag(v_a_1231_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_del_object(v___x_1233_);
v_val_1235_ = lean_ctor_get(v_a_1231_, 0);
lean_inc_n(v_val_1235_, 2);
lean_dec_ref_known(v_a_1231_, 1);
v___x_1236_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1235_);
v___x_1237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1226_);
lean_ctor_set(v___x_1237_, 1, v_val_1235_);
v___x_1238_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*2, v___y_1222_);
v___x_1239_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1238_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec(v_a_1231_);
lean_dec(v_a_1226_);
v___x_1240_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1240_);
v___x_1242_ = v___x_1233_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_a_1226_);
v_a_1245_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1230_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1230_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_a_1226_);
lean_dec(v_a_1212_);
v_a_1253_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1228_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1228_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_a_1212_);
v_a_1261_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1225_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1225_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_a_1212_);
lean_dec(v_val_1210_);
lean_dec(v_val_1202_);
lean_dec_ref(v_e_1176_);
v_a_1270_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1213_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1213_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1278_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1211_, 1);
lean_inc(v_val_1210_);
lean_inc(v_val_1202_);
v___x_1279_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_val_1202_);
lean_ctor_set(v___x_1279_, 1, v_val_1210_);
v___x_1280_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1281_, 0, v_e_1176_);
lean_ctor_set(v___x_1281_, 1, v_val_1202_);
lean_ctor_set(v___x_1281_, 2, v_val_1210_);
v___x_1282_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*2, v_strict_1179_);
v___x_1283_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1282_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_p_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_p_1285_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_a_1278_);
lean_inc_ref(v_p_1285_);
v___x_1286_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1285_, v_a_1278_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1287_, v___x_1193_, v_a_1278_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1302_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1302_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1302_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
if (lean_obj_tag(v_a_1289_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1291_);
v_val_1293_ = lean_ctor_get(v_a_1289_, 0);
lean_inc_n(v_val_1293_, 2);
lean_dec_ref_known(v_a_1289_, 1);
v___x_1294_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1293_);
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_a_1284_);
lean_ctor_set(v___x_1295_, 1, v_val_1293_);
v___x_1296_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*2, v_strict_1179_);
v___x_1297_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1296_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
lean_dec(v_a_1289_);
lean_dec(v_a_1284_);
v___x_1298_ = lean_box(0);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1298_);
v___x_1300_ = v___x_1291_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_a_1284_);
v_a_1303_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1288_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1288_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1284_);
lean_dec(v_a_1278_);
v_a_1311_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1286_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1286_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1278_);
v_a_1319_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1283_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1283_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_val_1210_);
lean_dec(v_val_1202_);
lean_dec_ref(v_e_1176_);
v_a_1327_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1211_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1211_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_a_1206_);
lean_dec(v_val_1202_);
lean_dec_ref(v_e_1176_);
v___x_1335_ = lean_box(0);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1335_);
v___x_1337_ = v___x_1208_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v_val_1202_);
lean_dec_ref(v_e_1176_);
v_a_1340_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1205_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1205_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_dec(v_a_1198_);
lean_dec_ref(v_rhs_1178_);
lean_dec_ref(v_e_1176_);
v___x_1348_ = lean_box(0);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1348_);
v___x_1350_ = v___x_1200_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_rhs_1178_);
lean_dec_ref(v_e_1176_);
v_a_1353_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1197_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1197_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1361_ = _args[0];
lean_object* v_lhs_1362_ = _args[1];
lean_object* v_rhs_1363_ = _args[2];
lean_object* v_strict_1364_ = _args[3];
lean_object* v_eqTrue_1365_ = _args[4];
lean_object* v_a_1366_ = _args[5];
lean_object* v_a_1367_ = _args[6];
lean_object* v_a_1368_ = _args[7];
lean_object* v_a_1369_ = _args[8];
lean_object* v_a_1370_ = _args[9];
lean_object* v_a_1371_ = _args[10];
lean_object* v_a_1372_ = _args[11];
lean_object* v_a_1373_ = _args[12];
lean_object* v_a_1374_ = _args[13];
lean_object* v_a_1375_ = _args[14];
lean_object* v_a_1376_ = _args[15];
lean_object* v_a_1377_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1378_; uint8_t v_eqTrue_boxed_1379_; lean_object* v_res_1380_; 
v_strict_boxed_1378_ = lean_unbox(v_strict_1364_);
v_eqTrue_boxed_1379_ = lean_unbox(v_eqTrue_1365_);
v_res_1380_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1361_, v_lhs_1362_, v_rhs_1363_, v_strict_boxed_1378_, v_eqTrue_boxed_1379_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1381_, lean_object* v_lhs_1382_, lean_object* v_rhs_1383_, uint8_t v_strict_1384_, uint8_t v_eqTrue_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1382_, v_a_1387_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = 0;
v___x_1401_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1382_, v___x_1400_, v_a_1399_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1468_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1468_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1468_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
if (lean_obj_tag(v_a_1402_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1407_; 
lean_del_object(v___x_1404_);
v_val_1406_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v_a_1402_, 1);
v___x_1407_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1383_, v_a_1387_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1383_, v___x_1400_, v_a_1408_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1447_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1447_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1447_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
if (lean_obj_tag(v_a_1410_) == 1)
{
lean_del_object(v___x_1412_);
if (v_eqTrue_1385_ == 0)
{
lean_object* v_val_1414_; lean_object* v___x_1415_; 
v_val_1414_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v_a_1410_, 1);
v___x_1415_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; uint8_t v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_unbox(v_a_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___f_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_a_1416_);
lean_dec(v_val_1414_);
lean_dec(v_val_1406_);
lean_inc(v_a_1386_);
v___f_1418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1418_, 0, v_a_1386_);
lean_closure_set(v___f_1418_, 1, v_e_1381_);
v___x_1419_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1420_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1419_, v___f_1418_, v_a_1387_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___y_1424_; 
lean_inc(v_val_1406_);
lean_inc(v_val_1414_);
v___x_1421_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_val_1414_);
lean_ctor_set(v___x_1421_, 1, v_val_1406_);
v___x_1422_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1421_);
if (v_strict_1384_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_unbox(v_a_1416_);
lean_dec(v_a_1416_);
v___y_1424_ = v___x_1428_;
goto v___jp_1423_;
}
else
{
lean_dec(v_a_1416_);
v___y_1424_ = v_eqTrue_1385_;
goto v___jp_1423_;
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1425_, 0, v_e_1381_);
lean_ctor_set(v___x_1425_, 1, v_val_1406_);
lean_ctor_set(v___x_1425_, 2, v_val_1414_);
v___x_1426_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1426_, 0, v___x_1422_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*2, v___y_1424_);
v___x_1427_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1426_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_val_1414_);
lean_dec(v_val_1406_);
lean_dec_ref(v_e_1381_);
v_a_1429_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1415_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1415_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_val_1437_ = lean_ctor_get(v_a_1410_, 0);
lean_inc_n(v_val_1437_, 2);
lean_dec_ref_known(v_a_1410_, 1);
lean_inc(v_val_1406_);
v___x_1438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_val_1406_);
lean_ctor_set(v___x_1438_, 1, v_val_1437_);
v___x_1439_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1438_);
v___x_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1440_, 0, v_e_1381_);
lean_ctor_set(v___x_1440_, 1, v_val_1406_);
lean_ctor_set(v___x_1440_, 2, v_val_1437_);
v___x_1441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*2, v_strict_1384_);
v___x_1442_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1441_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1442_;
}
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_dec(v_a_1410_);
lean_dec(v_val_1406_);
lean_dec_ref(v_e_1381_);
v___x_1443_ = lean_box(0);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1443_);
v___x_1445_ = v___x_1412_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
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
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_val_1406_);
lean_dec_ref(v_e_1381_);
v_a_1448_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1409_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1409_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_val_1406_);
lean_dec_ref(v_rhs_1383_);
lean_dec_ref(v_e_1381_);
v_a_1456_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1407_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1407_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_dec(v_a_1402_);
lean_dec_ref(v_rhs_1383_);
lean_dec_ref(v_e_1381_);
v___x_1464_ = lean_box(0);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1464_);
v___x_1466_ = v___x_1404_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
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
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_rhs_1383_);
lean_dec_ref(v_e_1381_);
v_a_1469_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1401_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1401_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_rhs_1383_);
lean_dec_ref(v_lhs_1382_);
lean_dec_ref(v_e_1381_);
v_a_1477_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1398_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1398_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1485_ = _args[0];
lean_object* v_lhs_1486_ = _args[1];
lean_object* v_rhs_1487_ = _args[2];
lean_object* v_strict_1488_ = _args[3];
lean_object* v_eqTrue_1489_ = _args[4];
lean_object* v_a_1490_ = _args[5];
lean_object* v_a_1491_ = _args[6];
lean_object* v_a_1492_ = _args[7];
lean_object* v_a_1493_ = _args[8];
lean_object* v_a_1494_ = _args[9];
lean_object* v_a_1495_ = _args[10];
lean_object* v_a_1496_ = _args[11];
lean_object* v_a_1497_ = _args[12];
lean_object* v_a_1498_ = _args[13];
lean_object* v_a_1499_ = _args[14];
lean_object* v_a_1500_ = _args[15];
lean_object* v_a_1501_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1502_; uint8_t v_eqTrue_boxed_1503_; lean_object* v_res_1504_; 
v_strict_boxed_1502_ = lean_unbox(v_strict_1488_);
v_eqTrue_boxed_1503_ = lean_unbox(v_eqTrue_1489_);
v_res_1504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1485_, v_lhs_1486_, v_rhs_1487_, v_strict_boxed_1502_, v_eqTrue_boxed_1503_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec(v_a_1490_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1505_, lean_object* v_lhs_1506_, lean_object* v_rhs_1507_, uint8_t v_strict_1508_, uint8_t v_eqTrue_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
lean_inc_ref(v_lhs_1506_);
v___x_1524_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1506_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_fst_1526_; lean_object* v___x_1527_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_fst_1526_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_fst_1526_);
lean_dec(v_a_1525_);
lean_inc_ref(v_rhs_1507_);
v___x_1527_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1507_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_fst_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1612_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v_fst_1529_ = lean_ctor_get(v_a_1528_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_a_1528_, 1);
lean_dec(v_unused_1613_);
v___x_1531_ = v_a_1528_;
v_isShared_1532_ = v_isSharedCheck_1612_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_fst_1529_);
lean_dec(v_a_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1612_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1506_, v_a_1511_);
lean_dec_ref(v_lhs_1506_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_id_1535_; lean_object* v_structId_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v_id_1535_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_id_1535_);
v_structId_1536_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_structId_1536_);
lean_dec(v_a_1523_);
v___x_1537_ = 0;
v___x_1538_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1526_, v___x_1537_, v_a_1534_, v_structId_1536_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1595_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1595_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1595_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
if (lean_obj_tag(v_a_1539_) == 1)
{
lean_object* v_val_1543_; lean_object* v___x_1544_; 
lean_del_object(v___x_1541_);
v_val_1543_ = lean_ctor_get(v_a_1539_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_a_1539_, 1);
v___x_1544_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1507_, v_a_1511_);
lean_dec_ref(v_rhs_1507_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1529_, v___x_1537_, v_a_1545_, v_structId_1536_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1574_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1574_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1574_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
if (lean_obj_tag(v_a_1547_) == 1)
{
lean_del_object(v___x_1549_);
if (v_eqTrue_1509_ == 0)
{
lean_object* v_val_1551_; lean_object* v___x_1553_; 
v_val_1551_ = lean_ctor_get(v_a_1547_, 0);
lean_inc_n(v_val_1551_, 2);
lean_dec_ref_known(v_a_1547_, 1);
lean_inc(v_val_1543_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 3);
lean_ctor_set(v___x_1531_, 1, v_val_1543_);
lean_ctor_set(v___x_1531_, 0, v_val_1551_);
v___x_1553_ = v___x_1531_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_val_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_val_1543_);
v___x_1553_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; uint8_t v___y_1556_; 
v___x_1554_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1553_);
if (v_strict_1508_ == 0)
{
uint8_t v___x_1560_; 
v___x_1560_ = 1;
v___y_1556_ = v___x_1560_;
goto v___jp_1555_;
}
else
{
v___y_1556_ = v_eqTrue_1509_;
goto v___jp_1555_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1557_, 0, v_e_1505_);
lean_ctor_set(v___x_1557_, 1, v_id_1535_);
lean_ctor_set(v___x_1557_, 2, v_val_1543_);
lean_ctor_set(v___x_1557_, 3, v_val_1551_);
v___x_1558_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1558_, 0, v___x_1554_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*2, v___y_1556_);
v___x_1559_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1558_, v_structId_1536_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_structId_1536_);
return v___x_1559_;
}
}
}
else
{
lean_object* v_val_1562_; lean_object* v___x_1564_; 
v_val_1562_ = lean_ctor_get(v_a_1547_, 0);
lean_inc_n(v_val_1562_, 2);
lean_dec_ref_known(v_a_1547_, 1);
lean_inc(v_val_1543_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 3);
lean_ctor_set(v___x_1531_, 1, v_val_1562_);
lean_ctor_set(v___x_1531_, 0, v_val_1543_);
v___x_1564_ = v___x_1531_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_val_1543_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_val_1562_);
v___x_1564_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1564_);
v___x_1566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1566_, 0, v_e_1505_);
lean_ctor_set(v___x_1566_, 1, v_id_1535_);
lean_ctor_set(v___x_1566_, 2, v_val_1543_);
lean_ctor_set(v___x_1566_, 3, v_val_1562_);
v___x_1567_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*2, v_strict_1508_);
v___x_1568_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1567_, v_structId_1536_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_structId_1536_);
return v___x_1568_;
}
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_dec(v_a_1547_);
lean_dec(v_val_1543_);
lean_dec(v_structId_1536_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_e_1505_);
v___x_1570_ = lean_box(0);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1570_);
v___x_1572_ = v___x_1549_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_val_1543_);
lean_dec(v_structId_1536_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_e_1505_);
v_a_1575_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1546_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1546_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_val_1543_);
lean_dec(v_structId_1536_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_e_1505_);
v_a_1583_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1544_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1544_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v_a_1539_);
lean_dec(v_structId_1536_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_e_1505_);
v___x_1591_ = lean_box(0);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1591_);
v___x_1593_ = v___x_1541_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_structId_1536_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_e_1505_);
v_a_1596_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1538_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1538_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec(v_fst_1526_);
lean_dec(v_a_1523_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_e_1505_);
v_a_1604_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1533_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1533_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_fst_1526_);
lean_dec(v_a_1523_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_lhs_1506_);
lean_dec_ref(v_e_1505_);
v_a_1614_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1527_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1527_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1523_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_lhs_1506_);
lean_dec_ref(v_e_1505_);
v_a_1622_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1524_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1524_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_lhs_1506_);
lean_dec_ref(v_e_1505_);
v_a_1630_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1522_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1522_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1638_ = _args[0];
lean_object* v_lhs_1639_ = _args[1];
lean_object* v_rhs_1640_ = _args[2];
lean_object* v_strict_1641_ = _args[3];
lean_object* v_eqTrue_1642_ = _args[4];
lean_object* v_a_1643_ = _args[5];
lean_object* v_a_1644_ = _args[6];
lean_object* v_a_1645_ = _args[7];
lean_object* v_a_1646_ = _args[8];
lean_object* v_a_1647_ = _args[9];
lean_object* v_a_1648_ = _args[10];
lean_object* v_a_1649_ = _args[11];
lean_object* v_a_1650_ = _args[12];
lean_object* v_a_1651_ = _args[13];
lean_object* v_a_1652_ = _args[14];
lean_object* v_a_1653_ = _args[15];
lean_object* v_a_1654_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1655_; uint8_t v_eqTrue_boxed_1656_; lean_object* v_res_1657_; 
v_strict_boxed_1655_ = lean_unbox(v_strict_1641_);
v_eqTrue_boxed_1656_ = lean_unbox(v_eqTrue_1642_);
v_res_1657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1638_, v_lhs_1639_, v_rhs_1640_, v_strict_boxed_1655_, v_eqTrue_boxed_1656_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec(v_a_1643_);
return v_res_1657_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
if (lean_obj_tag(v_x_1659_) == 0)
{
uint8_t v___x_1660_; 
v___x_1660_ = 1;
return v___x_1660_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = 0;
return v___x_1661_;
}
}
else
{
if (lean_obj_tag(v_x_1659_) == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = 0;
return v___x_1662_;
}
else
{
lean_object* v_val_1663_; lean_object* v_val_1664_; uint8_t v___x_1665_; 
v_val_1663_ = lean_ctor_get(v_x_1658_, 0);
v_val_1664_ = lean_ctor_get(v_x_1659_, 0);
v___x_1665_ = lean_expr_eqv(v_val_1663_, v_val_1664_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1666_, v_x_1667_);
lean_dec(v_x_1667_);
lean_dec(v_x_1666_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1670_, uint8_t v_eqTrue_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1674_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1877_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1877_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1877_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v_linarith_1688_; 
v_linarith_1688_ = lean_ctor_get_uint8(v_a_1684_, sizeof(void*)*14 + 22);
lean_dec(v_a_1684_);
if (v_linarith_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec_ref(v_e_1670_);
v___x_1689_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1689_);
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = l_Lean_Expr_getAppNumArgs(v_e_1670_);
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = lean_nat_dec_eq(v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v___x_1693_);
lean_dec_ref(v_e_1670_);
v___x_1696_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1696_);
v___x_1698_ = v___x_1686_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_del_object(v___x_1686_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_sub(v___x_1693_, v___x_1700_);
lean_inc(v___x_1701_);
v___x_1702_ = l_Lean_Expr_getRevArg_x21(v_e_1670_, v___x_1701_);
lean_inc_ref(v___x_1702_);
v___x_1703_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1702_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1868_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1868_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1868_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v_strict_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; 
v___x_1708_ = lean_nat_sub(v___x_1701_, v___x_1700_);
lean_dec(v___x_1701_);
v___x_1709_ = l_Lean_Expr_getRevArg_x21(v_e_1670_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(2u);
v___x_1711_ = lean_nat_sub(v___x_1693_, v___x_1710_);
v___x_1712_ = lean_nat_sub(v___x_1711_, v___x_1700_);
lean_dec(v___x_1711_);
v___x_1713_ = l_Lean_Expr_getRevArg_x21(v_e_1670_, v___x_1712_);
v___x_1714_ = lean_unsigned_to_nat(3u);
v___x_1715_ = lean_nat_sub(v___x_1693_, v___x_1714_);
lean_dec(v___x_1693_);
v___x_1716_ = lean_nat_sub(v___x_1715_, v___x_1700_);
lean_dec(v___x_1715_);
v___x_1717_ = l_Lean_Expr_getRevArg_x21(v_e_1670_, v___x_1716_);
if (lean_obj_tag(v_a_1704_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1745_; 
lean_del_object(v___x_1706_);
lean_dec_ref(v___x_1702_);
v_val_1744_ = lean_ctor_get(v_a_1704_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v_a_1704_, 1);
v___x_1745_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1744_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_leFn_x3f_1750_; lean_object* v_ltFn_x3f_1751_; uint8_t v___x_1752_; 
v_leFn_x3f_1750_ = lean_ctor_get(v_a_1746_, 20);
lean_inc(v_leFn_x3f_1750_);
v_ltFn_x3f_1751_ = lean_ctor_get(v_a_1746_, 21);
lean_inc(v_ltFn_x3f_1751_);
lean_dec(v_a_1746_);
v___x_1752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1750_, v___x_1709_);
lean_dec(v_leFn_x3f_1750_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; 
v___x_1753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1751_, v___x_1709_);
lean_dec_ref(v___x_1709_);
lean_dec(v_ltFn_x3f_1751_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec(v_val_1744_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_e_1670_);
v___x_1754_ = lean_box(0);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1756_ = v___x_1748_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
else
{
lean_del_object(v___x_1748_);
v_strict_1719_ = v___x_1695_;
v___y_1720_ = v_val_1744_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
v___y_1728_ = v_a_1679_;
v___y_1729_ = v_a_1680_;
v___y_1730_ = v_a_1681_;
goto v___jp_1718_;
}
}
else
{
uint8_t v___x_1758_; 
lean_dec(v_ltFn_x3f_1751_);
lean_del_object(v___x_1748_);
lean_dec_ref(v___x_1709_);
v___x_1758_ = 0;
v_strict_1719_ = v___x_1758_;
v___y_1720_ = v_val_1744_;
v___y_1721_ = v_a_1672_;
v___y_1722_ = v_a_1673_;
v___y_1723_ = v_a_1674_;
v___y_1724_ = v_a_1675_;
v___y_1725_ = v_a_1676_;
v___y_1726_ = v_a_1677_;
v___y_1727_ = v_a_1678_;
v___y_1728_ = v_a_1679_;
v___y_1729_ = v_a_1680_;
v___y_1730_ = v_a_1681_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_val_1744_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_e_1670_);
v_a_1760_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1745_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1745_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_a_1704_);
v___x_1768_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1702_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1859_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1859_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1859_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_a_1769_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; 
v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_a_1769_, 1);
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1773_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1846_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1846_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1846_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_leInst_x3f_1784_; lean_object* v_ltInst_x3f_1785_; lean_object* v_lawfulOrderLTInst_x3f_1786_; lean_object* v_isPreorderInst_x3f_1787_; lean_object* v_orderedAddInst_x3f_1788_; lean_object* v_isLinearInst_x3f_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; uint8_t v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; uint8_t v___y_1824_; uint8_t v___y_1844_; 
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
lean_dec(v_isPreorderInst_x3f_1787_);
v___y_1844_ = v___x_1695_;
goto v___jp_1843_;
}
else
{
if (lean_obj_tag(v_isPreorderInst_x3f_1787_) == 0)
{
v___y_1844_ = v___x_1695_;
goto v___jp_1843_;
}
else
{
uint8_t v___x_1845_; 
lean_dec_ref_known(v_isPreorderInst_x3f_1787_, 1);
v___x_1845_ = 0;
v___y_1824_ = v___x_1845_;
goto v___jp_1823_;
}
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
if (lean_obj_tag(v_isLinearInst_x3f_1789_) == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec(v___y_1792_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_e_1670_);
v___x_1803_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1803_);
v___x_1805_ = v___x_1771_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v___x_1807_; 
lean_dec_ref_known(v_isLinearInst_x3f_1789_, 1);
lean_del_object(v___x_1771_);
v___x_1807_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1670_, v___x_1713_, v___x_1717_, v___y_1797_, v_eqTrue_1671_, v___y_1792_, v___y_1795_, v___y_1801_, v___y_1793_, v___y_1791_, v___y_1798_, v___y_1794_, v___y_1802_, v___y_1799_, v___y_1796_, v___y_1800_);
lean_dec(v___y_1792_);
return v___x_1807_;
}
}
v___jp_1808_:
{
if (v_eqTrue_1671_ == 0)
{
v___y_1791_ = v___y_1809_;
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
goto v___jp_1790_;
}
else
{
if (v___y_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v_isLinearInst_x3f_1789_);
lean_del_object(v___x_1771_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1670_, v___x_1713_, v___x_1717_, v___y_1815_, v_eqTrue_1671_, v___y_1810_, v___y_1813_, v___y_1819_, v___y_1811_, v___y_1809_, v___y_1816_, v___y_1812_, v___y_1820_, v___y_1817_, v___y_1814_, v___y_1818_);
lean_dec(v___y_1810_);
return v___x_1822_;
}
else
{
v___y_1791_ = v___y_1809_;
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
goto v___jp_1790_;
}
}
}
v___jp_1823_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1788_) == 0)
{
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec(v_leInst_x3f_1784_);
lean_dec(v_val_1773_);
lean_del_object(v___x_1771_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1706_);
lean_dec_ref(v_e_1670_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1841_; 
lean_del_object(v___x_1777_);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_orderedAddInst_x3f_1788_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v_orderedAddInst_x3f_1788_, 0);
lean_dec(v_unused_1842_);
v___x_1826_ = v_orderedAddInst_x3f_1788_;
v_isShared_1827_ = v_isSharedCheck_1841_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v_orderedAddInst_x3f_1788_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1841_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1709_);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1709_);
v___x_1829_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1829_, v_leInst_x3f_1784_);
lean_dec(v_leInst_x3f_1784_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1829_, v_ltInst_x3f_1785_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec_ref(v___x_1829_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_val_1773_);
lean_del_object(v___x_1771_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_e_1670_);
v___x_1832_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1832_);
v___x_1834_ = v___x_1706_;
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
if (v___x_1695_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_del_object(v___x_1706_);
v___y_1809_ = v_a_1675_;
v___y_1810_ = v_val_1773_;
v___y_1811_ = v_a_1674_;
v___y_1812_ = v_a_1677_;
v___y_1813_ = v_a_1672_;
v___y_1814_ = v_a_1680_;
v___y_1815_ = v___x_1695_;
v___y_1816_ = v_a_1676_;
v___y_1817_ = v_a_1679_;
v___y_1818_ = v_a_1681_;
v___y_1819_ = v_a_1673_;
v___y_1820_ = v_a_1678_;
v___y_1821_ = v___y_1824_;
goto v___jp_1808_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1786_) == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_val_1773_);
lean_del_object(v___x_1771_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_e_1670_);
v___x_1836_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1836_);
v___x_1838_ = v___x_1706_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1786_, 1);
lean_del_object(v___x_1706_);
v___y_1809_ = v_a_1675_;
v___y_1810_ = v_val_1773_;
v___y_1811_ = v_a_1674_;
v___y_1812_ = v_a_1677_;
v___y_1813_ = v_a_1672_;
v___y_1814_ = v_a_1680_;
v___y_1815_ = v___x_1695_;
v___y_1816_ = v_a_1676_;
v___y_1817_ = v_a_1679_;
v___y_1818_ = v_a_1681_;
v___y_1819_ = v_a_1673_;
v___y_1820_ = v_a_1678_;
v___y_1821_ = v___y_1824_;
goto v___jp_1808_;
}
}
}
}
else
{
lean_dec_ref(v___x_1829_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1785_);
lean_del_object(v___x_1706_);
v___y_1809_ = v_a_1675_;
v___y_1810_ = v_val_1773_;
v___y_1811_ = v_a_1674_;
v___y_1812_ = v_a_1677_;
v___y_1813_ = v_a_1672_;
v___y_1814_ = v_a_1680_;
v___y_1815_ = v___y_1824_;
v___y_1816_ = v_a_1676_;
v___y_1817_ = v_a_1679_;
v___y_1818_ = v_a_1681_;
v___y_1819_ = v_a_1673_;
v___y_1820_ = v_a_1678_;
v___y_1821_ = v___y_1824_;
goto v___jp_1808_;
}
}
}
}
}
v___jp_1843_:
{
if (v___y_1844_ == 0)
{
v___y_1824_ = v___y_1844_;
goto v___jp_1823_;
}
else
{
lean_dec(v_isLinearInst_x3f_1789_);
lean_dec(v_orderedAddInst_x3f_1788_);
lean_dec(v_lawfulOrderLTInst_x3f_1786_);
lean_dec(v_ltInst_x3f_1785_);
lean_dec(v_leInst_x3f_1784_);
lean_dec(v_val_1773_);
lean_del_object(v___x_1771_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1706_);
lean_dec_ref(v_e_1670_);
goto v___jp_1779_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_val_1773_);
lean_del_object(v___x_1771_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1706_);
lean_dec_ref(v_e_1670_);
v_a_1847_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1774_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1774_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_a_1769_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1706_);
lean_dec_ref(v_e_1670_);
v___x_1855_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1855_);
v___x_1857_ = v___x_1771_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1706_);
lean_dec_ref(v_e_1670_);
v_a_1860_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1768_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1768_);
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
v___jp_1718_:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; uint8_t v___x_1733_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = lean_unbox(v_a_1732_);
lean_dec(v_a_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1670_, v___x_1713_, v___x_1717_, v_strict_1719_, v_eqTrue_1671_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1720_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1670_, v___x_1713_, v___x_1717_, v_strict_1719_, v_eqTrue_1671_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1720_);
return v___x_1735_;
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v___y_1720_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_e_1670_);
v_a_1736_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1731_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1731_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v___x_1702_);
lean_dec(v___x_1701_);
lean_dec(v___x_1693_);
lean_dec_ref(v_e_1670_);
v_a_1869_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1703_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1703_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v_e_1670_);
v_a_1878_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1683_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1683_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1886_, lean_object* v_eqTrue_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v_eqTrue_boxed_1899_; lean_object* v_res_1900_; 
v_eqTrue_boxed_1899_ = lean_unbox(v_eqTrue_1887_);
v_res_1900_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1886_, v_eqTrue_boxed_1899_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec(v_a_1888_);
return v_res_1900_;
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
