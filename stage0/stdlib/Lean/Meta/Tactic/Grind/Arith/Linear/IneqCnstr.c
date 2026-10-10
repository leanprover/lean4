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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(lean_object* v_fn_x3f_1_, lean_object* v_inst_2_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_x3f_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_fn_x3f_1_, v_inst_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object* v_fn_x3f_10_, lean_object* v_inst_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_fn_x3f_10_, v_inst_11_);
lean_dec_ref(v_inst_11_);
lean_dec(v_fn_x3f_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(lean_object* v_c_14_, lean_object* v_x_15_, size_t v_x_16_, size_t v_x_17_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v_cs_18_; size_t v_j_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_cs_18_ = lean_ctor_get(v_x_15_, 0);
v_j_19_ = lean_usize_shift_right(v_x_16_, v_x_17_);
v___x_20_ = lean_usize_to_nat(v_j_19_);
v___x_21_ = lean_array_get_size(v_cs_18_);
v___x_22_ = lean_nat_dec_lt(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_dec(v___x_20_);
lean_dec_ref(v_c_14_);
return v_x_15_;
}
else
{
lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_40_; 
lean_inc_ref(v_cs_18_);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v_x_15_, 0);
lean_dec(v_unused_41_);
v___x_24_ = v_x_15_;
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
else
{
lean_dec(v_x_15_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v_i_29_; size_t v___x_30_; size_t v_shift_31_; lean_object* v_v_32_; lean_object* v___x_33_; lean_object* v_xs_x27_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_shift_left(v___x_26_, v_x_17_);
v___x_28_ = lean_usize_sub(v___x_27_, v___x_26_);
v_i_29_ = lean_usize_land(v_x_16_, v___x_28_);
v___x_30_ = ((size_t)5ULL);
v_shift_31_ = lean_usize_sub(v_x_17_, v___x_30_);
v_v_32_ = lean_array_fget(v_cs_18_, v___x_20_);
v___x_33_ = lean_box(0);
v_xs_x27_34_ = lean_array_fset(v_cs_18_, v___x_20_, v___x_33_);
v___x_35_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_14_, v_v_32_, v_i_29_, v_shift_31_);
v___x_36_ = lean_array_fset(v_xs_x27_34_, v___x_20_, v___x_35_);
lean_dec(v___x_20_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_36_);
v___x_38_ = v___x_24_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
else
{
lean_object* v_vs_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_vs_42_ = lean_ctor_get(v_x_15_, 0);
v___x_43_ = lean_usize_to_nat(v_x_16_);
v___x_44_ = lean_array_get_size(v_vs_42_);
v___x_45_ = lean_nat_dec_lt(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec(v___x_43_);
lean_dec_ref(v_c_14_);
return v_x_15_;
}
else
{
lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_57_; 
lean_inc_ref(v_vs_42_);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_x_15_, 0);
lean_dec(v_unused_58_);
v___x_47_ = v_x_15_;
v_isShared_48_ = v_isSharedCheck_57_;
goto v_resetjp_46_;
}
else
{
lean_dec(v_x_15_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_57_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_v_49_; lean_object* v___x_50_; lean_object* v_xs_x27_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v_v_49_ = lean_array_fget(v_vs_42_, v___x_43_);
v___x_50_ = lean_box(0);
v_xs_x27_51_ = lean_array_fset(v_vs_42_, v___x_43_, v___x_50_);
v___x_52_ = l_Lean_PersistentArray_push___redArg(v_v_49_, v_c_14_);
v___x_53_ = lean_array_fset(v_xs_x27_51_, v___x_43_, v___x_52_);
lean_dec(v___x_43_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_53_);
v___x_55_ = v___x_47_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
size_t v_x_16_ = stack[2].m_num;
size_t v_x_17_ = stack[3].m_num;
lean_object* v_res_59_;
v_res_59_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_14_, v_x_15_, v_x_16_, v_x_17_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4___boxed(lean_object* v_c_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
size_t v_x_69619__boxed_64_; size_t v_x_69620__boxed_65_; lean_object* v_res_66_; 
v_x_69619__boxed_64_ = lean_unbox_usize(v_x_62_);
lean_dec(v_x_62_);
v_x_69620__boxed_65_ = lean_unbox_usize(v_x_63_);
lean_dec(v_x_63_);
v_res_66_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_60_, v_x_61_, v_x_69619__boxed_64_, v_x_69620__boxed_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object* v_c_67_, lean_object* v_t_68_, lean_object* v_i_69_){
_start:
{
lean_object* v_root_70_; lean_object* v_tail_71_; lean_object* v_size_72_; size_t v_shift_73_; lean_object* v_tailOff_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_98_; 
v_root_70_ = lean_ctor_get(v_t_68_, 0);
v_tail_71_ = lean_ctor_get(v_t_68_, 1);
v_size_72_ = lean_ctor_get(v_t_68_, 2);
v_shift_73_ = lean_ctor_get_usize(v_t_68_, 4);
v_tailOff_74_ = lean_ctor_get(v_t_68_, 3);
v_isSharedCheck_98_ = !lean_is_exclusive(v_t_68_);
if (v_isSharedCheck_98_ == 0)
{
v___x_76_ = v_t_68_;
v_isShared_77_ = v_isSharedCheck_98_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_tailOff_74_);
lean_inc(v_size_72_);
lean_inc(v_tail_71_);
lean_inc(v_root_70_);
lean_dec(v_t_68_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_98_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint8_t v___x_78_; 
v___x_78_ = lean_nat_dec_le(v_tailOff_74_, v_i_69_);
if (v___x_78_ == 0)
{
size_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_79_ = lean_usize_of_nat(v_i_69_);
v___x_80_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_67_, v_root_70_, v___x_79_, v_shift_73_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_80_);
v___x_82_ = v___x_76_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_tail_71_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_size_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 3, v_tailOff_74_);
lean_ctor_set_usize(v_reuseFailAlloc_83_, 4, v_shift_73_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_nat_sub(v_i_69_, v_tailOff_74_);
v___x_85_ = lean_array_get_size(v_tail_71_);
v___x_86_ = lean_nat_dec_lt(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_88_; 
lean_dec(v___x_84_);
lean_dec_ref(v_c_67_);
if (v_isShared_77_ == 0)
{
v___x_88_ = v___x_76_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_root_70_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_tail_71_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_size_72_);
lean_ctor_set(v_reuseFailAlloc_89_, 3, v_tailOff_74_);
lean_ctor_set_usize(v_reuseFailAlloc_89_, 4, v_shift_73_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v_v_90_; lean_object* v___x_91_; lean_object* v_xs_x27_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v_v_90_ = lean_array_fget(v_tail_71_, v___x_84_);
v___x_91_ = lean_box(0);
v_xs_x27_92_ = lean_array_fset(v_tail_71_, v___x_84_, v___x_91_);
v___x_93_ = l_Lean_PersistentArray_push___redArg(v_v_90_, v_c_67_);
v___x_94_ = lean_array_fset(v_xs_x27_92_, v___x_84_, v___x_93_);
lean_dec(v___x_84_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_94_);
v___x_96_ = v___x_76_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_root_70_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v_size_72_);
lean_ctor_set(v_reuseFailAlloc_97_, 3, v_tailOff_74_);
lean_ctor_set_usize(v_reuseFailAlloc_97_, 4, v_shift_73_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object* v_c_99_, lean_object* v_t_100_, lean_object* v_i_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_99_, v_t_100_, v_i_101_);
lean_dec(v_i_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object* v___y_103_, lean_object* v_c_104_, lean_object* v_v_105_, lean_object* v_s_106_){
_start:
{
lean_object* v_structs_107_; lean_object* v_typeIdOf_108_; lean_object* v_exprToStructId_109_; lean_object* v_exprToStructIdEntries_110_; lean_object* v_forbiddenNatModules_111_; lean_object* v_natStructs_112_; lean_object* v_natTypeIdOf_113_; lean_object* v_exprToNatStructId_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_structs_107_ = lean_ctor_get(v_s_106_, 0);
v_typeIdOf_108_ = lean_ctor_get(v_s_106_, 1);
v_exprToStructId_109_ = lean_ctor_get(v_s_106_, 2);
v_exprToStructIdEntries_110_ = lean_ctor_get(v_s_106_, 3);
v_forbiddenNatModules_111_ = lean_ctor_get(v_s_106_, 4);
v_natStructs_112_ = lean_ctor_get(v_s_106_, 5);
v_natTypeIdOf_113_ = lean_ctor_get(v_s_106_, 6);
v_exprToNatStructId_114_ = lean_ctor_get(v_s_106_, 7);
v___x_115_ = lean_array_get_size(v_structs_107_);
v___x_116_ = lean_nat_dec_lt(v___y_103_, v___x_115_);
if (v___x_116_ == 0)
{
lean_dec_ref(v_c_104_);
return v_s_106_;
}
else
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_178_; 
lean_inc_ref(v_exprToNatStructId_114_);
lean_inc_ref(v_natTypeIdOf_113_);
lean_inc_ref(v_natStructs_112_);
lean_inc_ref(v_forbiddenNatModules_111_);
lean_inc_ref(v_exprToStructIdEntries_110_);
lean_inc_ref(v_exprToStructId_109_);
lean_inc_ref(v_typeIdOf_108_);
lean_inc_ref(v_structs_107_);
v_isSharedCheck_178_ = !lean_is_exclusive(v_s_106_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_179_ = lean_ctor_get(v_s_106_, 7);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_s_106_, 6);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_s_106_, 5);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_s_106_, 4);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_s_106_, 3);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_s_106_, 2);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_s_106_, 1);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_s_106_, 0);
lean_dec(v_unused_186_);
v___x_118_ = v_s_106_;
v_isShared_119_ = v_isSharedCheck_178_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_s_106_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_178_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_v_120_; lean_object* v_id_121_; lean_object* v_ringId_x3f_122_; lean_object* v_type_123_; lean_object* v_u_124_; lean_object* v_intModuleInst_125_; lean_object* v_leInst_x3f_126_; lean_object* v_ltInst_x3f_127_; lean_object* v_lawfulOrderLTInst_x3f_128_; lean_object* v_isPreorderInst_x3f_129_; lean_object* v_orderedAddInst_x3f_130_; lean_object* v_isLinearInst_x3f_131_; lean_object* v_noNatDivInst_x3f_132_; lean_object* v_ringInst_x3f_133_; lean_object* v_commRingInst_x3f_134_; lean_object* v_orderedRingInst_x3f_135_; lean_object* v_fieldInst_x3f_136_; lean_object* v_charInst_x3f_137_; lean_object* v_zero_138_; lean_object* v_ofNatZero_139_; lean_object* v_one_x3f_140_; lean_object* v_leFn_x3f_141_; lean_object* v_ltFn_x3f_142_; lean_object* v_addFn_143_; lean_object* v_zsmulFn_144_; lean_object* v_nsmulFn_145_; lean_object* v_zsmulFn_x3f_146_; lean_object* v_nsmulFn_x3f_147_; lean_object* v_homomulFn_x3f_148_; lean_object* v_subFn_149_; lean_object* v_negFn_150_; lean_object* v_vars_151_; lean_object* v_varMap_152_; lean_object* v_lowers_153_; lean_object* v_uppers_154_; lean_object* v_diseqs_155_; lean_object* v_assignment_156_; uint8_t v_caseSplits_157_; lean_object* v_conflict_x3f_158_; lean_object* v_diseqSplits_159_; lean_object* v_elimEqs_160_; lean_object* v_elimStack_161_; lean_object* v_occurs_162_; lean_object* v_ignored_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_177_; 
v_v_120_ = lean_array_fget(v_structs_107_, v___y_103_);
v_id_121_ = lean_ctor_get(v_v_120_, 0);
v_ringId_x3f_122_ = lean_ctor_get(v_v_120_, 1);
v_type_123_ = lean_ctor_get(v_v_120_, 2);
v_u_124_ = lean_ctor_get(v_v_120_, 3);
v_intModuleInst_125_ = lean_ctor_get(v_v_120_, 4);
v_leInst_x3f_126_ = lean_ctor_get(v_v_120_, 5);
v_ltInst_x3f_127_ = lean_ctor_get(v_v_120_, 6);
v_lawfulOrderLTInst_x3f_128_ = lean_ctor_get(v_v_120_, 7);
v_isPreorderInst_x3f_129_ = lean_ctor_get(v_v_120_, 8);
v_orderedAddInst_x3f_130_ = lean_ctor_get(v_v_120_, 9);
v_isLinearInst_x3f_131_ = lean_ctor_get(v_v_120_, 10);
v_noNatDivInst_x3f_132_ = lean_ctor_get(v_v_120_, 11);
v_ringInst_x3f_133_ = lean_ctor_get(v_v_120_, 12);
v_commRingInst_x3f_134_ = lean_ctor_get(v_v_120_, 13);
v_orderedRingInst_x3f_135_ = lean_ctor_get(v_v_120_, 14);
v_fieldInst_x3f_136_ = lean_ctor_get(v_v_120_, 15);
v_charInst_x3f_137_ = lean_ctor_get(v_v_120_, 16);
v_zero_138_ = lean_ctor_get(v_v_120_, 17);
v_ofNatZero_139_ = lean_ctor_get(v_v_120_, 18);
v_one_x3f_140_ = lean_ctor_get(v_v_120_, 19);
v_leFn_x3f_141_ = lean_ctor_get(v_v_120_, 20);
v_ltFn_x3f_142_ = lean_ctor_get(v_v_120_, 21);
v_addFn_143_ = lean_ctor_get(v_v_120_, 22);
v_zsmulFn_144_ = lean_ctor_get(v_v_120_, 23);
v_nsmulFn_145_ = lean_ctor_get(v_v_120_, 24);
v_zsmulFn_x3f_146_ = lean_ctor_get(v_v_120_, 25);
v_nsmulFn_x3f_147_ = lean_ctor_get(v_v_120_, 26);
v_homomulFn_x3f_148_ = lean_ctor_get(v_v_120_, 27);
v_subFn_149_ = lean_ctor_get(v_v_120_, 28);
v_negFn_150_ = lean_ctor_get(v_v_120_, 29);
v_vars_151_ = lean_ctor_get(v_v_120_, 30);
v_varMap_152_ = lean_ctor_get(v_v_120_, 31);
v_lowers_153_ = lean_ctor_get(v_v_120_, 32);
v_uppers_154_ = lean_ctor_get(v_v_120_, 33);
v_diseqs_155_ = lean_ctor_get(v_v_120_, 34);
v_assignment_156_ = lean_ctor_get(v_v_120_, 35);
v_caseSplits_157_ = lean_ctor_get_uint8(v_v_120_, sizeof(void*)*42);
v_conflict_x3f_158_ = lean_ctor_get(v_v_120_, 36);
v_diseqSplits_159_ = lean_ctor_get(v_v_120_, 37);
v_elimEqs_160_ = lean_ctor_get(v_v_120_, 38);
v_elimStack_161_ = lean_ctor_get(v_v_120_, 39);
v_occurs_162_ = lean_ctor_get(v_v_120_, 40);
v_ignored_163_ = lean_ctor_get(v_v_120_, 41);
v_isSharedCheck_177_ = !lean_is_exclusive(v_v_120_);
if (v_isSharedCheck_177_ == 0)
{
v___x_165_ = v_v_120_;
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_ignored_163_);
lean_inc(v_occurs_162_);
lean_inc(v_elimStack_161_);
lean_inc(v_elimEqs_160_);
lean_inc(v_diseqSplits_159_);
lean_inc(v_conflict_x3f_158_);
lean_inc(v_assignment_156_);
lean_inc(v_diseqs_155_);
lean_inc(v_uppers_154_);
lean_inc(v_lowers_153_);
lean_inc(v_varMap_152_);
lean_inc(v_vars_151_);
lean_inc(v_negFn_150_);
lean_inc(v_subFn_149_);
lean_inc(v_homomulFn_x3f_148_);
lean_inc(v_nsmulFn_x3f_147_);
lean_inc(v_zsmulFn_x3f_146_);
lean_inc(v_nsmulFn_145_);
lean_inc(v_zsmulFn_144_);
lean_inc(v_addFn_143_);
lean_inc(v_ltFn_x3f_142_);
lean_inc(v_leFn_x3f_141_);
lean_inc(v_one_x3f_140_);
lean_inc(v_ofNatZero_139_);
lean_inc(v_zero_138_);
lean_inc(v_charInst_x3f_137_);
lean_inc(v_fieldInst_x3f_136_);
lean_inc(v_orderedRingInst_x3f_135_);
lean_inc(v_commRingInst_x3f_134_);
lean_inc(v_ringInst_x3f_133_);
lean_inc(v_noNatDivInst_x3f_132_);
lean_inc(v_isLinearInst_x3f_131_);
lean_inc(v_orderedAddInst_x3f_130_);
lean_inc(v_isPreorderInst_x3f_129_);
lean_inc(v_lawfulOrderLTInst_x3f_128_);
lean_inc(v_ltInst_x3f_127_);
lean_inc(v_leInst_x3f_126_);
lean_inc(v_intModuleInst_125_);
lean_inc(v_u_124_);
lean_inc(v_type_123_);
lean_inc(v_ringId_x3f_122_);
lean_inc(v_id_121_);
lean_dec(v_v_120_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v_xs_x27_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_167_ = lean_box(0);
v_xs_x27_168_ = lean_array_fset(v_structs_107_, v___y_103_, v___x_167_);
v___x_169_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_104_, v_lowers_153_, v_v_105_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 32, v___x_169_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_id_121_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_ringId_x3f_122_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_type_123_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_u_124_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_intModuleInst_125_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v_leInst_x3f_126_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_ltInst_x3f_127_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_lawfulOrderLTInst_x3f_128_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_isPreorderInst_x3f_129_);
lean_ctor_set(v_reuseFailAlloc_176_, 9, v_orderedAddInst_x3f_130_);
lean_ctor_set(v_reuseFailAlloc_176_, 10, v_isLinearInst_x3f_131_);
lean_ctor_set(v_reuseFailAlloc_176_, 11, v_noNatDivInst_x3f_132_);
lean_ctor_set(v_reuseFailAlloc_176_, 12, v_ringInst_x3f_133_);
lean_ctor_set(v_reuseFailAlloc_176_, 13, v_commRingInst_x3f_134_);
lean_ctor_set(v_reuseFailAlloc_176_, 14, v_orderedRingInst_x3f_135_);
lean_ctor_set(v_reuseFailAlloc_176_, 15, v_fieldInst_x3f_136_);
lean_ctor_set(v_reuseFailAlloc_176_, 16, v_charInst_x3f_137_);
lean_ctor_set(v_reuseFailAlloc_176_, 17, v_zero_138_);
lean_ctor_set(v_reuseFailAlloc_176_, 18, v_ofNatZero_139_);
lean_ctor_set(v_reuseFailAlloc_176_, 19, v_one_x3f_140_);
lean_ctor_set(v_reuseFailAlloc_176_, 20, v_leFn_x3f_141_);
lean_ctor_set(v_reuseFailAlloc_176_, 21, v_ltFn_x3f_142_);
lean_ctor_set(v_reuseFailAlloc_176_, 22, v_addFn_143_);
lean_ctor_set(v_reuseFailAlloc_176_, 23, v_zsmulFn_144_);
lean_ctor_set(v_reuseFailAlloc_176_, 24, v_nsmulFn_145_);
lean_ctor_set(v_reuseFailAlloc_176_, 25, v_zsmulFn_x3f_146_);
lean_ctor_set(v_reuseFailAlloc_176_, 26, v_nsmulFn_x3f_147_);
lean_ctor_set(v_reuseFailAlloc_176_, 27, v_homomulFn_x3f_148_);
lean_ctor_set(v_reuseFailAlloc_176_, 28, v_subFn_149_);
lean_ctor_set(v_reuseFailAlloc_176_, 29, v_negFn_150_);
lean_ctor_set(v_reuseFailAlloc_176_, 30, v_vars_151_);
lean_ctor_set(v_reuseFailAlloc_176_, 31, v_varMap_152_);
lean_ctor_set(v_reuseFailAlloc_176_, 32, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 33, v_uppers_154_);
lean_ctor_set(v_reuseFailAlloc_176_, 34, v_diseqs_155_);
lean_ctor_set(v_reuseFailAlloc_176_, 35, v_assignment_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 36, v_conflict_x3f_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 37, v_diseqSplits_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 38, v_elimEqs_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 39, v_elimStack_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 40, v_occurs_162_);
lean_ctor_set(v_reuseFailAlloc_176_, 41, v_ignored_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*42, v_caseSplits_157_);
v___x_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_array_fset(v_xs_x27_168_, v___y_103_, v___x_171_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_172_);
v___x_174_ = v___x_118_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_typeIdOf_108_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_exprToStructId_109_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_exprToStructIdEntries_110_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_forbiddenNatModules_111_);
lean_ctor_set(v_reuseFailAlloc_175_, 5, v_natStructs_112_);
lean_ctor_set(v_reuseFailAlloc_175_, 6, v_natTypeIdOf_113_);
lean_ctor_set(v_reuseFailAlloc_175_, 7, v_exprToNatStructId_114_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object* v___y_187_, lean_object* v_c_188_, lean_object* v_v_189_, lean_object* v_s_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(v___y_187_, v_c_188_, v_v_189_, v_s_190_);
lean_dec(v_v_189_);
lean_dec(v___y_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object* v___y_192_, lean_object* v_c_193_, lean_object* v_v_194_, lean_object* v_s_195_){
_start:
{
lean_object* v_structs_196_; lean_object* v_typeIdOf_197_; lean_object* v_exprToStructId_198_; lean_object* v_exprToStructIdEntries_199_; lean_object* v_forbiddenNatModules_200_; lean_object* v_natStructs_201_; lean_object* v_natTypeIdOf_202_; lean_object* v_exprToNatStructId_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_structs_196_ = lean_ctor_get(v_s_195_, 0);
v_typeIdOf_197_ = lean_ctor_get(v_s_195_, 1);
v_exprToStructId_198_ = lean_ctor_get(v_s_195_, 2);
v_exprToStructIdEntries_199_ = lean_ctor_get(v_s_195_, 3);
v_forbiddenNatModules_200_ = lean_ctor_get(v_s_195_, 4);
v_natStructs_201_ = lean_ctor_get(v_s_195_, 5);
v_natTypeIdOf_202_ = lean_ctor_get(v_s_195_, 6);
v_exprToNatStructId_203_ = lean_ctor_get(v_s_195_, 7);
v___x_204_ = lean_array_get_size(v_structs_196_);
v___x_205_ = lean_nat_dec_lt(v___y_192_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec_ref(v_c_193_);
return v_s_195_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_267_; 
lean_inc_ref(v_exprToNatStructId_203_);
lean_inc_ref(v_natTypeIdOf_202_);
lean_inc_ref(v_natStructs_201_);
lean_inc_ref(v_forbiddenNatModules_200_);
lean_inc_ref(v_exprToStructIdEntries_199_);
lean_inc_ref(v_exprToStructId_198_);
lean_inc_ref(v_typeIdOf_197_);
lean_inc_ref(v_structs_196_);
v_isSharedCheck_267_ = !lean_is_exclusive(v_s_195_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_268_ = lean_ctor_get(v_s_195_, 7);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_s_195_, 6);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_s_195_, 5);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_s_195_, 4);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_s_195_, 3);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_s_195_, 2);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_s_195_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_s_195_, 0);
lean_dec(v_unused_275_);
v___x_207_ = v_s_195_;
v_isShared_208_ = v_isSharedCheck_267_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_s_195_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_267_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_v_209_; lean_object* v_id_210_; lean_object* v_ringId_x3f_211_; lean_object* v_type_212_; lean_object* v_u_213_; lean_object* v_intModuleInst_214_; lean_object* v_leInst_x3f_215_; lean_object* v_ltInst_x3f_216_; lean_object* v_lawfulOrderLTInst_x3f_217_; lean_object* v_isPreorderInst_x3f_218_; lean_object* v_orderedAddInst_x3f_219_; lean_object* v_isLinearInst_x3f_220_; lean_object* v_noNatDivInst_x3f_221_; lean_object* v_ringInst_x3f_222_; lean_object* v_commRingInst_x3f_223_; lean_object* v_orderedRingInst_x3f_224_; lean_object* v_fieldInst_x3f_225_; lean_object* v_charInst_x3f_226_; lean_object* v_zero_227_; lean_object* v_ofNatZero_228_; lean_object* v_one_x3f_229_; lean_object* v_leFn_x3f_230_; lean_object* v_ltFn_x3f_231_; lean_object* v_addFn_232_; lean_object* v_zsmulFn_233_; lean_object* v_nsmulFn_234_; lean_object* v_zsmulFn_x3f_235_; lean_object* v_nsmulFn_x3f_236_; lean_object* v_homomulFn_x3f_237_; lean_object* v_subFn_238_; lean_object* v_negFn_239_; lean_object* v_vars_240_; lean_object* v_varMap_241_; lean_object* v_lowers_242_; lean_object* v_uppers_243_; lean_object* v_diseqs_244_; lean_object* v_assignment_245_; uint8_t v_caseSplits_246_; lean_object* v_conflict_x3f_247_; lean_object* v_diseqSplits_248_; lean_object* v_elimEqs_249_; lean_object* v_elimStack_250_; lean_object* v_occurs_251_; lean_object* v_ignored_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_266_; 
v_v_209_ = lean_array_fget(v_structs_196_, v___y_192_);
v_id_210_ = lean_ctor_get(v_v_209_, 0);
v_ringId_x3f_211_ = lean_ctor_get(v_v_209_, 1);
v_type_212_ = lean_ctor_get(v_v_209_, 2);
v_u_213_ = lean_ctor_get(v_v_209_, 3);
v_intModuleInst_214_ = lean_ctor_get(v_v_209_, 4);
v_leInst_x3f_215_ = lean_ctor_get(v_v_209_, 5);
v_ltInst_x3f_216_ = lean_ctor_get(v_v_209_, 6);
v_lawfulOrderLTInst_x3f_217_ = lean_ctor_get(v_v_209_, 7);
v_isPreorderInst_x3f_218_ = lean_ctor_get(v_v_209_, 8);
v_orderedAddInst_x3f_219_ = lean_ctor_get(v_v_209_, 9);
v_isLinearInst_x3f_220_ = lean_ctor_get(v_v_209_, 10);
v_noNatDivInst_x3f_221_ = lean_ctor_get(v_v_209_, 11);
v_ringInst_x3f_222_ = lean_ctor_get(v_v_209_, 12);
v_commRingInst_x3f_223_ = lean_ctor_get(v_v_209_, 13);
v_orderedRingInst_x3f_224_ = lean_ctor_get(v_v_209_, 14);
v_fieldInst_x3f_225_ = lean_ctor_get(v_v_209_, 15);
v_charInst_x3f_226_ = lean_ctor_get(v_v_209_, 16);
v_zero_227_ = lean_ctor_get(v_v_209_, 17);
v_ofNatZero_228_ = lean_ctor_get(v_v_209_, 18);
v_one_x3f_229_ = lean_ctor_get(v_v_209_, 19);
v_leFn_x3f_230_ = lean_ctor_get(v_v_209_, 20);
v_ltFn_x3f_231_ = lean_ctor_get(v_v_209_, 21);
v_addFn_232_ = lean_ctor_get(v_v_209_, 22);
v_zsmulFn_233_ = lean_ctor_get(v_v_209_, 23);
v_nsmulFn_234_ = lean_ctor_get(v_v_209_, 24);
v_zsmulFn_x3f_235_ = lean_ctor_get(v_v_209_, 25);
v_nsmulFn_x3f_236_ = lean_ctor_get(v_v_209_, 26);
v_homomulFn_x3f_237_ = lean_ctor_get(v_v_209_, 27);
v_subFn_238_ = lean_ctor_get(v_v_209_, 28);
v_negFn_239_ = lean_ctor_get(v_v_209_, 29);
v_vars_240_ = lean_ctor_get(v_v_209_, 30);
v_varMap_241_ = lean_ctor_get(v_v_209_, 31);
v_lowers_242_ = lean_ctor_get(v_v_209_, 32);
v_uppers_243_ = lean_ctor_get(v_v_209_, 33);
v_diseqs_244_ = lean_ctor_get(v_v_209_, 34);
v_assignment_245_ = lean_ctor_get(v_v_209_, 35);
v_caseSplits_246_ = lean_ctor_get_uint8(v_v_209_, sizeof(void*)*42);
v_conflict_x3f_247_ = lean_ctor_get(v_v_209_, 36);
v_diseqSplits_248_ = lean_ctor_get(v_v_209_, 37);
v_elimEqs_249_ = lean_ctor_get(v_v_209_, 38);
v_elimStack_250_ = lean_ctor_get(v_v_209_, 39);
v_occurs_251_ = lean_ctor_get(v_v_209_, 40);
v_ignored_252_ = lean_ctor_get(v_v_209_, 41);
v_isSharedCheck_266_ = !lean_is_exclusive(v_v_209_);
if (v_isSharedCheck_266_ == 0)
{
v___x_254_ = v_v_209_;
v_isShared_255_ = v_isSharedCheck_266_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_ignored_252_);
lean_inc(v_occurs_251_);
lean_inc(v_elimStack_250_);
lean_inc(v_elimEqs_249_);
lean_inc(v_diseqSplits_248_);
lean_inc(v_conflict_x3f_247_);
lean_inc(v_assignment_245_);
lean_inc(v_diseqs_244_);
lean_inc(v_uppers_243_);
lean_inc(v_lowers_242_);
lean_inc(v_varMap_241_);
lean_inc(v_vars_240_);
lean_inc(v_negFn_239_);
lean_inc(v_subFn_238_);
lean_inc(v_homomulFn_x3f_237_);
lean_inc(v_nsmulFn_x3f_236_);
lean_inc(v_zsmulFn_x3f_235_);
lean_inc(v_nsmulFn_234_);
lean_inc(v_zsmulFn_233_);
lean_inc(v_addFn_232_);
lean_inc(v_ltFn_x3f_231_);
lean_inc(v_leFn_x3f_230_);
lean_inc(v_one_x3f_229_);
lean_inc(v_ofNatZero_228_);
lean_inc(v_zero_227_);
lean_inc(v_charInst_x3f_226_);
lean_inc(v_fieldInst_x3f_225_);
lean_inc(v_orderedRingInst_x3f_224_);
lean_inc(v_commRingInst_x3f_223_);
lean_inc(v_ringInst_x3f_222_);
lean_inc(v_noNatDivInst_x3f_221_);
lean_inc(v_isLinearInst_x3f_220_);
lean_inc(v_orderedAddInst_x3f_219_);
lean_inc(v_isPreorderInst_x3f_218_);
lean_inc(v_lawfulOrderLTInst_x3f_217_);
lean_inc(v_ltInst_x3f_216_);
lean_inc(v_leInst_x3f_215_);
lean_inc(v_intModuleInst_214_);
lean_inc(v_u_213_);
lean_inc(v_type_212_);
lean_inc(v_ringId_x3f_211_);
lean_inc(v_id_210_);
lean_dec(v_v_209_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_266_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v_xs_x27_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_256_ = lean_box(0);
v_xs_x27_257_ = lean_array_fset(v_structs_196_, v___y_192_, v___x_256_);
v___x_258_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_193_, v_uppers_243_, v_v_194_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 33, v___x_258_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_id_210_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_ringId_x3f_211_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_type_212_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_u_213_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_intModuleInst_214_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_leInst_x3f_215_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v_ltInst_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_lawfulOrderLTInst_x3f_217_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v_isPreorderInst_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_265_, 9, v_orderedAddInst_x3f_219_);
lean_ctor_set(v_reuseFailAlloc_265_, 10, v_isLinearInst_x3f_220_);
lean_ctor_set(v_reuseFailAlloc_265_, 11, v_noNatDivInst_x3f_221_);
lean_ctor_set(v_reuseFailAlloc_265_, 12, v_ringInst_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_265_, 13, v_commRingInst_x3f_223_);
lean_ctor_set(v_reuseFailAlloc_265_, 14, v_orderedRingInst_x3f_224_);
lean_ctor_set(v_reuseFailAlloc_265_, 15, v_fieldInst_x3f_225_);
lean_ctor_set(v_reuseFailAlloc_265_, 16, v_charInst_x3f_226_);
lean_ctor_set(v_reuseFailAlloc_265_, 17, v_zero_227_);
lean_ctor_set(v_reuseFailAlloc_265_, 18, v_ofNatZero_228_);
lean_ctor_set(v_reuseFailAlloc_265_, 19, v_one_x3f_229_);
lean_ctor_set(v_reuseFailAlloc_265_, 20, v_leFn_x3f_230_);
lean_ctor_set(v_reuseFailAlloc_265_, 21, v_ltFn_x3f_231_);
lean_ctor_set(v_reuseFailAlloc_265_, 22, v_addFn_232_);
lean_ctor_set(v_reuseFailAlloc_265_, 23, v_zsmulFn_233_);
lean_ctor_set(v_reuseFailAlloc_265_, 24, v_nsmulFn_234_);
lean_ctor_set(v_reuseFailAlloc_265_, 25, v_zsmulFn_x3f_235_);
lean_ctor_set(v_reuseFailAlloc_265_, 26, v_nsmulFn_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_265_, 27, v_homomulFn_x3f_237_);
lean_ctor_set(v_reuseFailAlloc_265_, 28, v_subFn_238_);
lean_ctor_set(v_reuseFailAlloc_265_, 29, v_negFn_239_);
lean_ctor_set(v_reuseFailAlloc_265_, 30, v_vars_240_);
lean_ctor_set(v_reuseFailAlloc_265_, 31, v_varMap_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 32, v_lowers_242_);
lean_ctor_set(v_reuseFailAlloc_265_, 33, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 34, v_diseqs_244_);
lean_ctor_set(v_reuseFailAlloc_265_, 35, v_assignment_245_);
lean_ctor_set(v_reuseFailAlloc_265_, 36, v_conflict_x3f_247_);
lean_ctor_set(v_reuseFailAlloc_265_, 37, v_diseqSplits_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 38, v_elimEqs_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 39, v_elimStack_250_);
lean_ctor_set(v_reuseFailAlloc_265_, 40, v_occurs_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 41, v_ignored_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*42, v_caseSplits_246_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_array_fset(v_xs_x27_257_, v___y_192_, v___x_260_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_261_);
v___x_263_ = v___x_207_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_typeIdOf_197_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_exprToStructId_198_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_exprToStructIdEntries_199_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v_forbiddenNatModules_200_);
lean_ctor_set(v_reuseFailAlloc_264_, 5, v_natStructs_201_);
lean_ctor_set(v_reuseFailAlloc_264_, 6, v_natTypeIdOf_202_);
lean_ctor_set(v_reuseFailAlloc_264_, 7, v_exprToNatStructId_203_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object* v___y_276_, lean_object* v_c_277_, lean_object* v_v_278_, lean_object* v_s_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(v___y_276_, v_c_277_, v_v_278_, v_s_279_);
lean_dec(v_v_278_);
lean_dec(v___y_276_);
return v_res_280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_to_int(v___x_281_);
return v___x_282_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(lean_object* v_k_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = l_Lean_instInhabitedExpr;
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___closed__0);
v___x_299_ = lean_int_dec_eq(v_k_283_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_320_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_320_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_320_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_320_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_vars_307_; lean_object* v_zsmulFn_308_; lean_object* v_size_309_; lean_object* v___x_310_; lean_object* v___y_312_; uint8_t v___x_317_; 
v_vars_307_ = lean_ctor_get(v_a_303_, 30);
lean_inc_ref(v_vars_307_);
lean_dec(v_a_303_);
v_zsmulFn_308_ = lean_ctor_get(v_a_301_, 23);
lean_inc_ref(v_zsmulFn_308_);
lean_dec(v_a_301_);
v_size_309_ = lean_ctor_get(v_vars_307_, 2);
v___x_310_ = l_Lean_mkIntLit(v_k_283_);
v___x_317_ = lean_nat_dec_lt(v_x_284_, v_size_309_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec_ref(v_vars_307_);
v___x_318_ = l_outOfBounds___redArg(v___x_297_);
v___y_312_ = v___x_318_;
goto v___jp_311_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentArray_get_x21___redArg(v___x_297_, v_vars_307_, v_x_284_);
lean_dec_ref(v_vars_307_);
v___y_312_ = v___x_319_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Lean_mkAppB(v_zsmulFn_308_, v___x_310_, v___y_312_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_313_);
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_a_301_);
v_a_321_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_302_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_302_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_300_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_300_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_353_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_353_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_vars_342_; lean_object* v_size_343_; uint8_t v___x_344_; 
v_vars_342_ = lean_ctor_get(v_a_338_, 30);
lean_inc_ref(v_vars_342_);
lean_dec(v_a_338_);
v_size_343_ = lean_ctor_get(v_vars_342_, 2);
v___x_344_ = lean_nat_dec_lt(v_x_284_, v_size_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
lean_dec_ref(v_vars_342_);
v___x_345_ = l_outOfBounds___redArg(v___x_297_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_345_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Lean_PersistentArray_get_x21___redArg(v___x_297_, v_vars_342_, v_x_284_);
lean_dec_ref(v_vars_342_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_349_);
v___x_351_ = v___x_340_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_337_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_337_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_283_ = stack[0].m_obj;
lean_object* v_x_284_ = stack[1].m_obj;
lean_object* v___y_285_ = stack[2].m_obj;
lean_object* v___y_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v___y_289_ = stack[6].m_obj;
lean_object* v___y_290_ = stack[7].m_obj;
lean_object* v___y_291_ = stack[8].m_obj;
lean_object* v___y_292_ = stack[9].m_obj;
lean_object* v___y_293_ = stack[10].m_obj;
lean_object* v___y_294_ = stack[11].m_obj;
lean_object* v___y_295_ = stack[12].m_obj;
lean_object* v_res_362_;
v_res_362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_283_, v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_k_363_, lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_363_, v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec(v___y_366_);
lean_dec(v___y_365_);
lean_dec(v_x_364_);
lean_dec(v_k_363_);
return v_res_377_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(lean_object* v_p_378_, lean_object* v_acc_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
if (lean_obj_tag(v_p_378_) == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_acc_379_);
return v___x_392_;
}
else
{
lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v_p_395_; lean_object* v___x_396_; 
v_k_393_ = lean_ctor_get(v_p_378_, 0);
v_v_394_ = lean_ctor_get(v_p_378_, 1);
v_p_395_ = lean_ctor_get(v_p_378_, 2);
v___x_396_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v___x_398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_393_, v_v_394_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v_addFn_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v_addFn_400_ = lean_ctor_get(v_a_397_, 22);
lean_inc_ref(v_addFn_400_);
lean_dec(v_a_397_);
v___x_401_ = l_Lean_mkAppB(v_addFn_400_, v_acc_379_, v_a_399_);
v_p_378_ = v_p_395_;
v_acc_379_ = v___x_401_;
goto _start;
}
else
{
lean_dec(v_a_397_);
lean_dec_ref(v_acc_379_);
return v___x_398_;
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_acc_379_);
v_a_403_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_396_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_396_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_378_ = stack[0].m_obj;
lean_object* v_acc_379_ = stack[1].m_obj;
lean_object* v___y_380_ = stack[2].m_obj;
lean_object* v___y_381_ = stack[3].m_obj;
lean_object* v___y_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v___y_384_ = stack[6].m_obj;
lean_object* v___y_385_ = stack[7].m_obj;
lean_object* v___y_386_ = stack[8].m_obj;
lean_object* v___y_387_ = stack[9].m_obj;
lean_object* v___y_388_ = stack[10].m_obj;
lean_object* v___y_389_ = stack[11].m_obj;
lean_object* v___y_390_ = stack[12].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_378_, v_acc_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8___boxed(lean_object* v_p_412_, lean_object* v_acc_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_412_, v_acc_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec(v___y_415_);
lean_dec(v___y_414_);
lean_dec(v_p_412_);
return v_res_426_;
}
}
lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(lean_object* v_p_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
if (lean_obj_tag(v_p_427_) == 0)
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_zero_445_; lean_object* v___x_447_; 
v_zero_445_ = lean_ctor_get(v_a_441_, 17);
lean_inc_ref(v_zero_445_);
lean_dec(v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_zero_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_zero_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_440_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_440_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_k_458_; lean_object* v_v_459_; lean_object* v_p_460_; lean_object* v___x_461_; 
v_k_458_ = lean_ctor_get(v_p_427_, 0);
v_v_459_ = lean_ctor_get(v_p_427_, 1);
v_p_460_ = lean_ctor_get(v_p_427_, 2);
v___x_461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__7(v_k_458_, v_v_459_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_spec__8(v_p_460_, v_a_462_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v___x_463_;
}
else
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_427_ = stack[0].m_obj;
lean_object* v___y_428_ = stack[1].m_obj;
lean_object* v___y_429_ = stack[2].m_obj;
lean_object* v___y_430_ = stack[3].m_obj;
lean_object* v___y_431_ = stack[4].m_obj;
lean_object* v___y_432_ = stack[5].m_obj;
lean_object* v___y_433_ = stack[6].m_obj;
lean_object* v___y_434_ = stack[7].m_obj;
lean_object* v___y_435_ = stack[8].m_obj;
lean_object* v___y_436_ = stack[9].m_obj;
lean_object* v___y_437_ = stack[10].m_obj;
lean_object* v___y_438_ = stack[11].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_p_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v_p_465_);
return v_res_478_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(lean_object* v_msgData_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_env_486_; uint8_t v___x_487_; lean_object* v_env_488_; lean_object* v___x_489_; lean_object* v_toCold_490_; lean_object* v_mctx_491_; lean_object* v_lctx_492_; lean_object* v_options_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_485_ = lean_st_ref_get(v___y_483_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_485_);
v___x_487_ = 0;
v_env_488_ = l_Lean_Environment_setRecordingDeps(v_env_486_, v___x_487_);
v___x_489_ = lean_st_ref_get(v___y_481_);
v_toCold_490_ = lean_ctor_get(v___y_482_, 0);
v_mctx_491_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_mctx_491_);
lean_dec(v___x_489_);
v_lctx_492_ = lean_ctor_get(v___y_480_, 2);
v_options_493_ = lean_ctor_get(v_toCold_490_, 2);
lean_inc_ref(v_options_493_);
lean_inc_ref(v_lctx_492_);
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v_env_488_);
lean_ctor_set(v___x_494_, 1, v_mctx_491_);
lean_ctor_set(v___x_494_, 2, v_lctx_492_);
lean_ctor_set(v___x_494_, 3, v_options_493_);
v___x_495_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_msgData_479_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_479_ = stack[0].m_obj;
lean_object* v___y_480_ = stack[1].m_obj;
lean_object* v___y_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object* v_msgData_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_504_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_ref_511_; lean_object* v___x_512_; lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_ref_511_ = lean_ctor_get(v___y_508_, 2);
v___x_512_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_inc(v_ref_511_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_ref_511_);
lean_ctor_set(v___x_517_, 1, v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_505_ = stack[0].m_obj;
lean_object* v___y_506_ = stack[1].m_obj;
lean_object* v___y_507_ = stack[2].m_obj;
lean_object* v___y_508_ = stack[3].m_obj;
lean_object* v___y_509_ = stack[4].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_557_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_557_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_557_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_557_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_ltFn_x3f_550_; 
v_ltFn_x3f_550_ = lean_ctor_get(v_a_546_, 21);
lean_inc(v_ltFn_x3f_550_);
lean_dec(v_a_546_);
if (lean_obj_tag(v_ltFn_x3f_550_) == 1)
{
lean_object* v_val_551_; lean_object* v___x_553_; 
v_val_551_ = lean_ctor_get(v_ltFn_x3f_550_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_ltFn_x3f_550_, 1);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_val_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_ltFn_x3f_550_);
lean_del_object(v___x_548_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
v___x_556_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_555_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_556_;
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_a_558_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_545_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_545_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_533_ = stack[0].m_obj;
lean_object* v___y_534_ = stack[1].m_obj;
lean_object* v___y_535_ = stack[2].m_obj;
lean_object* v___y_536_ = stack[3].m_obj;
lean_object* v___y_537_ = stack[4].m_obj;
lean_object* v___y_538_ = stack[5].m_obj;
lean_object* v___y_539_ = stack[6].m_obj;
lean_object* v___y_540_ = stack[7].m_obj;
lean_object* v___y_541_ = stack[8].m_obj;
lean_object* v___y_542_ = stack[9].m_obj;
lean_object* v___y_543_ = stack[10].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec(v___y_568_);
lean_dec(v___y_567_);
return v_res_579_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_607_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_607_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_leFn_x3f_600_; 
v_leFn_x3f_600_ = lean_ctor_get(v_a_596_, 20);
lean_inc(v_leFn_x3f_600_);
lean_dec(v_a_596_);
if (lean_obj_tag(v_leFn_x3f_600_) == 1)
{
lean_object* v_val_601_; lean_object* v___x_603_; 
v_val_601_ = lean_ctor_get(v_leFn_x3f_600_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v_leFn_x3f_600_, 1);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_val_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_val_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_leFn_x3f_600_);
lean_del_object(v___x_598_);
v___x_605_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
v___x_606_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_605_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_606_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_595_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_595_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_583_ = stack[0].m_obj;
lean_object* v___y_584_ = stack[1].m_obj;
lean_object* v___y_585_ = stack[2].m_obj;
lean_object* v___y_586_ = stack[3].m_obj;
lean_object* v___y_587_ = stack[4].m_obj;
lean_object* v___y_588_ = stack[5].m_obj;
lean_object* v___y_589_ = stack[6].m_obj;
lean_object* v___y_590_ = stack[7].m_obj;
lean_object* v___y_591_ = stack[8].m_obj;
lean_object* v___y_592_ = stack[9].m_obj;
lean_object* v___y_593_ = stack[10].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
return v_res_629_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object* v_p_630_, uint8_t v_strict_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
if (v_strict_631_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_630_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_ofNatZero_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v_ofNatZero_653_ = lean_ctor_get(v_a_649_, 18);
lean_inc_ref(v_ofNatZero_653_);
lean_dec(v_a_649_);
v___x_654_ = l_Lean_mkAppB(v_a_645_, v_a_647_, v_ofNatZero_653_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_a_647_);
lean_dec(v_a_645_);
v_a_659_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_648_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_648_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_dec(v_a_645_);
return v___x_646_;
}
}
else
{
return v___x_644_;
}
}
else
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_630_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_ofNatZero_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v_ofNatZero_676_ = lean_ctor_get(v_a_672_, 18);
lean_inc_ref(v_ofNatZero_676_);
lean_dec(v_a_672_);
v___x_677_ = l_Lean_mkAppB(v_a_668_, v_a_670_, v_ofNatZero_676_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_677_);
v___x_679_ = v___x_674_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_670_);
lean_dec(v_a_668_);
v_a_682_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_671_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_671_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_dec(v_a_668_);
return v___x_669_;
}
}
else
{
return v___x_667_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_630_ = stack[0].m_obj;
uint8_t v_strict_631_ = stack[1].m_num;
lean_object* v___y_632_ = stack[2].m_obj;
lean_object* v___y_633_ = stack[3].m_obj;
lean_object* v___y_634_ = stack[4].m_obj;
lean_object* v___y_635_ = stack[5].m_obj;
lean_object* v___y_636_ = stack[6].m_obj;
lean_object* v___y_637_ = stack[7].m_obj;
lean_object* v___y_638_ = stack[8].m_obj;
lean_object* v___y_639_ = stack[9].m_obj;
lean_object* v___y_640_ = stack[10].m_obj;
lean_object* v___y_641_ = stack[11].m_obj;
lean_object* v___y_642_ = stack[12].m_obj;
lean_object* v_res_690_;
v_res_690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_630_, v_strict_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_p_691_, lean_object* v_strict_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_strict_boxed_705_; lean_object* v_res_706_; 
v_strict_boxed_705_ = lean_unbox(v_strict_692_);
v_res_706_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_691_, v_strict_boxed_705_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v_p_691_);
return v_res_706_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_c_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_p_720_; uint8_t v_strict_721_; lean_object* v___x_722_; 
v_p_720_ = lean_ctor_get(v_c_707_, 0);
v_strict_721_ = lean_ctor_get_uint8(v_c_707_, sizeof(void*)*2);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_720_, v_strict_721_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_707_ = stack[0].m_obj;
lean_object* v___y_708_ = stack[1].m_obj;
lean_object* v___y_709_ = stack[2].m_obj;
lean_object* v___y_710_ = stack[3].m_obj;
lean_object* v___y_711_ = stack[4].m_obj;
lean_object* v___y_712_ = stack[5].m_obj;
lean_object* v___y_713_ = stack[6].m_obj;
lean_object* v___y_714_ = stack[7].m_obj;
lean_object* v___y_715_ = stack[8].m_obj;
lean_object* v___y_716_ = stack[9].m_obj;
lean_object* v___y_717_ = stack[10].m_obj;
lean_object* v___y_718_ = stack[11].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_c_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v_c_724_);
return v_res_737_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_738_; double v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_float_of_nat(v___x_738_);
return v___x_739_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object* v_cls_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_ref_750_; lean_object* v___x_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_797_; 
v_ref_750_ = lean_ctor_get(v___y_747_, 2);
v___x_751_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_797_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_797_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_797_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v_traceState_757_; lean_object* v_env_758_; lean_object* v_nextMacroScope_759_; lean_object* v_ngen_760_; lean_object* v_auxDeclNGen_761_; lean_object* v_cache_762_; lean_object* v_recordedDeps_763_; lean_object* v_messages_764_; lean_object* v_infoState_765_; lean_object* v_snapshotTasks_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_796_; 
v___x_756_ = lean_st_ref_take(v___y_748_);
v_traceState_757_ = lean_ctor_get(v___x_756_, 4);
v_env_758_ = lean_ctor_get(v___x_756_, 0);
v_nextMacroScope_759_ = lean_ctor_get(v___x_756_, 1);
v_ngen_760_ = lean_ctor_get(v___x_756_, 2);
v_auxDeclNGen_761_ = lean_ctor_get(v___x_756_, 3);
v_cache_762_ = lean_ctor_get(v___x_756_, 5);
v_recordedDeps_763_ = lean_ctor_get(v___x_756_, 6);
v_messages_764_ = lean_ctor_get(v___x_756_, 7);
v_infoState_765_ = lean_ctor_get(v___x_756_, 8);
v_snapshotTasks_766_ = lean_ctor_get(v___x_756_, 9);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_796_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_796_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snapshotTasks_766_);
lean_inc(v_infoState_765_);
lean_inc(v_messages_764_);
lean_inc(v_recordedDeps_763_);
lean_inc(v_cache_762_);
lean_inc(v_traceState_757_);
lean_inc(v_auxDeclNGen_761_);
lean_inc(v_ngen_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_env_758_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_796_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint64_t v_tid_770_; lean_object* v_traces_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_795_; 
v_tid_770_ = lean_ctor_get_uint64(v_traceState_757_, sizeof(void*)*1);
v_traces_771_ = lean_ctor_get(v_traceState_757_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_traceState_757_);
if (v_isSharedCheck_795_ == 0)
{
v___x_773_ = v_traceState_757_;
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_traces_771_);
lean_dec(v_traceState_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; double v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_775_ = lean_box(0);
v___x_776_ = lean_box(0);
v___x_777_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0);
v___x_778_ = 0;
v___x_779_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1));
v___x_780_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_780_, 0, v_cls_743_);
lean_ctor_set(v___x_780_, 1, v___x_776_);
lean_ctor_set(v___x_780_, 2, v___x_779_);
lean_ctor_set_float(v___x_780_, sizeof(void*)*3, v___x_777_);
lean_ctor_set_float(v___x_780_, sizeof(void*)*3 + 8, v___x_777_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*3 + 16, v___x_778_);
v___x_781_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2));
v___x_782_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v_a_752_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
lean_inc(v_ref_750_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_ref_750_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_PersistentArray_push___redArg(v_traces_771_, v___x_783_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_784_);
v___x_786_ = v___x_773_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_784_);
lean_ctor_set_uint64(v_reuseFailAlloc_794_, sizeof(void*)*1, v_tid_770_);
v___x_786_ = v_reuseFailAlloc_794_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 4, v___x_786_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_env_758_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_ngen_760_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_auxDeclNGen_761_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v_cache_762_);
lean_ctor_set(v_reuseFailAlloc_793_, 6, v_recordedDeps_763_);
lean_ctor_set(v_reuseFailAlloc_793_, 7, v_messages_764_);
lean_ctor_set(v_reuseFailAlloc_793_, 8, v_infoState_765_);
lean_ctor_set(v_reuseFailAlloc_793_, 9, v_snapshotTasks_766_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_st_ref_put(v___y_748_, v___x_788_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_775_);
v___x_791_ = v___x_754_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_775_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_743_ = stack[0].m_obj;
lean_object* v_msg_744_ = stack[1].m_obj;
lean_object* v___y_745_ = stack[2].m_obj;
lean_object* v___y_746_ = stack[3].m_obj;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_743_, v_msg_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(lean_object* v_cls_799_, lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_799_, v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_nat_to_int(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_821_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_822_ = l_Lean_Name_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_830_ = l_Lean_Name_append(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_838_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_839_ = l_Lean_Name_append(v___x_838_, v___x_837_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16(void){
_start:
{
lean_object* v_cls_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_cls_844_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_845_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_846_ = l_Lean_Name_append(v___x_845_, v_cls_844_);
return v___x_846_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* v_c_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v_toCold_937_; lean_object* v_options_938_; lean_object* v_inheritedTraceOptions_939_; uint8_t v_hasTrace_940_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; 
v_toCold_937_ = lean_ctor_get(v_a_857_, 0);
v_options_938_ = lean_ctor_get(v_toCold_937_, 2);
v_inheritedTraceOptions_939_ = lean_ctor_get(v_toCold_937_, 11);
v_hasTrace_940_ = lean_ctor_get_uint8(v_options_938_, sizeof(void*)*1);
if (v_hasTrace_940_ == 0)
{
v___y_942_ = v_a_848_;
v___y_943_ = v_a_849_;
v___y_944_ = v_a_850_;
v___y_945_ = v_a_851_;
v___y_946_ = v_a_852_;
v___y_947_ = v_a_853_;
v___y_948_ = v_a_854_;
v___y_949_ = v_a_855_;
v___y_950_ = v_a_856_;
v___y_951_ = v_a_857_;
v___y_952_ = v_a_858_;
goto v___jp_941_;
}
else
{
lean_object* v_cls_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_cls_1016_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_1018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_939_, v_options_938_, v___x_1017_);
if (v___x_1018_ == 0)
{
v___y_942_ = v_a_848_;
v___y_943_ = v_a_849_;
v___y_944_ = v_a_850_;
v___y_945_ = v_a_851_;
v___y_946_ = v_a_852_;
v___y_947_ = v_a_853_;
v___y_948_ = v_a_854_;
v___y_949_ = v_a_855_;
v___y_950_ = v_a_856_;
v___y_951_ = v_a_857_;
v___y_952_ = v_a_858_;
goto v___jp_941_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l_Lean_MessageData_ofExpr(v_a_1020_);
v___x_1022_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1016_, v___x_1021_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref_known(v___x_1022_, 1);
v___y_942_ = v_a_848_;
v___y_943_ = v_a_849_;
v___y_944_ = v_a_850_;
v___y_945_ = v_a_851_;
v___y_946_ = v_a_852_;
v___y_947_ = v_a_853_;
v___y_948_ = v_a_854_;
v___y_949_ = v_a_855_;
v___y_950_ = v_a_856_;
v___y_951_ = v_a_857_;
v___y_952_ = v_a_858_;
goto v___jp_941_;
}
else
{
lean_dec_ref(v_c_847_);
return v___x_1022_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_c_847_);
v_a_1023_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1019_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1019_);
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
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
v___jp_863_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v_c_847_);
v___x_876_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_875_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
v___jp_877_:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_847_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_903_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; uint8_t v___x_896_; uint8_t v___x_897_; 
v___x_895_ = 0;
v___x_896_ = lean_unbox(v_a_891_);
lean_dec(v_a_891_);
v___x_897_ = l_Lean_instBEqLBool_beq(v___x_896_, v___x_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_900_; 
lean_dec(v___y_878_);
v___x_898_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_898_);
v___x_900_ = v___x_893_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
else
{
lean_object* v___x_902_; 
lean_del_object(v___x_893_);
v___x_902_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_878_, v___y_879_, v___y_880_);
return v___x_902_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v___y_878_);
v_a_904_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_890_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_890_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
v___jp_912_:
{
lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___x_930_; 
lean_inc(v___y_913_);
lean_inc_ref_n(v_c_847_, 2);
lean_inc_n(v___y_917_, 2);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_928_, 0, v___y_917_);
lean_closure_set(v___f_928_, 1, v_c_847_);
lean_closure_set(v___f_928_, 2, v___y_913_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(v___f_929_, 0, v___y_917_);
lean_closure_set(v___f_929_, 1, v_c_847_);
lean_closure_set(v___f_929_, 2, v___y_913_);
v___x_930_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
lean_dec_ref_known(v___x_930_, 1);
v___x_931_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_932_ = lean_int_dec_lt(v___y_915_, v___x_931_);
lean_dec(v___y_915_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___f_928_);
v___x_933_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_934_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_933_, v___f_929_, v___y_918_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref_known(v___x_934_, 1);
v___y_878_ = v___y_914_;
v___y_879_ = v___y_917_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_919_;
v___y_882_ = v___y_920_;
v___y_883_ = v___y_921_;
v___y_884_ = v___y_922_;
v___y_885_ = v___y_923_;
v___y_886_ = v___y_924_;
v___y_887_ = v___y_925_;
v___y_888_ = v___y_926_;
v___y_889_ = v___y_927_;
goto v___jp_877_;
}
else
{
lean_dec(v___y_914_);
lean_dec_ref(v_c_847_);
return v___x_934_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v___f_929_);
v___x_935_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_936_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_935_, v___f_928_, v___y_918_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_dec_ref_known(v___x_936_, 1);
v___y_878_ = v___y_914_;
v___y_879_ = v___y_917_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_919_;
v___y_882_ = v___y_920_;
v___y_883_ = v___y_921_;
v___y_884_ = v___y_922_;
v___y_885_ = v___y_923_;
v___y_886_ = v___y_924_;
v___y_887_ = v___y_925_;
v___y_888_ = v___y_926_;
v___y_889_ = v___y_927_;
goto v___jp_877_;
}
else
{
lean_dec(v___y_914_);
lean_dec_ref(v_c_847_);
return v___x_936_;
}
}
}
else
{
lean_dec_ref(v___f_929_);
lean_dec_ref(v___f_928_);
lean_dec(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_c_847_);
return v___x_930_;
}
}
v___jp_941_:
{
lean_object* v_p_953_; 
v_p_953_ = lean_ctor_get(v_c_847_, 0);
if (lean_obj_tag(v_p_953_) == 0)
{
uint8_t v_strict_954_; 
v_strict_954_ = lean_ctor_get_uint8(v_c_847_, sizeof(void*)*2);
if (v_strict_954_ == 0)
{
lean_object* v_toCold_955_; lean_object* v_options_956_; uint8_t v_hasTrace_957_; 
v_toCold_955_ = lean_ctor_get(v___y_951_, 0);
v_options_956_ = lean_ctor_get(v_toCold_955_, 2);
v_hasTrace_957_ = lean_ctor_get_uint8(v_options_956_, sizeof(void*)*1);
if (v_hasTrace_957_ == 0)
{
lean_dec_ref(v_c_847_);
goto v___jp_860_;
}
else
{
lean_object* v_inheritedTraceOptions_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_inheritedTraceOptions_958_ = lean_ctor_get(v_toCold_955_, 11);
v___x_959_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_960_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_961_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_958_, v_options_956_, v___x_960_);
if (v___x_961_ == 0)
{
lean_dec_ref(v_c_847_);
goto v___jp_860_;
}
else
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_847_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec_ref(v_c_847_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = l_Lean_MessageData_ofExpr(v_a_963_);
v___x_965_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_959_, v___x_964_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
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
else
{
lean_object* v_toCold_974_; lean_object* v_options_975_; uint8_t v_hasTrace_976_; 
v_toCold_974_ = lean_ctor_get(v___y_951_, 0);
v_options_975_ = lean_ctor_get(v_toCold_974_, 2);
v_hasTrace_976_ = lean_ctor_get_uint8(v_options_975_, sizeof(void*)*1);
if (v_hasTrace_976_ == 0)
{
v___y_864_ = v___y_942_;
v___y_865_ = v___y_943_;
v___y_866_ = v___y_944_;
v___y_867_ = v___y_945_;
v___y_868_ = v___y_946_;
v___y_869_ = v___y_947_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_949_;
v___y_872_ = v___y_950_;
v___y_873_ = v___y_951_;
v___y_874_ = v___y_952_;
goto v___jp_863_;
}
else
{
lean_object* v_inheritedTraceOptions_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_inheritedTraceOptions_977_ = lean_ctor_get(v_toCold_974_, 11);
v___x_978_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_979_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_977_, v_options_975_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_864_ = v___y_942_;
v___y_865_ = v___y_943_;
v___y_866_ = v___y_944_;
v___y_867_ = v___y_945_;
v___y_868_ = v___y_946_;
v___y_869_ = v___y_947_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_949_;
v___y_872_ = v___y_950_;
v___y_873_ = v___y_951_;
v___y_874_ = v___y_952_;
goto v___jp_863_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_847_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_MessageData_ofExpr(v_a_982_);
v___x_984_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_978_, v___x_983_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v___y_864_ = v___y_942_;
v___y_865_ = v___y_943_;
v___y_866_ = v___y_944_;
v___y_867_ = v___y_945_;
v___y_868_ = v___y_946_;
v___y_869_ = v___y_947_;
v___y_870_ = v___y_948_;
v___y_871_ = v___y_949_;
v___y_872_ = v___y_950_;
v___y_873_ = v___y_951_;
v___y_874_ = v___y_952_;
goto v___jp_863_;
}
else
{
lean_dec_ref(v_c_847_);
return v___x_984_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_c_847_);
v_a_985_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_981_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_981_);
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
}
}
}
else
{
lean_object* v_toCold_993_; lean_object* v_options_994_; uint8_t v_hasTrace_995_; 
v_toCold_993_ = lean_ctor_get(v___y_951_, 0);
v_options_994_ = lean_ctor_get(v_toCold_993_, 2);
v_hasTrace_995_ = lean_ctor_get_uint8(v_options_994_, sizeof(void*)*1);
if (v_hasTrace_995_ == 0)
{
lean_object* v_k_996_; lean_object* v_v_997_; 
v_k_996_ = lean_ctor_get(v_p_953_, 0);
v_v_997_ = lean_ctor_get(v_p_953_, 1);
lean_inc_ref(v_p_953_);
lean_inc(v_k_996_);
lean_inc_n(v_v_997_, 2);
v___y_913_ = v_v_997_;
v___y_914_ = v_v_997_;
v___y_915_ = v_k_996_;
v___y_916_ = v_p_953_;
v___y_917_ = v___y_942_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
v___y_921_ = v___y_946_;
v___y_922_ = v___y_947_;
v___y_923_ = v___y_948_;
v___y_924_ = v___y_949_;
v___y_925_ = v___y_950_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_952_;
goto v___jp_912_;
}
else
{
lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v_inheritedTraceOptions_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_k_998_ = lean_ctor_get(v_p_953_, 0);
v_v_999_ = lean_ctor_get(v_p_953_, 1);
v_inheritedTraceOptions_1000_ = lean_ctor_get(v_toCold_993_, 11);
v___x_1001_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_1002_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_1003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1000_, v_options_994_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_inc_ref(v_p_953_);
lean_inc(v_k_998_);
lean_inc_n(v_v_999_, 2);
v___y_913_ = v_v_999_;
v___y_914_ = v_v_999_;
v___y_915_ = v_k_998_;
v___y_916_ = v_p_953_;
v___y_917_ = v___y_942_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
v___y_921_ = v___y_946_;
v___y_922_ = v___y_947_;
v___y_923_ = v___y_948_;
v___y_924_ = v___y_949_;
v___y_925_ = v___y_950_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_952_;
goto v___jp_912_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_847_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = l_Lean_MessageData_ofExpr(v_a_1005_);
v___x_1007_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_1001_, v___x_1006_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_dec_ref_known(v___x_1007_, 1);
lean_inc_ref(v_p_953_);
lean_inc(v_k_998_);
lean_inc_n(v_v_999_, 2);
v___y_913_ = v_v_999_;
v___y_914_ = v_v_999_;
v___y_915_ = v_k_998_;
v___y_916_ = v_p_953_;
v___y_917_ = v___y_942_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
v___y_921_ = v___y_946_;
v___y_922_ = v___y_947_;
v___y_923_ = v___y_948_;
v___y_924_ = v___y_949_;
v___y_925_ = v___y_950_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_952_;
goto v___jp_912_;
}
else
{
lean_dec_ref(v_c_847_);
return v___x_1007_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_c_847_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_847_ = stack[0].m_obj;
lean_object* v_a_848_ = stack[1].m_obj;
lean_object* v_a_849_ = stack[2].m_obj;
lean_object* v_a_850_ = stack[3].m_obj;
lean_object* v_a_851_ = stack[4].m_obj;
lean_object* v_a_852_ = stack[5].m_obj;
lean_object* v_a_853_ = stack[6].m_obj;
lean_object* v_a_854_ = stack[7].m_obj;
lean_object* v_a_855_ = stack[8].m_obj;
lean_object* v_a_856_ = stack[9].m_obj;
lean_object* v_a_857_ = stack[10].m_obj;
lean_object* v_a_858_ = stack[11].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec(v_a_1033_);
return v_res_1045_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1046_, v_msg_1047_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1046_ = stack[0].m_obj;
lean_object* v_msg_1047_ = stack[1].m_obj;
lean_object* v___y_1048_ = stack[2].m_obj;
lean_object* v___y_1049_ = stack[3].m_obj;
lean_object* v___y_1050_ = stack[4].m_obj;
lean_object* v___y_1051_ = stack[5].m_obj;
lean_object* v___y_1052_ = stack[6].m_obj;
lean_object* v___y_1053_ = stack[7].m_obj;
lean_object* v___y_1054_ = stack[8].m_obj;
lean_object* v___y_1055_ = stack[9].m_obj;
lean_object* v___y_1056_ = stack[10].m_obj;
lean_object* v___y_1057_ = stack[11].m_obj;
lean_object* v___y_1058_ = stack[12].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1062_, lean_object* v_msg_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1062_, v_msg_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
return v_res_1076_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1078_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1078_ = stack[1].m_obj;
lean_object* v___y_1079_ = stack[2].m_obj;
lean_object* v___y_1080_ = stack[3].m_obj;
lean_object* v___y_1081_ = stack[4].m_obj;
lean_object* v___y_1082_ = stack[5].m_obj;
lean_object* v___y_1083_ = stack[6].m_obj;
lean_object* v___y_1084_ = stack[7].m_obj;
lean_object* v___y_1085_ = stack[8].m_obj;
lean_object* v___y_1086_ = stack[9].m_obj;
lean_object* v___y_1087_ = stack[10].m_obj;
lean_object* v___y_1088_ = stack[11].m_obj;
lean_object* v___y_1089_ = stack[12].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_box(0), v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1093_, v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v___y_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1108_, lean_object* v_e_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v_structs_1111_; lean_object* v_typeIdOf_1112_; lean_object* v_exprToStructId_1113_; lean_object* v_exprToStructIdEntries_1114_; lean_object* v_forbiddenNatModules_1115_; lean_object* v_natStructs_1116_; lean_object* v_natTypeIdOf_1117_; lean_object* v_exprToNatStructId_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_structs_1111_ = lean_ctor_get(v_s_1110_, 0);
v_typeIdOf_1112_ = lean_ctor_get(v_s_1110_, 1);
v_exprToStructId_1113_ = lean_ctor_get(v_s_1110_, 2);
v_exprToStructIdEntries_1114_ = lean_ctor_get(v_s_1110_, 3);
v_forbiddenNatModules_1115_ = lean_ctor_get(v_s_1110_, 4);
v_natStructs_1116_ = lean_ctor_get(v_s_1110_, 5);
v_natTypeIdOf_1117_ = lean_ctor_get(v_s_1110_, 6);
v_exprToNatStructId_1118_ = lean_ctor_get(v_s_1110_, 7);
v___x_1119_ = lean_array_get_size(v_structs_1111_);
v___x_1120_ = lean_nat_dec_lt(v_a_1108_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v_e_1109_);
return v_s_1110_;
}
else
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1182_; 
lean_inc_ref(v_exprToNatStructId_1118_);
lean_inc_ref(v_natTypeIdOf_1117_);
lean_inc_ref(v_natStructs_1116_);
lean_inc_ref(v_forbiddenNatModules_1115_);
lean_inc_ref(v_exprToStructIdEntries_1114_);
lean_inc_ref(v_exprToStructId_1113_);
lean_inc_ref(v_typeIdOf_1112_);
lean_inc_ref(v_structs_1111_);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_s_1110_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1183_ = lean_ctor_get(v_s_1110_, 7);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_s_1110_, 6);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_s_1110_, 5);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_s_1110_, 4);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_s_1110_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_s_1110_, 2);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_s_1110_, 1);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_s_1110_, 0);
lean_dec(v_unused_1190_);
v___x_1122_ = v_s_1110_;
v_isShared_1123_ = v_isSharedCheck_1182_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_s_1110_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1182_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_v_1124_; lean_object* v_id_1125_; lean_object* v_ringId_x3f_1126_; lean_object* v_type_1127_; lean_object* v_u_1128_; lean_object* v_intModuleInst_1129_; lean_object* v_leInst_x3f_1130_; lean_object* v_ltInst_x3f_1131_; lean_object* v_lawfulOrderLTInst_x3f_1132_; lean_object* v_isPreorderInst_x3f_1133_; lean_object* v_orderedAddInst_x3f_1134_; lean_object* v_isLinearInst_x3f_1135_; lean_object* v_noNatDivInst_x3f_1136_; lean_object* v_ringInst_x3f_1137_; lean_object* v_commRingInst_x3f_1138_; lean_object* v_orderedRingInst_x3f_1139_; lean_object* v_fieldInst_x3f_1140_; lean_object* v_charInst_x3f_1141_; lean_object* v_zero_1142_; lean_object* v_ofNatZero_1143_; lean_object* v_one_x3f_1144_; lean_object* v_leFn_x3f_1145_; lean_object* v_ltFn_x3f_1146_; lean_object* v_addFn_1147_; lean_object* v_zsmulFn_1148_; lean_object* v_nsmulFn_1149_; lean_object* v_zsmulFn_x3f_1150_; lean_object* v_nsmulFn_x3f_1151_; lean_object* v_homomulFn_x3f_1152_; lean_object* v_subFn_1153_; lean_object* v_negFn_1154_; lean_object* v_vars_1155_; lean_object* v_varMap_1156_; lean_object* v_lowers_1157_; lean_object* v_uppers_1158_; lean_object* v_diseqs_1159_; lean_object* v_assignment_1160_; uint8_t v_caseSplits_1161_; lean_object* v_conflict_x3f_1162_; lean_object* v_diseqSplits_1163_; lean_object* v_elimEqs_1164_; lean_object* v_elimStack_1165_; lean_object* v_occurs_1166_; lean_object* v_ignored_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1181_; 
v_v_1124_ = lean_array_fget(v_structs_1111_, v_a_1108_);
v_id_1125_ = lean_ctor_get(v_v_1124_, 0);
v_ringId_x3f_1126_ = lean_ctor_get(v_v_1124_, 1);
v_type_1127_ = lean_ctor_get(v_v_1124_, 2);
v_u_1128_ = lean_ctor_get(v_v_1124_, 3);
v_intModuleInst_1129_ = lean_ctor_get(v_v_1124_, 4);
v_leInst_x3f_1130_ = lean_ctor_get(v_v_1124_, 5);
v_ltInst_x3f_1131_ = lean_ctor_get(v_v_1124_, 6);
v_lawfulOrderLTInst_x3f_1132_ = lean_ctor_get(v_v_1124_, 7);
v_isPreorderInst_x3f_1133_ = lean_ctor_get(v_v_1124_, 8);
v_orderedAddInst_x3f_1134_ = lean_ctor_get(v_v_1124_, 9);
v_isLinearInst_x3f_1135_ = lean_ctor_get(v_v_1124_, 10);
v_noNatDivInst_x3f_1136_ = lean_ctor_get(v_v_1124_, 11);
v_ringInst_x3f_1137_ = lean_ctor_get(v_v_1124_, 12);
v_commRingInst_x3f_1138_ = lean_ctor_get(v_v_1124_, 13);
v_orderedRingInst_x3f_1139_ = lean_ctor_get(v_v_1124_, 14);
v_fieldInst_x3f_1140_ = lean_ctor_get(v_v_1124_, 15);
v_charInst_x3f_1141_ = lean_ctor_get(v_v_1124_, 16);
v_zero_1142_ = lean_ctor_get(v_v_1124_, 17);
v_ofNatZero_1143_ = lean_ctor_get(v_v_1124_, 18);
v_one_x3f_1144_ = lean_ctor_get(v_v_1124_, 19);
v_leFn_x3f_1145_ = lean_ctor_get(v_v_1124_, 20);
v_ltFn_x3f_1146_ = lean_ctor_get(v_v_1124_, 21);
v_addFn_1147_ = lean_ctor_get(v_v_1124_, 22);
v_zsmulFn_1148_ = lean_ctor_get(v_v_1124_, 23);
v_nsmulFn_1149_ = lean_ctor_get(v_v_1124_, 24);
v_zsmulFn_x3f_1150_ = lean_ctor_get(v_v_1124_, 25);
v_nsmulFn_x3f_1151_ = lean_ctor_get(v_v_1124_, 26);
v_homomulFn_x3f_1152_ = lean_ctor_get(v_v_1124_, 27);
v_subFn_1153_ = lean_ctor_get(v_v_1124_, 28);
v_negFn_1154_ = lean_ctor_get(v_v_1124_, 29);
v_vars_1155_ = lean_ctor_get(v_v_1124_, 30);
v_varMap_1156_ = lean_ctor_get(v_v_1124_, 31);
v_lowers_1157_ = lean_ctor_get(v_v_1124_, 32);
v_uppers_1158_ = lean_ctor_get(v_v_1124_, 33);
v_diseqs_1159_ = lean_ctor_get(v_v_1124_, 34);
v_assignment_1160_ = lean_ctor_get(v_v_1124_, 35);
v_caseSplits_1161_ = lean_ctor_get_uint8(v_v_1124_, sizeof(void*)*42);
v_conflict_x3f_1162_ = lean_ctor_get(v_v_1124_, 36);
v_diseqSplits_1163_ = lean_ctor_get(v_v_1124_, 37);
v_elimEqs_1164_ = lean_ctor_get(v_v_1124_, 38);
v_elimStack_1165_ = lean_ctor_get(v_v_1124_, 39);
v_occurs_1166_ = lean_ctor_get(v_v_1124_, 40);
v_ignored_1167_ = lean_ctor_get(v_v_1124_, 41);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_v_1124_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1169_ = v_v_1124_;
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_ignored_1167_);
lean_inc(v_occurs_1166_);
lean_inc(v_elimStack_1165_);
lean_inc(v_elimEqs_1164_);
lean_inc(v_diseqSplits_1163_);
lean_inc(v_conflict_x3f_1162_);
lean_inc(v_assignment_1160_);
lean_inc(v_diseqs_1159_);
lean_inc(v_uppers_1158_);
lean_inc(v_lowers_1157_);
lean_inc(v_varMap_1156_);
lean_inc(v_vars_1155_);
lean_inc(v_negFn_1154_);
lean_inc(v_subFn_1153_);
lean_inc(v_homomulFn_x3f_1152_);
lean_inc(v_nsmulFn_x3f_1151_);
lean_inc(v_zsmulFn_x3f_1150_);
lean_inc(v_nsmulFn_1149_);
lean_inc(v_zsmulFn_1148_);
lean_inc(v_addFn_1147_);
lean_inc(v_ltFn_x3f_1146_);
lean_inc(v_leFn_x3f_1145_);
lean_inc(v_one_x3f_1144_);
lean_inc(v_ofNatZero_1143_);
lean_inc(v_zero_1142_);
lean_inc(v_charInst_x3f_1141_);
lean_inc(v_fieldInst_x3f_1140_);
lean_inc(v_orderedRingInst_x3f_1139_);
lean_inc(v_commRingInst_x3f_1138_);
lean_inc(v_ringInst_x3f_1137_);
lean_inc(v_noNatDivInst_x3f_1136_);
lean_inc(v_isLinearInst_x3f_1135_);
lean_inc(v_orderedAddInst_x3f_1134_);
lean_inc(v_isPreorderInst_x3f_1133_);
lean_inc(v_lawfulOrderLTInst_x3f_1132_);
lean_inc(v_ltInst_x3f_1131_);
lean_inc(v_leInst_x3f_1130_);
lean_inc(v_intModuleInst_1129_);
lean_inc(v_u_1128_);
lean_inc(v_type_1127_);
lean_inc(v_ringId_x3f_1126_);
lean_inc(v_id_1125_);
lean_dec(v_v_1124_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v_xs_x27_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1171_ = lean_box(0);
v_xs_x27_1172_ = lean_array_fset(v_structs_1111_, v_a_1108_, v___x_1171_);
v___x_1173_ = l_Lean_PersistentArray_push___redArg(v_ignored_1167_, v_e_1109_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 41, v___x_1173_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_id_1125_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_ringId_x3f_1126_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_type_1127_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_u_1128_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_intModuleInst_1129_);
lean_ctor_set(v_reuseFailAlloc_1180_, 5, v_leInst_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1180_, 6, v_ltInst_x3f_1131_);
lean_ctor_set(v_reuseFailAlloc_1180_, 7, v_lawfulOrderLTInst_x3f_1132_);
lean_ctor_set(v_reuseFailAlloc_1180_, 8, v_isPreorderInst_x3f_1133_);
lean_ctor_set(v_reuseFailAlloc_1180_, 9, v_orderedAddInst_x3f_1134_);
lean_ctor_set(v_reuseFailAlloc_1180_, 10, v_isLinearInst_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1180_, 11, v_noNatDivInst_x3f_1136_);
lean_ctor_set(v_reuseFailAlloc_1180_, 12, v_ringInst_x3f_1137_);
lean_ctor_set(v_reuseFailAlloc_1180_, 13, v_commRingInst_x3f_1138_);
lean_ctor_set(v_reuseFailAlloc_1180_, 14, v_orderedRingInst_x3f_1139_);
lean_ctor_set(v_reuseFailAlloc_1180_, 15, v_fieldInst_x3f_1140_);
lean_ctor_set(v_reuseFailAlloc_1180_, 16, v_charInst_x3f_1141_);
lean_ctor_set(v_reuseFailAlloc_1180_, 17, v_zero_1142_);
lean_ctor_set(v_reuseFailAlloc_1180_, 18, v_ofNatZero_1143_);
lean_ctor_set(v_reuseFailAlloc_1180_, 19, v_one_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1180_, 20, v_leFn_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1180_, 21, v_ltFn_x3f_1146_);
lean_ctor_set(v_reuseFailAlloc_1180_, 22, v_addFn_1147_);
lean_ctor_set(v_reuseFailAlloc_1180_, 23, v_zsmulFn_1148_);
lean_ctor_set(v_reuseFailAlloc_1180_, 24, v_nsmulFn_1149_);
lean_ctor_set(v_reuseFailAlloc_1180_, 25, v_zsmulFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1180_, 26, v_nsmulFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1180_, 27, v_homomulFn_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1180_, 28, v_subFn_1153_);
lean_ctor_set(v_reuseFailAlloc_1180_, 29, v_negFn_1154_);
lean_ctor_set(v_reuseFailAlloc_1180_, 30, v_vars_1155_);
lean_ctor_set(v_reuseFailAlloc_1180_, 31, v_varMap_1156_);
lean_ctor_set(v_reuseFailAlloc_1180_, 32, v_lowers_1157_);
lean_ctor_set(v_reuseFailAlloc_1180_, 33, v_uppers_1158_);
lean_ctor_set(v_reuseFailAlloc_1180_, 34, v_diseqs_1159_);
lean_ctor_set(v_reuseFailAlloc_1180_, 35, v_assignment_1160_);
lean_ctor_set(v_reuseFailAlloc_1180_, 36, v_conflict_x3f_1162_);
lean_ctor_set(v_reuseFailAlloc_1180_, 37, v_diseqSplits_1163_);
lean_ctor_set(v_reuseFailAlloc_1180_, 38, v_elimEqs_1164_);
lean_ctor_set(v_reuseFailAlloc_1180_, 39, v_elimStack_1165_);
lean_ctor_set(v_reuseFailAlloc_1180_, 40, v_occurs_1166_);
lean_ctor_set(v_reuseFailAlloc_1180_, 41, v___x_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*42, v_caseSplits_1161_);
v___x_1175_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_array_fset(v_xs_x27_1172_, v_a_1108_, v___x_1175_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1176_);
v___x_1178_ = v___x_1122_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_typeIdOf_1112_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_exprToStructId_1113_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_exprToStructIdEntries_1114_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_forbiddenNatModules_1115_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_natStructs_1116_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_natTypeIdOf_1117_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_exprToNatStructId_1118_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1191_, lean_object* v_e_1192_, lean_object* v_s_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1191_, v_e_1192_, v_s_1193_);
lean_dec(v_a_1191_);
return v_res_1194_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1195_, lean_object* v_lhs_1196_, lean_object* v_rhs_1197_, uint8_t v_strict_1198_, uint8_t v_eqTrue_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___f_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc_ref(v_e_1195_);
lean_inc(v_a_1200_);
v___f_1212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1212_, 0, v_a_1200_);
lean_closure_set(v___f_1212_, 1, v_e_1195_);
v___x_1213_ = 0;
v___x_1214_ = lean_box(v___x_1213_);
v___x_1215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_1215_, 0, v_lhs_1196_);
lean_closure_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1215_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1370_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1370_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1370_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
if (lean_obj_tag(v_a_1217_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_del_object(v___x_1219_);
v_val_1221_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v_a_1217_, 1);
v___x_1222_ = lean_box(v___x_1213_);
v___x_1223_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_1223_, 0, v_rhs_1197_);
lean_closure_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1223_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1357_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1357_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1357_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
if (lean_obj_tag(v_a_1225_) == 1)
{
lean_object* v_val_1229_; lean_object* v___x_1230_; 
lean_del_object(v___x_1227_);
v_val_1229_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v_a_1225_, 1);
v___x_1230_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1195_, v_a_1201_);
if (lean_obj_tag(v___x_1230_) == 0)
{
if (v_eqTrue_1199_ == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; uint8_t v___x_1234_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = lean_unbox(v_a_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_a_1233_);
lean_dec(v_a_1231_);
lean_dec(v_val_1229_);
lean_dec(v_val_1221_);
lean_dec_ref(v_e_1195_);
v___x_1235_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1236_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1235_, v___f_1212_, v_a_1201_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___y_1240_; 
lean_dec_ref(v___f_1212_);
lean_inc(v_val_1221_);
lean_inc(v_val_1229_);
v___x_1237_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_val_1229_);
lean_ctor_set(v___x_1237_, 1, v_val_1221_);
v___x_1238_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1237_);
if (v_strict_1198_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
v___y_1240_ = v___x_1287_;
goto v___jp_1239_;
}
else
{
lean_dec(v_a_1233_);
v___y_1240_ = v_eqTrue_1199_;
goto v___jp_1239_;
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1241_, 0, v_e_1195_);
lean_ctor_set(v___x_1241_, 1, v_val_1221_);
lean_ctor_set(v___x_1241_, 2, v_val_1229_);
v___x_1242_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*2, v___y_1240_);
v___x_1243_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1242_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_p_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v_p_1245_ = lean_ctor_get(v_a_1244_, 0);
lean_inc_ref(v_p_1245_);
v___x_1246_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1245_, v_a_1231_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1247_, v___x_1213_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1262_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1262_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1262_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
if (lean_obj_tag(v_a_1249_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1251_);
v_val_1253_ = lean_ctor_get(v_a_1249_, 0);
lean_inc_n(v_val_1253_, 2);
lean_dec_ref_known(v_a_1249_, 1);
v___x_1254_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1253_);
v___x_1255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_a_1244_);
lean_ctor_set(v___x_1255_, 1, v_val_1253_);
v___x_1256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*2, v___y_1240_);
v___x_1257_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1256_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_a_1249_);
lean_dec(v_a_1244_);
v___x_1258_ = lean_box(0);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1258_);
v___x_1260_ = v___x_1251_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_a_1244_);
v_a_1263_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1248_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1248_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_a_1244_);
v_a_1271_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1246_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1246_);
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
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_a_1231_);
v_a_1279_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1243_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1243_);
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
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1231_);
lean_dec(v_val_1229_);
lean_dec(v_val_1221_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_e_1195_);
v_a_1288_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1232_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1232_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v___f_1212_);
v_a_1296_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1230_, 1);
lean_inc(v_val_1229_);
lean_inc(v_val_1221_);
v___x_1297_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_val_1221_);
lean_ctor_set(v___x_1297_, 1, v_val_1229_);
v___x_1298_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_e_1195_);
lean_ctor_set(v___x_1299_, 1, v_val_1221_);
lean_ctor_set(v___x_1299_, 2, v_val_1229_);
v___x_1300_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*2, v_strict_1198_);
v___x_1301_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1300_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_p_1303_; lean_object* v___x_1304_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_p_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_p_1303_);
v___x_1304_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1303_, v_a_1296_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1305_, v___x_1213_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1320_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
if (lean_obj_tag(v_a_1307_) == 1)
{
lean_object* v_val_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_del_object(v___x_1309_);
v_val_1311_ = lean_ctor_get(v_a_1307_, 0);
lean_inc_n(v_val_1311_, 2);
lean_dec_ref_known(v_a_1307_, 1);
v___x_1312_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1311_);
v___x_1313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1302_);
lean_ctor_set(v___x_1313_, 1, v_val_1311_);
v___x_1314_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*2, v_strict_1198_);
v___x_1315_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1314_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v_a_1307_);
lean_dec(v_a_1302_);
v___x_1316_ = lean_box(0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1316_);
v___x_1318_ = v___x_1309_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_a_1302_);
v_a_1321_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1306_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1306_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1302_);
v_a_1329_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1304_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1304_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
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
lean_dec(v_a_1296_);
v_a_1337_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1301_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1301_);
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
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_val_1229_);
lean_dec(v_val_1221_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_e_1195_);
v_a_1345_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1230_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1230_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
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
lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_dec(v_a_1225_);
lean_dec(v_val_1221_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_e_1195_);
v___x_1353_ = lean_box(0);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1353_);
v___x_1355_ = v___x_1227_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
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
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_val_1221_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_e_1195_);
v_a_1358_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1224_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1224_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec(v_a_1217_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_rhs_1197_);
lean_dec_ref(v_e_1195_);
v___x_1366_ = lean_box(0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1366_);
v___x_1368_ = v___x_1219_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___f_1212_);
lean_dec_ref(v_rhs_1197_);
lean_dec_ref(v_e_1195_);
v_a_1371_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1216_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1216_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1195_ = stack[0].m_obj;
lean_object* v_lhs_1196_ = stack[1].m_obj;
lean_object* v_rhs_1197_ = stack[2].m_obj;
uint8_t v_strict_1198_ = stack[3].m_num;
uint8_t v_eqTrue_1199_ = stack[4].m_num;
lean_object* v_a_1200_ = stack[5].m_obj;
lean_object* v_a_1201_ = stack[6].m_obj;
lean_object* v_a_1202_ = stack[7].m_obj;
lean_object* v_a_1203_ = stack[8].m_obj;
lean_object* v_a_1204_ = stack[9].m_obj;
lean_object* v_a_1205_ = stack[10].m_obj;
lean_object* v_a_1206_ = stack[11].m_obj;
lean_object* v_a_1207_ = stack[12].m_obj;
lean_object* v_a_1208_ = stack[13].m_obj;
lean_object* v_a_1209_ = stack[14].m_obj;
lean_object* v_a_1210_ = stack[15].m_obj;
lean_object* v_res_1379_;
v_res_1379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1195_, v_lhs_1196_, v_rhs_1197_, v_strict_1198_, v_eqTrue_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
stack->m_obj
 = v_res_1379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1380_ = _args[0];
lean_object* v_lhs_1381_ = _args[1];
lean_object* v_rhs_1382_ = _args[2];
lean_object* v_strict_1383_ = _args[3];
lean_object* v_eqTrue_1384_ = _args[4];
lean_object* v_a_1385_ = _args[5];
lean_object* v_a_1386_ = _args[6];
lean_object* v_a_1387_ = _args[7];
lean_object* v_a_1388_ = _args[8];
lean_object* v_a_1389_ = _args[9];
lean_object* v_a_1390_ = _args[10];
lean_object* v_a_1391_ = _args[11];
lean_object* v_a_1392_ = _args[12];
lean_object* v_a_1393_ = _args[13];
lean_object* v_a_1394_ = _args[14];
lean_object* v_a_1395_ = _args[15];
lean_object* v_a_1396_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1397_; uint8_t v_eqTrue_boxed_1398_; lean_object* v_res_1399_; 
v_strict_boxed_1397_ = lean_unbox(v_strict_1383_);
v_eqTrue_boxed_1398_ = lean_unbox(v_eqTrue_1384_);
v_res_1399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1380_, v_lhs_1381_, v_rhs_1382_, v_strict_boxed_1397_, v_eqTrue_boxed_1398_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec(v_a_1385_);
return v_res_1399_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1400_, lean_object* v_lhs_1401_, lean_object* v_rhs_1402_, uint8_t v_strict_1403_, uint8_t v_eqTrue_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___f_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
lean_inc_ref(v_e_1400_);
lean_inc(v_a_1405_);
v___f_1417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1417_, 0, v_a_1405_);
lean_closure_set(v___f_1417_, 1, v_e_1400_);
v___x_1418_ = 0;
v___x_1419_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1401_, v___x_1418_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1475_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1475_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1475_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
if (lean_obj_tag(v_a_1420_) == 1)
{
lean_object* v_val_1424_; lean_object* v___x_1425_; 
lean_del_object(v___x_1422_);
v_val_1424_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v_a_1420_, 1);
v___x_1425_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1402_, v___x_1418_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1462_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1462_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1462_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_a_1426_) == 1)
{
lean_del_object(v___x_1428_);
if (v_eqTrue_1404_ == 0)
{
lean_object* v_val_1430_; lean_object* v___x_1431_; 
v_val_1430_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v_a_1426_, 1);
v___x_1431_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_unbox(v_a_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec(v_a_1432_);
lean_dec(v_val_1430_);
lean_dec(v_val_1424_);
lean_dec_ref(v_e_1400_);
v___x_1434_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1435_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1434_, v___f_1417_, v_a_1406_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___y_1439_; 
lean_dec_ref(v___f_1417_);
lean_inc(v_val_1424_);
lean_inc(v_val_1430_);
v___x_1436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_val_1430_);
lean_ctor_set(v___x_1436_, 1, v_val_1424_);
v___x_1437_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1436_);
if (v_strict_1403_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
v___y_1439_ = v___x_1443_;
goto v___jp_1438_;
}
else
{
lean_dec(v_a_1432_);
v___y_1439_ = v_eqTrue_1404_;
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1440_, 0, v_e_1400_);
lean_ctor_set(v___x_1440_, 1, v_val_1424_);
lean_ctor_set(v___x_1440_, 2, v_val_1430_);
v___x_1441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1437_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*2, v___y_1439_);
v___x_1442_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1441_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_val_1430_);
lean_dec(v_val_1424_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v_e_1400_);
v_a_1444_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1431_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1431_);
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
lean_object* v_val_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v___f_1417_);
v_val_1452_ = lean_ctor_get(v_a_1426_, 0);
lean_inc_n(v_val_1452_, 2);
lean_dec_ref_known(v_a_1426_, 1);
lean_inc(v_val_1424_);
v___x_1453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_val_1424_);
lean_ctor_set(v___x_1453_, 1, v_val_1452_);
v___x_1454_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1453_);
v___x_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1455_, 0, v_e_1400_);
lean_ctor_set(v___x_1455_, 1, v_val_1424_);
lean_ctor_set(v___x_1455_, 2, v_val_1452_);
v___x_1456_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*2, v_strict_1403_);
v___x_1457_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1456_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
return v___x_1457_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec(v_a_1426_);
lean_dec(v_val_1424_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v_e_1400_);
v___x_1458_ = lean_box(0);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1458_);
v___x_1460_ = v___x_1428_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
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
lean_dec(v_val_1424_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v_e_1400_);
v_a_1463_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1425_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1425_);
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
else
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_dec(v_a_1420_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v_rhs_1402_);
lean_dec_ref(v_e_1400_);
v___x_1471_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1471_);
v___x_1473_ = v___x_1422_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
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
lean_dec_ref(v___f_1417_);
lean_dec_ref(v_rhs_1402_);
lean_dec_ref(v_e_1400_);
v_a_1476_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1419_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1419_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1400_ = stack[0].m_obj;
lean_object* v_lhs_1401_ = stack[1].m_obj;
lean_object* v_rhs_1402_ = stack[2].m_obj;
uint8_t v_strict_1403_ = stack[3].m_num;
uint8_t v_eqTrue_1404_ = stack[4].m_num;
lean_object* v_a_1405_ = stack[5].m_obj;
lean_object* v_a_1406_ = stack[6].m_obj;
lean_object* v_a_1407_ = stack[7].m_obj;
lean_object* v_a_1408_ = stack[8].m_obj;
lean_object* v_a_1409_ = stack[9].m_obj;
lean_object* v_a_1410_ = stack[10].m_obj;
lean_object* v_a_1411_ = stack[11].m_obj;
lean_object* v_a_1412_ = stack[12].m_obj;
lean_object* v_a_1413_ = stack[13].m_obj;
lean_object* v_a_1414_ = stack[14].m_obj;
lean_object* v_a_1415_ = stack[15].m_obj;
lean_object* v_res_1484_;
v_res_1484_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1400_, v_lhs_1401_, v_rhs_1402_, v_strict_1403_, v_eqTrue_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
stack->m_obj
 = v_res_1484_;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1505_, lean_object* v_lhs_1506_, lean_object* v_rhs_1507_, uint8_t v_strict_1508_, uint8_t v_eqTrue_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
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
v___x_1527_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1507_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_fst_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1592_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v_fst_1529_ = lean_ctor_get(v_a_1528_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_a_1528_, 1);
lean_dec(v_unused_1593_);
v___x_1531_ = v_a_1528_;
v_isShared_1532_ = v_isSharedCheck_1592_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_fst_1529_);
lean_dec(v_a_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1592_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_id_1533_; lean_object* v_structId_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; 
v_id_1533_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_id_1533_);
v_structId_1534_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_structId_1534_);
lean_dec(v_a_1523_);
v___x_1535_ = 0;
v___x_1536_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1526_, v___x_1535_, v_structId_1534_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1583_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1583_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1583_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
if (lean_obj_tag(v_a_1537_) == 1)
{
lean_object* v_val_1541_; lean_object* v___x_1542_; 
lean_del_object(v___x_1539_);
v_val_1541_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v_a_1537_, 1);
v___x_1542_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1529_, v___x_1535_, v_structId_1534_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
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
if (v_eqTrue_1509_ == 0)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc_n(v_val_1547_, 2);
lean_dec_ref_known(v_a_1543_, 1);
lean_inc(v_val_1541_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 3);
lean_ctor_set(v___x_1531_, 1, v_val_1541_);
lean_ctor_set(v___x_1531_, 0, v_val_1547_);
v___x_1549_ = v___x_1531_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_val_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_val_1541_);
v___x_1549_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; uint8_t v___y_1552_; 
v___x_1550_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1549_);
if (v_strict_1508_ == 0)
{
uint8_t v___x_1556_; 
v___x_1556_ = 1;
v___y_1552_ = v___x_1556_;
goto v___jp_1551_;
}
else
{
v___y_1552_ = v_eqTrue_1509_;
goto v___jp_1551_;
}
v___jp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1553_, 0, v_e_1505_);
lean_ctor_set(v___x_1553_, 1, v_id_1533_);
lean_ctor_set(v___x_1553_, 2, v_val_1541_);
lean_ctor_set(v___x_1553_, 3, v_val_1547_);
v___x_1554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1550_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*2, v___y_1552_);
v___x_1555_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1554_, v_structId_1534_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_structId_1534_);
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
lean_inc(v_val_1541_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 3);
lean_ctor_set(v___x_1531_, 1, v_val_1558_);
lean_ctor_set(v___x_1531_, 0, v_val_1541_);
v___x_1560_ = v___x_1531_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_val_1541_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_val_1558_);
v___x_1560_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v_e_1505_);
lean_ctor_set(v___x_1562_, 1, v_id_1533_);
lean_ctor_set(v___x_1562_, 2, v_val_1541_);
lean_ctor_set(v___x_1562_, 3, v_val_1558_);
v___x_1563_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*2, v_strict_1508_);
v___x_1564_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1563_, v_structId_1534_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_structId_1534_);
return v___x_1564_;
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec(v_a_1543_);
lean_dec(v_val_1541_);
lean_dec(v_structId_1534_);
lean_dec(v_id_1533_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_e_1505_);
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
lean_dec(v_val_1541_);
lean_dec(v_structId_1534_);
lean_dec(v_id_1533_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_e_1505_);
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
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec(v_a_1537_);
lean_dec(v_structId_1534_);
lean_dec(v_id_1533_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_e_1505_);
v___x_1579_ = lean_box(0);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1579_);
v___x_1581_ = v___x_1539_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
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
lean_dec(v_structId_1534_);
lean_dec(v_id_1533_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1529_);
lean_dec_ref(v_e_1505_);
v_a_1584_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1536_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1536_);
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
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_fst_1526_);
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1505_);
v_a_1594_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1527_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1527_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1523_);
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_e_1505_);
v_a_1602_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1524_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1524_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v_rhs_1507_);
lean_dec_ref(v_lhs_1506_);
lean_dec_ref(v_e_1505_);
v_a_1610_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1522_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1522_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1505_ = stack[0].m_obj;
lean_object* v_lhs_1506_ = stack[1].m_obj;
lean_object* v_rhs_1507_ = stack[2].m_obj;
uint8_t v_strict_1508_ = stack[3].m_num;
uint8_t v_eqTrue_1509_ = stack[4].m_num;
lean_object* v_a_1510_ = stack[5].m_obj;
lean_object* v_a_1511_ = stack[6].m_obj;
lean_object* v_a_1512_ = stack[7].m_obj;
lean_object* v_a_1513_ = stack[8].m_obj;
lean_object* v_a_1514_ = stack[9].m_obj;
lean_object* v_a_1515_ = stack[10].m_obj;
lean_object* v_a_1516_ = stack[11].m_obj;
lean_object* v_a_1517_ = stack[12].m_obj;
lean_object* v_a_1518_ = stack[13].m_obj;
lean_object* v_a_1519_ = stack[14].m_obj;
lean_object* v_a_1520_ = stack[15].m_obj;
lean_object* v_res_1618_;
v_res_1618_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1505_, v_lhs_1506_, v_rhs_1507_, v_strict_1508_, v_eqTrue_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
stack->m_obj
 = v_res_1618_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1619_ = _args[0];
lean_object* v_lhs_1620_ = _args[1];
lean_object* v_rhs_1621_ = _args[2];
lean_object* v_strict_1622_ = _args[3];
lean_object* v_eqTrue_1623_ = _args[4];
lean_object* v_a_1624_ = _args[5];
lean_object* v_a_1625_ = _args[6];
lean_object* v_a_1626_ = _args[7];
lean_object* v_a_1627_ = _args[8];
lean_object* v_a_1628_ = _args[9];
lean_object* v_a_1629_ = _args[10];
lean_object* v_a_1630_ = _args[11];
lean_object* v_a_1631_ = _args[12];
lean_object* v_a_1632_ = _args[13];
lean_object* v_a_1633_ = _args[14];
lean_object* v_a_1634_ = _args[15];
lean_object* v_a_1635_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1636_; uint8_t v_eqTrue_boxed_1637_; lean_object* v_res_1638_; 
v_strict_boxed_1636_ = lean_unbox(v_strict_1622_);
v_eqTrue_boxed_1637_ = lean_unbox(v_eqTrue_1623_);
v_res_1638_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1619_, v_lhs_1620_, v_rhs_1621_, v_strict_boxed_1636_, v_eqTrue_boxed_1637_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec(v_a_1624_);
return v_res_1638_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
if (lean_obj_tag(v_x_1640_) == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = 1;
return v___x_1641_;
}
else
{
uint8_t v___x_1642_; 
v___x_1642_ = 0;
return v___x_1642_;
}
}
else
{
if (lean_obj_tag(v_x_1640_) == 0)
{
uint8_t v___x_1643_; 
v___x_1643_ = 0;
return v___x_1643_;
}
else
{
lean_object* v_val_1644_; lean_object* v_val_1645_; uint8_t v___x_1646_; 
v_val_1644_ = lean_ctor_get(v_x_1639_, 0);
v_val_1645_ = lean_ctor_get(v_x_1640_, 0);
v___x_1646_ = lean_expr_eqv(v_val_1644_, v_val_1645_);
return v___x_1646_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1639_ = stack[0].m_obj;
lean_object* v_x_1640_ = stack[1].m_obj;
uint8_t v_res_1647_;
v_res_1647_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1639_, v_x_1640_);
stack->m_num = v_res_1647_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
uint8_t v_res_1650_; lean_object* v_r_1651_; 
v_res_1650_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1648_, v_x_1649_);
lean_dec(v_x_1649_);
lean_dec(v_x_1648_);
v_r_1651_ = lean_box(v_res_1650_);
return v_r_1651_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1652_, uint8_t v_eqTrue_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1656_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1859_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1859_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1859_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v_linarith_1670_; 
v_linarith_1670_ = lean_ctor_get_uint8(v_a_1666_, sizeof(void*)*14 + 22);
lean_dec(v_a_1666_);
if (v_linarith_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_dec_ref(v_e_1652_);
v___x_1671_ = lean_box(0);
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
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = l_Lean_Expr_getAppNumArgs(v_e_1652_);
v___x_1676_ = lean_unsigned_to_nat(4u);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec(v___x_1675_);
lean_dec_ref(v_e_1652_);
v___x_1678_ = lean_box(0);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1678_);
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v_strict_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___x_1721_; 
lean_del_object(v___x_1668_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_sub(v___x_1675_, v___x_1682_);
lean_inc(v___x_1683_);
v___x_1684_ = l_Lean_Expr_getRevArg_x21(v_e_1652_, v___x_1683_);
v___x_1685_ = lean_nat_sub(v___x_1683_, v___x_1682_);
lean_dec(v___x_1683_);
v___x_1686_ = l_Lean_Expr_getRevArg_x21(v_e_1652_, v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(2u);
v___x_1688_ = lean_nat_sub(v___x_1675_, v___x_1687_);
v___x_1689_ = lean_nat_sub(v___x_1688_, v___x_1682_);
lean_dec(v___x_1688_);
v___x_1690_ = l_Lean_Expr_getRevArg_x21(v_e_1652_, v___x_1689_);
v___x_1691_ = lean_unsigned_to_nat(3u);
v___x_1692_ = lean_nat_sub(v___x_1675_, v___x_1691_);
lean_dec(v___x_1675_);
v___x_1693_ = lean_nat_sub(v___x_1692_, v___x_1682_);
lean_dec(v___x_1692_);
v___x_1694_ = l_Lean_Expr_getRevArg_x21(v_e_1652_, v___x_1693_);
lean_inc_ref(v___x_1684_);
v___x_1721_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1684_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1850_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1850_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1850_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
if (lean_obj_tag(v_a_1722_) == 1)
{
lean_object* v_val_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1684_);
v_val_1726_ = lean_ctor_get(v_a_1722_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v_a_1722_, 1);
v___x_1727_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1726_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1741_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_leFn_x3f_1732_; lean_object* v_ltFn_x3f_1733_; uint8_t v___x_1734_; 
v_leFn_x3f_1732_ = lean_ctor_get(v_a_1728_, 20);
lean_inc(v_leFn_x3f_1732_);
v_ltFn_x3f_1733_ = lean_ctor_get(v_a_1728_, 21);
lean_inc(v_ltFn_x3f_1733_);
lean_dec(v_a_1728_);
v___x_1734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1732_, v___x_1686_);
lean_dec(v_leFn_x3f_1732_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1733_, v___x_1686_);
lean_dec_ref(v___x_1686_);
lean_dec(v_ltFn_x3f_1733_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec(v_val_1726_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_e_1652_);
v___x_1736_ = lean_box(0);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1736_);
v___x_1738_ = v___x_1730_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_del_object(v___x_1730_);
v_strict_1696_ = v___x_1677_;
v___y_1697_ = v_val_1726_;
v___y_1698_ = v_a_1654_;
v___y_1699_ = v_a_1655_;
v___y_1700_ = v_a_1656_;
v___y_1701_ = v_a_1657_;
v___y_1702_ = v_a_1658_;
v___y_1703_ = v_a_1659_;
v___y_1704_ = v_a_1660_;
v___y_1705_ = v_a_1661_;
v___y_1706_ = v_a_1662_;
v___y_1707_ = v_a_1663_;
goto v___jp_1695_;
}
}
else
{
uint8_t v___x_1740_; 
lean_dec(v_ltFn_x3f_1733_);
lean_del_object(v___x_1730_);
lean_dec_ref(v___x_1686_);
v___x_1740_ = 0;
v_strict_1696_ = v___x_1740_;
v___y_1697_ = v_val_1726_;
v___y_1698_ = v_a_1654_;
v___y_1699_ = v_a_1655_;
v___y_1700_ = v_a_1656_;
v___y_1701_ = v_a_1657_;
v___y_1702_ = v_a_1658_;
v___y_1703_ = v_a_1659_;
v___y_1704_ = v_a_1660_;
v___y_1705_ = v_a_1661_;
v___y_1706_ = v_a_1662_;
v___y_1707_ = v_a_1663_;
goto v___jp_1695_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_val_1726_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
v_a_1742_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1727_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1727_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1750_; 
lean_dec(v_a_1722_);
v___x_1750_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1684_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1841_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1841_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1841_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
if (lean_obj_tag(v_a_1751_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1756_; 
v_val_1755_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_val_1755_);
lean_dec_ref_known(v_a_1751_, 1);
v___x_1756_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1755_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1828_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1828_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1828_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_leInst_x3f_1766_; lean_object* v_ltInst_x3f_1767_; lean_object* v_lawfulOrderLTInst_x3f_1768_; lean_object* v_isPreorderInst_x3f_1769_; lean_object* v_orderedAddInst_x3f_1770_; lean_object* v_isLinearInst_x3f_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; uint8_t v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; uint8_t v___y_1806_; uint8_t v___y_1826_; 
v_leInst_x3f_1766_ = lean_ctor_get(v_a_1757_, 5);
lean_inc(v_leInst_x3f_1766_);
v_ltInst_x3f_1767_ = lean_ctor_get(v_a_1757_, 6);
lean_inc(v_ltInst_x3f_1767_);
v_lawfulOrderLTInst_x3f_1768_ = lean_ctor_get(v_a_1757_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1768_);
v_isPreorderInst_x3f_1769_ = lean_ctor_get(v_a_1757_, 8);
lean_inc(v_isPreorderInst_x3f_1769_);
v_orderedAddInst_x3f_1770_ = lean_ctor_get(v_a_1757_, 9);
lean_inc(v_orderedAddInst_x3f_1770_);
v_isLinearInst_x3f_1771_ = lean_ctor_get(v_a_1757_, 10);
lean_inc(v_isLinearInst_x3f_1771_);
lean_dec(v_a_1757_);
if (lean_obj_tag(v_leInst_x3f_1766_) == 0)
{
lean_dec(v_isPreorderInst_x3f_1769_);
v___y_1826_ = v___x_1677_;
goto v___jp_1825_;
}
else
{
if (lean_obj_tag(v_isPreorderInst_x3f_1769_) == 0)
{
v___y_1826_ = v___x_1677_;
goto v___jp_1825_;
}
else
{
uint8_t v___x_1827_; 
lean_dec_ref_known(v_isPreorderInst_x3f_1769_, 1);
v___x_1827_ = 0;
v___y_1806_ = v___x_1827_;
goto v___jp_1805_;
}
}
v___jp_1761_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
v___jp_1772_:
{
if (lean_obj_tag(v_isLinearInst_x3f_1771_) == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v___y_1779_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_e_1652_);
v___x_1785_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1785_);
v___x_1787_ = v___x_1753_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref_known(v_isLinearInst_x3f_1771_, 1);
lean_del_object(v___x_1753_);
v___x_1789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1652_, v___x_1690_, v___x_1694_, v___y_1777_, v_eqTrue_1653_, v___y_1779_, v___y_1783_, v___y_1774_, v___y_1776_, v___y_1784_, v___y_1781_, v___y_1782_, v___y_1773_, v___y_1778_, v___y_1775_, v___y_1780_);
lean_dec(v___y_1779_);
return v___x_1789_;
}
}
v___jp_1790_:
{
if (v_eqTrue_1653_ == 0)
{
v___y_1773_ = v___y_1791_;
v___y_1774_ = v___y_1792_;
v___y_1775_ = v___y_1793_;
v___y_1776_ = v___y_1794_;
v___y_1777_ = v___y_1795_;
v___y_1778_ = v___y_1796_;
v___y_1779_ = v___y_1797_;
v___y_1780_ = v___y_1798_;
v___y_1781_ = v___y_1799_;
v___y_1782_ = v___y_1800_;
v___y_1783_ = v___y_1801_;
v___y_1784_ = v___y_1802_;
goto v___jp_1772_;
}
else
{
if (v___y_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec(v_isLinearInst_x3f_1771_);
lean_del_object(v___x_1753_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1652_, v___x_1690_, v___x_1694_, v___y_1795_, v_eqTrue_1653_, v___y_1797_, v___y_1801_, v___y_1792_, v___y_1794_, v___y_1802_, v___y_1799_, v___y_1800_, v___y_1791_, v___y_1796_, v___y_1793_, v___y_1798_);
lean_dec(v___y_1797_);
return v___x_1804_;
}
else
{
v___y_1773_ = v___y_1791_;
v___y_1774_ = v___y_1792_;
v___y_1775_ = v___y_1793_;
v___y_1776_ = v___y_1794_;
v___y_1777_ = v___y_1795_;
v___y_1778_ = v___y_1796_;
v___y_1779_ = v___y_1797_;
v___y_1780_ = v___y_1798_;
v___y_1781_ = v___y_1799_;
v___y_1782_ = v___y_1800_;
v___y_1783_ = v___y_1801_;
v___y_1784_ = v___y_1802_;
goto v___jp_1772_;
}
}
}
v___jp_1805_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1770_) == 0)
{
lean_dec(v_isLinearInst_x3f_1771_);
lean_dec(v_lawfulOrderLTInst_x3f_1768_);
lean_dec(v_ltInst_x3f_1767_);
lean_dec(v_leInst_x3f_1766_);
lean_dec(v_val_1755_);
lean_del_object(v___x_1753_);
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
goto v___jp_1761_;
}
else
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1823_; 
lean_del_object(v___x_1759_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_orderedAddInst_x3f_1770_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_orderedAddInst_x3f_1770_, 0);
lean_dec(v_unused_1824_);
v___x_1808_ = v_orderedAddInst_x3f_1770_;
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v_orderedAddInst_x3f_1770_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1686_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1686_);
v___x_1811_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
uint8_t v___x_1812_; 
v___x_1812_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1811_, v_leInst_x3f_1766_);
lean_dec(v_leInst_x3f_1766_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
v___x_1813_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1811_, v_ltInst_x3f_1767_);
lean_dec(v_ltInst_x3f_1767_);
lean_dec_ref(v___x_1811_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec(v_isLinearInst_x3f_1771_);
lean_dec(v_lawfulOrderLTInst_x3f_1768_);
lean_dec(v_val_1755_);
lean_del_object(v___x_1753_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_e_1652_);
v___x_1814_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1814_);
v___x_1816_ = v___x_1724_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
else
{
if (v___x_1677_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1768_);
lean_del_object(v___x_1724_);
v___y_1791_ = v_a_1660_;
v___y_1792_ = v_a_1655_;
v___y_1793_ = v_a_1662_;
v___y_1794_ = v_a_1656_;
v___y_1795_ = v___x_1677_;
v___y_1796_ = v_a_1661_;
v___y_1797_ = v_val_1755_;
v___y_1798_ = v_a_1663_;
v___y_1799_ = v_a_1658_;
v___y_1800_ = v_a_1659_;
v___y_1801_ = v_a_1654_;
v___y_1802_ = v_a_1657_;
v___y_1803_ = v___y_1806_;
goto v___jp_1790_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1768_) == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_dec(v_isLinearInst_x3f_1771_);
lean_dec(v_val_1755_);
lean_del_object(v___x_1753_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_e_1652_);
v___x_1818_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1818_);
v___x_1820_ = v___x_1724_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1768_, 1);
lean_del_object(v___x_1724_);
v___y_1791_ = v_a_1660_;
v___y_1792_ = v_a_1655_;
v___y_1793_ = v_a_1662_;
v___y_1794_ = v_a_1656_;
v___y_1795_ = v___x_1677_;
v___y_1796_ = v_a_1661_;
v___y_1797_ = v_val_1755_;
v___y_1798_ = v_a_1663_;
v___y_1799_ = v_a_1658_;
v___y_1800_ = v_a_1659_;
v___y_1801_ = v_a_1654_;
v___y_1802_ = v_a_1657_;
v___y_1803_ = v___y_1806_;
goto v___jp_1790_;
}
}
}
}
else
{
lean_dec_ref(v___x_1811_);
lean_dec(v_lawfulOrderLTInst_x3f_1768_);
lean_dec(v_ltInst_x3f_1767_);
lean_del_object(v___x_1724_);
v___y_1791_ = v_a_1660_;
v___y_1792_ = v_a_1655_;
v___y_1793_ = v_a_1662_;
v___y_1794_ = v_a_1656_;
v___y_1795_ = v___y_1806_;
v___y_1796_ = v_a_1661_;
v___y_1797_ = v_val_1755_;
v___y_1798_ = v_a_1663_;
v___y_1799_ = v_a_1658_;
v___y_1800_ = v_a_1659_;
v___y_1801_ = v_a_1654_;
v___y_1802_ = v_a_1657_;
v___y_1803_ = v___y_1806_;
goto v___jp_1790_;
}
}
}
}
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
v___y_1806_ = v___y_1826_;
goto v___jp_1805_;
}
else
{
lean_dec(v_isLinearInst_x3f_1771_);
lean_dec(v_orderedAddInst_x3f_1770_);
lean_dec(v_lawfulOrderLTInst_x3f_1768_);
lean_dec(v_ltInst_x3f_1767_);
lean_dec(v_leInst_x3f_1766_);
lean_dec(v_val_1755_);
lean_del_object(v___x_1753_);
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
goto v___jp_1761_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_val_1755_);
lean_del_object(v___x_1753_);
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
v_a_1829_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1756_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1756_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_a_1751_);
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
v___x_1837_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1837_);
v___x_1839_ = v___x_1753_;
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
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_del_object(v___x_1724_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v_e_1652_);
v_a_1842_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1750_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1750_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
lean_dec_ref(v___x_1684_);
lean_dec_ref(v_e_1652_);
v_a_1851_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1721_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1721_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
v___jp_1695_:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; uint8_t v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1652_, v___x_1690_, v___x_1694_, v_strict_1696_, v_eqTrue_1653_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1697_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1652_, v___x_1690_, v___x_1694_, v_strict_1696_, v_eqTrue_1653_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1697_);
return v___x_1712_;
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v___y_1697_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_e_1652_);
v_a_1713_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1708_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1708_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
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
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_e_1652_);
v_a_1860_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1665_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1665_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_propagateIneq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1652_ = stack[0].m_obj;
uint8_t v_eqTrue_1653_ = stack[1].m_num;
lean_object* v_a_1654_ = stack[2].m_obj;
lean_object* v_a_1655_ = stack[3].m_obj;
lean_object* v_a_1656_ = stack[4].m_obj;
lean_object* v_a_1657_ = stack[5].m_obj;
lean_object* v_a_1658_ = stack[6].m_obj;
lean_object* v_a_1659_ = stack[7].m_obj;
lean_object* v_a_1660_ = stack[8].m_obj;
lean_object* v_a_1661_ = stack[9].m_obj;
lean_object* v_a_1662_ = stack[10].m_obj;
lean_object* v_a_1663_ = stack[11].m_obj;
lean_object* v_res_1868_;
v_res_1868_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1652_, v_eqTrue_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
stack->m_obj
 = v_res_1868_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1869_, lean_object* v_eqTrue_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint8_t v_eqTrue_boxed_1882_; lean_object* v_res_1883_; 
v_eqTrue_boxed_1882_ = lean_unbox(v_eqTrue_1870_);
v_res_1883_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1869_, v_eqTrue_boxed_1882_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec(v_a_1871_);
return v_res_1883_;
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
