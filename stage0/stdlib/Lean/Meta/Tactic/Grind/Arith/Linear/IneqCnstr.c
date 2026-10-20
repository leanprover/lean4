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
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
size_t v_x_69619__boxed_62_; size_t v_x_69620__boxed_63_; lean_object* v_res_64_; 
v_x_69619__boxed_62_ = lean_unbox_usize(v_x_60_);
lean_dec(v_x_60_);
v_x_69620__boxed_63_ = lean_unbox_usize(v_x_61_);
lean_dec(v_x_61_);
v_res_64_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__4(v_c_58_, v_x_59_, v_x_69619__boxed_62_, v_x_69620__boxed_63_);
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
v___x_167_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_102_, v_lowers_151_, v_v_103_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 32, v___x_167_);
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
lean_ctor_set(v_reuseFailAlloc_174_, 32, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_174_, 33, v_uppers_152_);
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
v___x_256_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_c_191_, v_uppers_241_, v_v_192_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 33, v___x_256_);
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
lean_ctor_set(v_reuseFailAlloc_263_, 32, v_lowers_240_);
lean_ctor_set(v_reuseFailAlloc_263_, 33, v___x_256_);
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
lean_object* v___x_480_; lean_object* v_env_481_; uint8_t v___x_482_; lean_object* v_env_483_; lean_object* v___x_484_; lean_object* v_toCold_485_; lean_object* v_mctx_486_; lean_object* v_lctx_487_; lean_object* v_options_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = 0;
v_env_483_ = l_Lean_Environment_setRecordingDeps(v_env_481_, v___x_482_);
v___x_484_ = lean_st_ref_get(v___y_476_);
v_toCold_485_ = lean_ctor_get(v___y_477_, 0);
v_mctx_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc_ref(v_mctx_486_);
lean_dec(v___x_484_);
v_lctx_487_ = lean_ctor_get(v___y_475_, 2);
v_options_488_ = lean_ctor_get(v_toCold_485_, 2);
lean_inc_ref(v_options_488_);
lean_inc_ref(v_lctx_487_);
v___x_489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_489_, 0, v_env_483_);
lean_ctor_set(v___x_489_, 1, v_mctx_486_);
lean_ctor_set(v___x_489_, 2, v_lctx_487_);
lean_ctor_set(v___x_489_, 3, v_options_488_);
v___x_490_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_msgData_474_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2___boxed(lean_object* v_msgData_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msgData_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_ref_505_; lean_object* v___x_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_ref_505_ = lean_ctor_get(v___y_502_, 2);
v___x_506_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_ref_505_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_ref_505_);
lean_ctor_set(v___x_511_, 1, v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_msg_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__0));
v___x_525_ = l_Lean_stringToMessageData(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_550_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_ltFn_x3f_543_; 
v_ltFn_x3f_543_ = lean_ctor_get(v_a_539_, 21);
lean_inc(v_ltFn_x3f_543_);
lean_dec(v_a_539_);
if (lean_obj_tag(v_ltFn_x3f_543_) == 1)
{
lean_object* v_val_544_; lean_object* v___x_546_; 
v_val_544_ = lean_ctor_get(v_ltFn_x3f_543_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v_ltFn_x3f_543_, 1);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_val_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_ltFn_x3f_543_);
lean_del_object(v___x_541_);
v___x_548_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___closed__1);
v___x_549_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_548_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
return v___x_549_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_538_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_538_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3___boxed(lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v___y_560_);
lean_dec(v___y_559_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_599_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_leFn_x3f_592_; 
v_leFn_x3f_592_ = lean_ctor_get(v_a_588_, 20);
lean_inc(v_leFn_x3f_592_);
lean_dec(v_a_588_);
if (lean_obj_tag(v_leFn_x3f_592_) == 1)
{
lean_object* v_val_593_; lean_object* v___x_595_; 
v_val_593_ = lean_ctor_get(v_leFn_x3f_592_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v_leFn_x3f_592_, 1);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_val_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_val_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_leFn_x3f_592_);
lean_del_object(v___x_590_);
v___x_597_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___closed__1);
v___x_598_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v___x_597_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_598_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_587_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_587_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1___boxed(lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v___y_608_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(lean_object* v_p_621_, uint8_t v_strict_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
if (v_strict_622_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1(v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_621_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_649_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_ofNatZero_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v_ofNatZero_644_ = lean_ctor_get(v_a_640_, 18);
lean_inc_ref(v_ofNatZero_644_);
lean_dec(v_a_640_);
v___x_645_ = l_Lean_mkAppB(v_a_636_, v_a_638_, v_ofNatZero_644_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_a_638_);
lean_dec(v_a_636_);
v_a_650_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_639_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_639_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_dec(v_a_636_);
return v___x_637_;
}
}
else
{
return v___x_635_;
}
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__3(v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__2(v_p_621_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_672_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_ofNatZero_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_ofNatZero_667_ = lean_ctor_get(v_a_663_, 18);
lean_inc_ref(v_ofNatZero_667_);
lean_dec(v_a_663_);
v___x_668_ = l_Lean_mkAppB(v_a_659_, v_a_661_, v_ofNatZero_667_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_a_661_);
lean_dec(v_a_659_);
v_a_673_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_662_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_662_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_dec(v_a_659_);
return v___x_660_;
}
}
else
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_p_681_, lean_object* v_strict_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v_strict_boxed_695_; lean_object* v_res_696_; 
v_strict_boxed_695_ = lean_unbox(v_strict_682_);
v_res_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_681_, v_strict_boxed_695_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v_p_681_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_c_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_p_710_; uint8_t v_strict_711_; lean_object* v___x_712_; 
v_p_710_ = lean_ctor_get(v_c_697_, 0);
v_strict_711_ = lean_ctor_get_uint8(v_c_697_, sizeof(void*)*2);
v___x_712_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0(v_p_710_, v_strict_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_c_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_c_713_);
return v_res_726_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_727_; double v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_float_of_nat(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(lean_object* v_cls_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_ref_739_; lean_object* v___x_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_786_; 
v_ref_739_ = lean_ctor_get(v___y_736_, 2);
v___x_740_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__2(v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_786_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_786_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_786_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v_traceState_746_; lean_object* v_env_747_; lean_object* v_nextMacroScope_748_; lean_object* v_ngen_749_; lean_object* v_auxDeclNGen_750_; lean_object* v_cache_751_; lean_object* v_recordedDeps_752_; lean_object* v_messages_753_; lean_object* v_infoState_754_; lean_object* v_snapshotTasks_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_785_; 
v___x_745_ = lean_st_ref_take(v___y_737_);
v_traceState_746_ = lean_ctor_get(v___x_745_, 4);
v_env_747_ = lean_ctor_get(v___x_745_, 0);
v_nextMacroScope_748_ = lean_ctor_get(v___x_745_, 1);
v_ngen_749_ = lean_ctor_get(v___x_745_, 2);
v_auxDeclNGen_750_ = lean_ctor_get(v___x_745_, 3);
v_cache_751_ = lean_ctor_get(v___x_745_, 5);
v_recordedDeps_752_ = lean_ctor_get(v___x_745_, 6);
v_messages_753_ = lean_ctor_get(v___x_745_, 7);
v_infoState_754_ = lean_ctor_get(v___x_745_, 8);
v_snapshotTasks_755_ = lean_ctor_get(v___x_745_, 9);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_785_ == 0)
{
v___x_757_ = v___x_745_;
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snapshotTasks_755_);
lean_inc(v_infoState_754_);
lean_inc(v_messages_753_);
lean_inc(v_recordedDeps_752_);
lean_inc(v_cache_751_);
lean_inc(v_traceState_746_);
lean_inc(v_auxDeclNGen_750_);
lean_inc(v_ngen_749_);
lean_inc(v_nextMacroScope_748_);
lean_inc(v_env_747_);
lean_dec(v___x_745_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
uint64_t v_tid_759_; lean_object* v_traces_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_784_; 
v_tid_759_ = lean_ctor_get_uint64(v_traceState_746_, sizeof(void*)*1);
v_traces_760_ = lean_ctor_get(v_traceState_746_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_traceState_746_);
if (v_isSharedCheck_784_ == 0)
{
v___x_762_ = v_traceState_746_;
v_isShared_763_ = v_isSharedCheck_784_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_traces_760_);
lean_dec(v_traceState_746_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_784_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; double v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_box(0);
v___x_766_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__0);
v___x_767_ = 0;
v___x_768_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__1));
v___x_769_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_769_, 0, v_cls_732_);
lean_ctor_set(v___x_769_, 1, v___x_765_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
lean_ctor_set_float(v___x_769_, sizeof(void*)*3, v___x_766_);
lean_ctor_set_float(v___x_769_, sizeof(void*)*3 + 8, v___x_766_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*3 + 16, v___x_767_);
v___x_770_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___closed__2));
v___x_771_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v_a_741_);
lean_ctor_set(v___x_771_, 2, v___x_770_);
lean_inc(v_ref_739_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_ref_739_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_PersistentArray_push___redArg(v_traces_760_, v___x_772_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_773_);
v___x_775_ = v___x_762_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_773_);
lean_ctor_set_uint64(v_reuseFailAlloc_783_, sizeof(void*)*1, v_tid_759_);
v___x_775_ = v_reuseFailAlloc_783_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v___x_775_);
v___x_777_ = v___x_757_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_env_747_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_nextMacroScope_748_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_ngen_749_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_auxDeclNGen_750_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_cache_751_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_recordedDeps_752_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_messages_753_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_infoState_754_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_snapshotTasks_755_);
v___x_777_ = v_reuseFailAlloc_782_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_st_ref_put(v___y_737_, v___x_777_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_764_);
v___x_780_ = v___x_743_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_764_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg___boxed(lean_object* v_cls_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_787_, v_msg_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_nat_to_int(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_810_ = l_Lean_Name_append(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_817_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_818_ = l_Lean_Name_append(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_827_ = l_Lean_Name_append(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16(void){
_start:
{
lean_object* v_cls_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_cls_832_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_833_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_834_ = l_Lean_Name_append(v___x_833_, v_cls_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* v_c_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v_toCold_925_; lean_object* v_options_926_; lean_object* v_inheritedTraceOptions_927_; uint8_t v_hasTrace_928_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; 
v_toCold_925_ = lean_ctor_get(v_a_845_, 0);
v_options_926_ = lean_ctor_get(v_toCold_925_, 2);
v_inheritedTraceOptions_927_ = lean_ctor_get(v_toCold_925_, 11);
v_hasTrace_928_ = lean_ctor_get_uint8(v_options_926_, sizeof(void*)*1);
if (v_hasTrace_928_ == 0)
{
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
v___y_938_ = v_a_844_;
v___y_939_ = v_a_845_;
v___y_940_ = v_a_846_;
goto v___jp_929_;
}
else
{
lean_object* v_cls_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_cls_1004_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__15));
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__16);
v___x_1006_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_927_, v_options_926_, v___x_1005_);
if (v___x_1006_ == 0)
{
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
v___y_938_ = v_a_844_;
v___y_939_ = v_a_845_;
v___y_940_ = v_a_846_;
goto v___jp_929_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_MessageData_ofExpr(v_a_1008_);
v___x_1010_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1004_, v___x_1009_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_dec_ref_known(v___x_1010_, 1);
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
v___y_938_ = v_a_844_;
v___y_939_ = v_a_845_;
v___y_940_ = v_a_846_;
goto v___jp_929_;
}
else
{
lean_dec_ref(v_c_835_);
return v___x_1010_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_c_835_);
v_a_1011_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1007_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1007_);
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
}
v___jp_848_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
v___jp_851_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_c_835_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_863_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
v___jp_865_:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_835_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; uint8_t v___x_884_; uint8_t v___x_885_; 
v___x_883_ = 0;
v___x_884_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
v___x_885_ = l_Lean_instBEqLBool_beq(v___x_884_, v___x_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec(v___y_866_);
v___x_886_ = lean_box(0);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_886_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_890_; 
lean_del_object(v___x_881_);
v___x_890_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_866_, v___y_867_, v___y_868_);
return v___x_890_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v___y_866_);
v_a_892_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_878_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_878_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
v___jp_900_:
{
lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___x_918_; 
lean_inc(v___y_901_);
lean_inc_ref_n(v_c_835_, 2);
lean_inc_n(v___y_905_, 2);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_916_, 0, v___y_905_);
lean_closure_set(v___f_916_, 1, v_c_835_);
lean_closure_set(v___f_916_, 2, v___y_901_);
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(v___f_917_, 0, v___y_905_);
lean_closure_set(v___f_917_, 1, v_c_835_);
lean_closure_set(v___f_917_, 2, v___y_901_);
v___x_918_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; uint8_t v___x_920_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_919_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_920_ = lean_int_dec_lt(v___y_902_, v___x_919_);
lean_dec(v___y_902_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v___f_916_);
v___x_921_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_922_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_921_, v___f_917_, v___y_906_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref_known(v___x_922_, 1);
v___y_866_ = v___y_903_;
v___y_867_ = v___y_905_;
v___y_868_ = v___y_906_;
v___y_869_ = v___y_907_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_909_;
v___y_872_ = v___y_910_;
v___y_873_ = v___y_911_;
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_914_;
v___y_877_ = v___y_915_;
goto v___jp_865_;
}
else
{
lean_dec(v___y_903_);
lean_dec_ref(v_c_835_);
return v___x_922_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v___f_917_);
v___x_923_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_924_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_923_, v___f_916_, v___y_906_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_dec_ref_known(v___x_924_, 1);
v___y_866_ = v___y_903_;
v___y_867_ = v___y_905_;
v___y_868_ = v___y_906_;
v___y_869_ = v___y_907_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_909_;
v___y_872_ = v___y_910_;
v___y_873_ = v___y_911_;
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_914_;
v___y_877_ = v___y_915_;
goto v___jp_865_;
}
else
{
lean_dec(v___y_903_);
lean_dec_ref(v_c_835_);
return v___x_924_;
}
}
}
else
{
lean_dec_ref(v___f_917_);
lean_dec_ref(v___f_916_);
lean_dec(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v_c_835_);
return v___x_918_;
}
}
v___jp_929_:
{
lean_object* v_p_941_; 
v_p_941_ = lean_ctor_get(v_c_835_, 0);
if (lean_obj_tag(v_p_941_) == 0)
{
uint8_t v_strict_942_; 
v_strict_942_ = lean_ctor_get_uint8(v_c_835_, sizeof(void*)*2);
if (v_strict_942_ == 0)
{
lean_object* v_toCold_943_; lean_object* v_options_944_; uint8_t v_hasTrace_945_; 
v_toCold_943_ = lean_ctor_get(v___y_939_, 0);
v_options_944_ = lean_ctor_get(v_toCold_943_, 2);
v_hasTrace_945_ = lean_ctor_get_uint8(v_options_944_, sizeof(void*)*1);
if (v_hasTrace_945_ == 0)
{
lean_dec_ref(v_c_835_);
goto v___jp_848_;
}
else
{
lean_object* v_inheritedTraceOptions_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_inheritedTraceOptions_946_ = lean_ctor_get(v_toCold_943_, 11);
v___x_947_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_948_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8);
v___x_949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_946_, v_options_944_, v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_c_835_);
goto v___jp_848_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_835_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec_ref(v_c_835_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = l_Lean_MessageData_ofExpr(v_a_951_);
v___x_953_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_947_, v___x_952_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_953_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_950_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_962_; lean_object* v_options_963_; uint8_t v_hasTrace_964_; 
v_toCold_962_ = lean_ctor_get(v___y_939_, 0);
v_options_963_ = lean_ctor_get(v_toCold_962_, 2);
v_hasTrace_964_ = lean_ctor_get_uint8(v_options_963_, sizeof(void*)*1);
if (v_hasTrace_964_ == 0)
{
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
v___y_860_ = v___y_938_;
v___y_861_ = v___y_939_;
v___y_862_ = v___y_940_;
goto v___jp_851_;
}
else
{
lean_object* v_inheritedTraceOptions_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_inheritedTraceOptions_965_ = lean_ctor_get(v_toCold_962_, 11);
v___x_966_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_967_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__11);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_965_, v_options_963_, v___x_967_);
if (v___x_968_ == 0)
{
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
v___y_860_ = v___y_938_;
v___y_861_ = v___y_939_;
v___y_862_ = v___y_940_;
goto v___jp_851_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_835_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_MessageData_ofExpr(v_a_970_);
v___x_972_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_966_, v___x_971_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_dec_ref_known(v___x_972_, 1);
v___y_852_ = v___y_930_;
v___y_853_ = v___y_931_;
v___y_854_ = v___y_932_;
v___y_855_ = v___y_933_;
v___y_856_ = v___y_934_;
v___y_857_ = v___y_935_;
v___y_858_ = v___y_936_;
v___y_859_ = v___y_937_;
v___y_860_ = v___y_938_;
v___y_861_ = v___y_939_;
v___y_862_ = v___y_940_;
goto v___jp_851_;
}
else
{
lean_dec_ref(v_c_835_);
return v___x_972_;
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_c_835_);
v_a_973_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_969_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_969_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_981_; lean_object* v_options_982_; uint8_t v_hasTrace_983_; 
v_toCold_981_ = lean_ctor_get(v___y_939_, 0);
v_options_982_ = lean_ctor_get(v_toCold_981_, 2);
v_hasTrace_983_ = lean_ctor_get_uint8(v_options_982_, sizeof(void*)*1);
if (v_hasTrace_983_ == 0)
{
lean_object* v_k_984_; lean_object* v_v_985_; 
v_k_984_ = lean_ctor_get(v_p_941_, 0);
v_v_985_ = lean_ctor_get(v_p_941_, 1);
lean_inc_ref(v_p_941_);
lean_inc(v_k_984_);
lean_inc_n(v_v_985_, 2);
v___y_901_ = v_v_985_;
v___y_902_ = v_k_984_;
v___y_903_ = v_v_985_;
v___y_904_ = v_p_941_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
v___y_913_ = v___y_938_;
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
goto v___jp_900_;
}
else
{
lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v_inheritedTraceOptions_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_k_986_ = lean_ctor_get(v_p_941_, 0);
v_v_987_ = lean_ctor_get(v_p_941_, 1);
v_inheritedTraceOptions_988_ = lean_ctor_get(v_toCold_981_, 11);
v___x_989_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__13));
v___x_990_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__14);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_988_, v_options_982_, v___x_990_);
if (v___x_991_ == 0)
{
lean_inc_ref(v_p_941_);
lean_inc(v_k_986_);
lean_inc_n(v_v_987_, 2);
v___y_901_ = v_v_987_;
v___y_902_ = v_k_986_;
v___y_903_ = v_v_987_;
v___y_904_ = v_p_941_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
v___y_913_ = v___y_938_;
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
goto v___jp_900_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_c_835_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = l_Lean_MessageData_ofExpr(v_a_993_);
v___x_995_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v___x_989_, v___x_994_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_dec_ref_known(v___x_995_, 1);
lean_inc_ref(v_p_941_);
lean_inc(v_k_986_);
lean_inc_n(v_v_987_, 2);
v___y_901_ = v_v_987_;
v___y_902_ = v_k_986_;
v___y_903_ = v_v_987_;
v___y_904_ = v_p_941_;
v___y_905_ = v___y_930_;
v___y_906_ = v___y_931_;
v___y_907_ = v___y_932_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
v___y_913_ = v___y_938_;
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_c_835_);
return v___x_995_;
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_c_835_);
v_a_996_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_992_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_992_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_cls_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___redArg(v_cls_1033_, v_msg_1034_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_cls_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_cls_1048_, v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___redArg(v_msg_1064_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_msg_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1078_, v_msg_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1093_, lean_object* v_e_1094_, lean_object* v_s_1095_){
_start:
{
lean_object* v_structs_1096_; lean_object* v_typeIdOf_1097_; lean_object* v_exprToStructId_1098_; lean_object* v_exprToStructIdEntries_1099_; lean_object* v_forbiddenNatModules_1100_; lean_object* v_natStructs_1101_; lean_object* v_natTypeIdOf_1102_; lean_object* v_exprToNatStructId_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_structs_1096_ = lean_ctor_get(v_s_1095_, 0);
v_typeIdOf_1097_ = lean_ctor_get(v_s_1095_, 1);
v_exprToStructId_1098_ = lean_ctor_get(v_s_1095_, 2);
v_exprToStructIdEntries_1099_ = lean_ctor_get(v_s_1095_, 3);
v_forbiddenNatModules_1100_ = lean_ctor_get(v_s_1095_, 4);
v_natStructs_1101_ = lean_ctor_get(v_s_1095_, 5);
v_natTypeIdOf_1102_ = lean_ctor_get(v_s_1095_, 6);
v_exprToNatStructId_1103_ = lean_ctor_get(v_s_1095_, 7);
v___x_1104_ = lean_array_get_size(v_structs_1096_);
v___x_1105_ = lean_nat_dec_lt(v_a_1093_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v_e_1094_);
return v_s_1095_;
}
else
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1167_; 
lean_inc_ref(v_exprToNatStructId_1103_);
lean_inc_ref(v_natTypeIdOf_1102_);
lean_inc_ref(v_natStructs_1101_);
lean_inc_ref(v_forbiddenNatModules_1100_);
lean_inc_ref(v_exprToStructIdEntries_1099_);
lean_inc_ref(v_exprToStructId_1098_);
lean_inc_ref(v_typeIdOf_1097_);
lean_inc_ref(v_structs_1096_);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_s_1095_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1168_ = lean_ctor_get(v_s_1095_, 7);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_s_1095_, 6);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_s_1095_, 5);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_s_1095_, 4);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_s_1095_, 3);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_s_1095_, 2);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_s_1095_, 1);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_s_1095_, 0);
lean_dec(v_unused_1175_);
v___x_1107_ = v_s_1095_;
v_isShared_1108_ = v_isSharedCheck_1167_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v_s_1095_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1167_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_v_1109_; lean_object* v_id_1110_; lean_object* v_ringId_x3f_1111_; lean_object* v_type_1112_; lean_object* v_u_1113_; lean_object* v_intModuleInst_1114_; lean_object* v_leInst_x3f_1115_; lean_object* v_ltInst_x3f_1116_; lean_object* v_lawfulOrderLTInst_x3f_1117_; lean_object* v_isPreorderInst_x3f_1118_; lean_object* v_orderedAddInst_x3f_1119_; lean_object* v_isLinearInst_x3f_1120_; lean_object* v_noNatDivInst_x3f_1121_; lean_object* v_ringInst_x3f_1122_; lean_object* v_commRingInst_x3f_1123_; lean_object* v_orderedRingInst_x3f_1124_; lean_object* v_fieldInst_x3f_1125_; lean_object* v_charInst_x3f_1126_; lean_object* v_zero_1127_; lean_object* v_ofNatZero_1128_; lean_object* v_one_x3f_1129_; lean_object* v_leFn_x3f_1130_; lean_object* v_ltFn_x3f_1131_; lean_object* v_addFn_1132_; lean_object* v_zsmulFn_1133_; lean_object* v_nsmulFn_1134_; lean_object* v_zsmulFn_x3f_1135_; lean_object* v_nsmulFn_x3f_1136_; lean_object* v_homomulFn_x3f_1137_; lean_object* v_subFn_1138_; lean_object* v_negFn_1139_; lean_object* v_vars_1140_; lean_object* v_varMap_1141_; lean_object* v_lowers_1142_; lean_object* v_uppers_1143_; lean_object* v_diseqs_1144_; lean_object* v_assignment_1145_; uint8_t v_caseSplits_1146_; lean_object* v_conflict_x3f_1147_; lean_object* v_diseqSplits_1148_; lean_object* v_elimEqs_1149_; lean_object* v_elimStack_1150_; lean_object* v_occurs_1151_; lean_object* v_ignored_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1166_; 
v_v_1109_ = lean_array_fget(v_structs_1096_, v_a_1093_);
v_id_1110_ = lean_ctor_get(v_v_1109_, 0);
v_ringId_x3f_1111_ = lean_ctor_get(v_v_1109_, 1);
v_type_1112_ = lean_ctor_get(v_v_1109_, 2);
v_u_1113_ = lean_ctor_get(v_v_1109_, 3);
v_intModuleInst_1114_ = lean_ctor_get(v_v_1109_, 4);
v_leInst_x3f_1115_ = lean_ctor_get(v_v_1109_, 5);
v_ltInst_x3f_1116_ = lean_ctor_get(v_v_1109_, 6);
v_lawfulOrderLTInst_x3f_1117_ = lean_ctor_get(v_v_1109_, 7);
v_isPreorderInst_x3f_1118_ = lean_ctor_get(v_v_1109_, 8);
v_orderedAddInst_x3f_1119_ = lean_ctor_get(v_v_1109_, 9);
v_isLinearInst_x3f_1120_ = lean_ctor_get(v_v_1109_, 10);
v_noNatDivInst_x3f_1121_ = lean_ctor_get(v_v_1109_, 11);
v_ringInst_x3f_1122_ = lean_ctor_get(v_v_1109_, 12);
v_commRingInst_x3f_1123_ = lean_ctor_get(v_v_1109_, 13);
v_orderedRingInst_x3f_1124_ = lean_ctor_get(v_v_1109_, 14);
v_fieldInst_x3f_1125_ = lean_ctor_get(v_v_1109_, 15);
v_charInst_x3f_1126_ = lean_ctor_get(v_v_1109_, 16);
v_zero_1127_ = lean_ctor_get(v_v_1109_, 17);
v_ofNatZero_1128_ = lean_ctor_get(v_v_1109_, 18);
v_one_x3f_1129_ = lean_ctor_get(v_v_1109_, 19);
v_leFn_x3f_1130_ = lean_ctor_get(v_v_1109_, 20);
v_ltFn_x3f_1131_ = lean_ctor_get(v_v_1109_, 21);
v_addFn_1132_ = lean_ctor_get(v_v_1109_, 22);
v_zsmulFn_1133_ = lean_ctor_get(v_v_1109_, 23);
v_nsmulFn_1134_ = lean_ctor_get(v_v_1109_, 24);
v_zsmulFn_x3f_1135_ = lean_ctor_get(v_v_1109_, 25);
v_nsmulFn_x3f_1136_ = lean_ctor_get(v_v_1109_, 26);
v_homomulFn_x3f_1137_ = lean_ctor_get(v_v_1109_, 27);
v_subFn_1138_ = lean_ctor_get(v_v_1109_, 28);
v_negFn_1139_ = lean_ctor_get(v_v_1109_, 29);
v_vars_1140_ = lean_ctor_get(v_v_1109_, 30);
v_varMap_1141_ = lean_ctor_get(v_v_1109_, 31);
v_lowers_1142_ = lean_ctor_get(v_v_1109_, 32);
v_uppers_1143_ = lean_ctor_get(v_v_1109_, 33);
v_diseqs_1144_ = lean_ctor_get(v_v_1109_, 34);
v_assignment_1145_ = lean_ctor_get(v_v_1109_, 35);
v_caseSplits_1146_ = lean_ctor_get_uint8(v_v_1109_, sizeof(void*)*42);
v_conflict_x3f_1147_ = lean_ctor_get(v_v_1109_, 36);
v_diseqSplits_1148_ = lean_ctor_get(v_v_1109_, 37);
v_elimEqs_1149_ = lean_ctor_get(v_v_1109_, 38);
v_elimStack_1150_ = lean_ctor_get(v_v_1109_, 39);
v_occurs_1151_ = lean_ctor_get(v_v_1109_, 40);
v_ignored_1152_ = lean_ctor_get(v_v_1109_, 41);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_v_1109_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1154_ = v_v_1109_;
v_isShared_1155_ = v_isSharedCheck_1166_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_ignored_1152_);
lean_inc(v_occurs_1151_);
lean_inc(v_elimStack_1150_);
lean_inc(v_elimEqs_1149_);
lean_inc(v_diseqSplits_1148_);
lean_inc(v_conflict_x3f_1147_);
lean_inc(v_assignment_1145_);
lean_inc(v_diseqs_1144_);
lean_inc(v_uppers_1143_);
lean_inc(v_lowers_1142_);
lean_inc(v_varMap_1141_);
lean_inc(v_vars_1140_);
lean_inc(v_negFn_1139_);
lean_inc(v_subFn_1138_);
lean_inc(v_homomulFn_x3f_1137_);
lean_inc(v_nsmulFn_x3f_1136_);
lean_inc(v_zsmulFn_x3f_1135_);
lean_inc(v_nsmulFn_1134_);
lean_inc(v_zsmulFn_1133_);
lean_inc(v_addFn_1132_);
lean_inc(v_ltFn_x3f_1131_);
lean_inc(v_leFn_x3f_1130_);
lean_inc(v_one_x3f_1129_);
lean_inc(v_ofNatZero_1128_);
lean_inc(v_zero_1127_);
lean_inc(v_charInst_x3f_1126_);
lean_inc(v_fieldInst_x3f_1125_);
lean_inc(v_orderedRingInst_x3f_1124_);
lean_inc(v_commRingInst_x3f_1123_);
lean_inc(v_ringInst_x3f_1122_);
lean_inc(v_noNatDivInst_x3f_1121_);
lean_inc(v_isLinearInst_x3f_1120_);
lean_inc(v_orderedAddInst_x3f_1119_);
lean_inc(v_isPreorderInst_x3f_1118_);
lean_inc(v_lawfulOrderLTInst_x3f_1117_);
lean_inc(v_ltInst_x3f_1116_);
lean_inc(v_leInst_x3f_1115_);
lean_inc(v_intModuleInst_1114_);
lean_inc(v_u_1113_);
lean_inc(v_type_1112_);
lean_inc(v_ringId_x3f_1111_);
lean_inc(v_id_1110_);
lean_dec(v_v_1109_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1166_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v_xs_x27_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1156_ = lean_box(0);
v_xs_x27_1157_ = lean_array_fset(v_structs_1096_, v_a_1093_, v___x_1156_);
v___x_1158_ = l_Lean_PersistentArray_push___redArg(v_ignored_1152_, v_e_1094_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 41, v___x_1158_);
v___x_1160_ = v___x_1154_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_id_1110_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_ringId_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_type_1112_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_u_1113_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_intModuleInst_1114_);
lean_ctor_set(v_reuseFailAlloc_1165_, 5, v_leInst_x3f_1115_);
lean_ctor_set(v_reuseFailAlloc_1165_, 6, v_ltInst_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1165_, 7, v_lawfulOrderLTInst_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1165_, 8, v_isPreorderInst_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1165_, 9, v_orderedAddInst_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1165_, 10, v_isLinearInst_x3f_1120_);
lean_ctor_set(v_reuseFailAlloc_1165_, 11, v_noNatDivInst_x3f_1121_);
lean_ctor_set(v_reuseFailAlloc_1165_, 12, v_ringInst_x3f_1122_);
lean_ctor_set(v_reuseFailAlloc_1165_, 13, v_commRingInst_x3f_1123_);
lean_ctor_set(v_reuseFailAlloc_1165_, 14, v_orderedRingInst_x3f_1124_);
lean_ctor_set(v_reuseFailAlloc_1165_, 15, v_fieldInst_x3f_1125_);
lean_ctor_set(v_reuseFailAlloc_1165_, 16, v_charInst_x3f_1126_);
lean_ctor_set(v_reuseFailAlloc_1165_, 17, v_zero_1127_);
lean_ctor_set(v_reuseFailAlloc_1165_, 18, v_ofNatZero_1128_);
lean_ctor_set(v_reuseFailAlloc_1165_, 19, v_one_x3f_1129_);
lean_ctor_set(v_reuseFailAlloc_1165_, 20, v_leFn_x3f_1130_);
lean_ctor_set(v_reuseFailAlloc_1165_, 21, v_ltFn_x3f_1131_);
lean_ctor_set(v_reuseFailAlloc_1165_, 22, v_addFn_1132_);
lean_ctor_set(v_reuseFailAlloc_1165_, 23, v_zsmulFn_1133_);
lean_ctor_set(v_reuseFailAlloc_1165_, 24, v_nsmulFn_1134_);
lean_ctor_set(v_reuseFailAlloc_1165_, 25, v_zsmulFn_x3f_1135_);
lean_ctor_set(v_reuseFailAlloc_1165_, 26, v_nsmulFn_x3f_1136_);
lean_ctor_set(v_reuseFailAlloc_1165_, 27, v_homomulFn_x3f_1137_);
lean_ctor_set(v_reuseFailAlloc_1165_, 28, v_subFn_1138_);
lean_ctor_set(v_reuseFailAlloc_1165_, 29, v_negFn_1139_);
lean_ctor_set(v_reuseFailAlloc_1165_, 30, v_vars_1140_);
lean_ctor_set(v_reuseFailAlloc_1165_, 31, v_varMap_1141_);
lean_ctor_set(v_reuseFailAlloc_1165_, 32, v_lowers_1142_);
lean_ctor_set(v_reuseFailAlloc_1165_, 33, v_uppers_1143_);
lean_ctor_set(v_reuseFailAlloc_1165_, 34, v_diseqs_1144_);
lean_ctor_set(v_reuseFailAlloc_1165_, 35, v_assignment_1145_);
lean_ctor_set(v_reuseFailAlloc_1165_, 36, v_conflict_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1165_, 37, v_diseqSplits_1148_);
lean_ctor_set(v_reuseFailAlloc_1165_, 38, v_elimEqs_1149_);
lean_ctor_set(v_reuseFailAlloc_1165_, 39, v_elimStack_1150_);
lean_ctor_set(v_reuseFailAlloc_1165_, 40, v_occurs_1151_);
lean_ctor_set(v_reuseFailAlloc_1165_, 41, v___x_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1165_, sizeof(void*)*42, v_caseSplits_1146_);
v___x_1160_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_array_fset(v_xs_x27_1157_, v_a_1093_, v___x_1160_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1161_);
v___x_1163_ = v___x_1107_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_typeIdOf_1097_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_exprToStructId_1098_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_exprToStructIdEntries_1099_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_forbiddenNatModules_1100_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_natStructs_1101_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_natTypeIdOf_1102_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v_exprToNatStructId_1103_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1176_, lean_object* v_e_1177_, lean_object* v_s_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1176_, v_e_1177_, v_s_1178_);
lean_dec(v_a_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1180_, lean_object* v_lhs_1181_, lean_object* v_rhs_1182_, uint8_t v_strict_1183_, uint8_t v_eqTrue_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___f_1197_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_inc_ref(v_e_1180_);
lean_inc(v_a_1185_);
v___f_1197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1197_, 0, v_a_1185_);
lean_closure_set(v___f_1197_, 1, v_e_1180_);
v___x_1201_ = 0;
v___x_1202_ = lean_box(v___x_1201_);
v___x_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_1203_, 0, v_lhs_1181_);
lean_closure_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1203_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1367_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1367_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1367_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
if (lean_obj_tag(v_a_1205_) == 1)
{
lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1207_);
v_val_1209_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_val_1209_);
lean_dec_ref_known(v_a_1205_, 1);
v___x_1210_ = lean_box(v___x_1201_);
v___x_1211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_1211_, 0, v_rhs_1182_);
lean_closure_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1211_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1354_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1354_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1354_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
if (lean_obj_tag(v_a_1213_) == 1)
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
lean_del_object(v___x_1215_);
v_val_1217_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_a_1213_, 1);
v___x_1218_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1180_, v_a_1186_);
if (lean_obj_tag(v___x_1218_) == 0)
{
if (v_eqTrue_1184_ == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; uint8_t v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = lean_unbox(v_a_1221_);
lean_dec(v_a_1221_);
if (v___x_1222_ == 0)
{
lean_dec(v_a_1219_);
lean_dec(v_val_1217_);
lean_dec(v_val_1209_);
lean_dec_ref(v_e_1180_);
goto v___jp_1198_;
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; uint8_t v___x_1225_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v___x_1225_ = lean_unbox(v_a_1224_);
if (v___x_1225_ == 0)
{
lean_dec(v_a_1224_);
lean_dec(v_a_1219_);
lean_dec(v_val_1217_);
lean_dec(v_val_1209_);
lean_dec_ref(v_e_1180_);
goto v___jp_1198_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___y_1229_; 
lean_dec_ref(v___f_1197_);
lean_inc(v_val_1209_);
lean_inc(v_val_1217_);
v___x_1226_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_val_1217_);
lean_ctor_set(v___x_1226_, 1, v_val_1209_);
v___x_1227_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1226_);
if (v_strict_1183_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_unbox(v_a_1224_);
lean_dec(v_a_1224_);
v___y_1229_ = v___x_1276_;
goto v___jp_1228_;
}
else
{
lean_dec(v_a_1224_);
v___y_1229_ = v_eqTrue_1184_;
goto v___jp_1228_;
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1230_, 0, v_e_1180_);
lean_ctor_set(v___x_1230_, 1, v_val_1209_);
lean_ctor_set(v___x_1230_, 2, v_val_1217_);
v___x_1231_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1231_, 0, v___x_1227_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*2, v___y_1229_);
v___x_1232_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1231_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_p_1234_; lean_object* v___x_1235_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_p_1234_ = lean_ctor_get(v_a_1233_, 0);
lean_inc_ref(v_p_1234_);
v___x_1235_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1234_, v_a_1219_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1236_, v___x_1201_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1251_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1251_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1251_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
if (lean_obj_tag(v_a_1238_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1240_);
v_val_1242_ = lean_ctor_get(v_a_1238_, 0);
lean_inc_n(v_val_1242_, 2);
lean_dec_ref_known(v_a_1238_, 1);
v___x_1243_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1242_);
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_a_1233_);
lean_ctor_set(v___x_1244_, 1, v_val_1242_);
v___x_1245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*2, v___y_1229_);
v___x_1246_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1245_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_a_1238_);
lean_dec(v_a_1233_);
v___x_1247_ = lean_box(0);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1247_);
v___x_1249_ = v___x_1240_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_a_1233_);
v_a_1252_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1237_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1237_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_a_1233_);
v_a_1260_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1235_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1235_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_a_1219_);
v_a_1268_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1232_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1232_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_a_1219_);
lean_dec(v_val_1217_);
lean_dec(v_val_1209_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_e_1180_);
v_a_1277_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1223_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1223_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_a_1219_);
lean_dec(v_val_1217_);
lean_dec(v_val_1209_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_e_1180_);
v_a_1285_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1220_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1220_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref(v___f_1197_);
v_a_1293_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1218_, 1);
lean_inc(v_val_1217_);
lean_inc(v_val_1209_);
v___x_1294_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_val_1209_);
lean_ctor_set(v___x_1294_, 1, v_val_1217_);
v___x_1295_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v_e_1180_);
lean_ctor_set(v___x_1296_, 1, v_val_1209_);
lean_ctor_set(v___x_1296_, 2, v_val_1217_);
v___x_1297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*2, v_strict_1183_);
v___x_1298_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1297_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_p_1300_; lean_object* v___x_1301_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v_p_1300_ = lean_ctor_get(v_a_1299_, 0);
lean_inc_ref(v_p_1300_);
v___x_1301_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1300_, v_a_1293_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1303_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1302_, v___x_1201_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1317_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1317_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1317_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
if (lean_obj_tag(v_a_1304_) == 1)
{
lean_object* v_val_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1306_);
v_val_1308_ = lean_ctor_get(v_a_1304_, 0);
lean_inc_n(v_val_1308_, 2);
lean_dec_ref_known(v_a_1304_, 1);
v___x_1309_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1308_);
v___x_1310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_a_1299_);
lean_ctor_set(v___x_1310_, 1, v_val_1308_);
v___x_1311_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*2, v_strict_1183_);
v___x_1312_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1311_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec(v_a_1304_);
lean_dec(v_a_1299_);
v___x_1313_ = lean_box(0);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1313_);
v___x_1315_ = v___x_1306_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_a_1299_);
v_a_1318_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1303_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1303_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_a_1299_);
v_a_1326_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1301_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1301_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_a_1293_);
v_a_1334_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1298_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1298_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_val_1217_);
lean_dec(v_val_1209_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_e_1180_);
v_a_1342_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1218_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1218_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
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
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_a_1213_);
lean_dec(v_val_1209_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_e_1180_);
v___x_1350_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1350_);
v___x_1352_ = v___x_1215_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_val_1209_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_e_1180_);
v_a_1355_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1212_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1212_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_a_1205_);
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_rhs_1182_);
lean_dec_ref(v_e_1180_);
v___x_1363_ = lean_box(0);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1363_);
v___x_1365_ = v___x_1207_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_rhs_1182_);
lean_dec_ref(v_e_1180_);
v_a_1368_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1204_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1204_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
v___jp_1198_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1200_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1199_, v___f_1197_, v_a_1186_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1376_ = _args[0];
lean_object* v_lhs_1377_ = _args[1];
lean_object* v_rhs_1378_ = _args[2];
lean_object* v_strict_1379_ = _args[3];
lean_object* v_eqTrue_1380_ = _args[4];
lean_object* v_a_1381_ = _args[5];
lean_object* v_a_1382_ = _args[6];
lean_object* v_a_1383_ = _args[7];
lean_object* v_a_1384_ = _args[8];
lean_object* v_a_1385_ = _args[9];
lean_object* v_a_1386_ = _args[10];
lean_object* v_a_1387_ = _args[11];
lean_object* v_a_1388_ = _args[12];
lean_object* v_a_1389_ = _args[13];
lean_object* v_a_1390_ = _args[14];
lean_object* v_a_1391_ = _args[15];
lean_object* v_a_1392_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1393_; uint8_t v_eqTrue_boxed_1394_; lean_object* v_res_1395_; 
v_strict_boxed_1393_ = lean_unbox(v_strict_1379_);
v_eqTrue_boxed_1394_ = lean_unbox(v_eqTrue_1380_);
v_res_1395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1376_, v_lhs_1377_, v_rhs_1378_, v_strict_boxed_1393_, v_eqTrue_boxed_1394_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec(v_a_1381_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1396_, lean_object* v_lhs_1397_, lean_object* v_rhs_1398_, uint8_t v_strict_1399_, uint8_t v_eqTrue_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___f_1413_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
lean_inc_ref(v_e_1396_);
lean_inc(v_a_1401_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1413_, 0, v_a_1401_);
lean_closure_set(v___f_1413_, 1, v_e_1396_);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1397_, v___x_1417_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1483_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1483_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1483_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
if (lean_obj_tag(v_a_1419_) == 1)
{
lean_object* v_val_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1421_);
v_val_1423_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_a_1419_, 1);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1398_, v___x_1417_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1470_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1470_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1470_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
if (lean_obj_tag(v_a_1425_) == 1)
{
lean_del_object(v___x_1427_);
if (v_eqTrue_1400_ == 0)
{
lean_object* v_val_1429_; lean_object* v___x_1430_; 
v_val_1429_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v_a_1425_, 1);
v___x_1430_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
lean_dec(v_val_1429_);
lean_dec(v_val_1423_);
lean_dec_ref(v_e_1396_);
goto v___jp_1414_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_unbox(v_a_1434_);
if (v___x_1435_ == 0)
{
lean_dec(v_a_1434_);
lean_dec(v_val_1429_);
lean_dec(v_val_1423_);
lean_dec_ref(v_e_1396_);
goto v___jp_1414_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___y_1439_; 
lean_dec_ref(v___f_1413_);
lean_inc(v_val_1423_);
lean_inc(v_val_1429_);
v___x_1436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_val_1429_);
lean_ctor_set(v___x_1436_, 1, v_val_1423_);
v___x_1437_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1436_);
if (v_strict_1399_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
v___y_1439_ = v___x_1443_;
goto v___jp_1438_;
}
else
{
lean_dec(v_a_1434_);
v___y_1439_ = v_eqTrue_1400_;
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1440_, 0, v_e_1396_);
lean_ctor_set(v___x_1440_, 1, v_val_1423_);
lean_ctor_set(v___x_1440_, 2, v_val_1429_);
v___x_1441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1437_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*2, v___y_1439_);
v___x_1442_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1441_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_val_1429_);
lean_dec(v_val_1423_);
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_e_1396_);
v_a_1444_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1433_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1433_);
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
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_val_1429_);
lean_dec(v_val_1423_);
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_e_1396_);
v_a_1452_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1430_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1430_);
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
lean_object* v_val_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v___f_1413_);
v_val_1460_ = lean_ctor_get(v_a_1425_, 0);
lean_inc_n(v_val_1460_, 2);
lean_dec_ref_known(v_a_1425_, 1);
lean_inc(v_val_1423_);
v___x_1461_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_val_1423_);
lean_ctor_set(v___x_1461_, 1, v_val_1460_);
v___x_1462_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1463_, 0, v_e_1396_);
lean_ctor_set(v___x_1463_, 1, v_val_1423_);
lean_ctor_set(v___x_1463_, 2, v_val_1460_);
v___x_1464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*2, v_strict_1399_);
v___x_1465_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1464_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
return v___x_1465_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec(v_a_1425_);
lean_dec(v_val_1423_);
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_e_1396_);
v___x_1466_ = lean_box(0);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1466_);
v___x_1468_ = v___x_1427_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
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
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_val_1423_);
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_e_1396_);
v_a_1471_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1424_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1424_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec(v_a_1419_);
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_rhs_1398_);
lean_dec_ref(v_e_1396_);
v___x_1479_ = lean_box(0);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1479_);
v___x_1481_ = v___x_1421_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
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
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_rhs_1398_);
lean_dec_ref(v_e_1396_);
v_a_1484_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1418_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1418_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
v___jp_1414_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1416_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1415_, v___f_1413_, v_a_1402_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1492_ = _args[0];
lean_object* v_lhs_1493_ = _args[1];
lean_object* v_rhs_1494_ = _args[2];
lean_object* v_strict_1495_ = _args[3];
lean_object* v_eqTrue_1496_ = _args[4];
lean_object* v_a_1497_ = _args[5];
lean_object* v_a_1498_ = _args[6];
lean_object* v_a_1499_ = _args[7];
lean_object* v_a_1500_ = _args[8];
lean_object* v_a_1501_ = _args[9];
lean_object* v_a_1502_ = _args[10];
lean_object* v_a_1503_ = _args[11];
lean_object* v_a_1504_ = _args[12];
lean_object* v_a_1505_ = _args[13];
lean_object* v_a_1506_ = _args[14];
lean_object* v_a_1507_ = _args[15];
lean_object* v_a_1508_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1509_; uint8_t v_eqTrue_boxed_1510_; lean_object* v_res_1511_; 
v_strict_boxed_1509_ = lean_unbox(v_strict_1495_);
v_eqTrue_boxed_1510_ = lean_unbox(v_eqTrue_1496_);
v_res_1511_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1492_, v_lhs_1493_, v_rhs_1494_, v_strict_boxed_1509_, v_eqTrue_boxed_1510_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec(v_a_1497_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1512_, lean_object* v_lhs_1513_, lean_object* v_rhs_1514_, uint8_t v_strict_1515_, uint8_t v_eqTrue_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1513_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_fst_1533_; lean_object* v___x_1534_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_fst_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_fst_1533_);
lean_dec(v_a_1532_);
v___x_1534_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1514_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_fst_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1599_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_fst_1536_ = lean_ctor_get(v_a_1535_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_a_1535_, 1);
lean_dec(v_unused_1600_);
v___x_1538_ = v_a_1535_;
v_isShared_1539_ = v_isSharedCheck_1599_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_fst_1536_);
lean_dec(v_a_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1599_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_id_1540_; lean_object* v_structId_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; 
v_id_1540_ = lean_ctor_get(v_a_1530_, 0);
lean_inc(v_id_1540_);
v_structId_1541_ = lean_ctor_get(v_a_1530_, 1);
lean_inc(v_structId_1541_);
lean_dec(v_a_1530_);
v___x_1542_ = 0;
v___x_1543_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1533_, v___x_1542_, v_structId_1541_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1590_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1590_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1590_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
if (lean_obj_tag(v_a_1544_) == 1)
{
lean_object* v_val_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1546_);
v_val_1548_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_a_1544_, 1);
v___x_1549_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1536_, v___x_1542_, v_structId_1541_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1577_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1577_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1577_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_del_object(v___x_1552_);
if (v_eqTrue_1516_ == 0)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; 
v_val_1554_ = lean_ctor_get(v_a_1550_, 0);
lean_inc_n(v_val_1554_, 2);
lean_dec_ref_known(v_a_1550_, 1);
lean_inc(v_val_1548_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 3);
lean_ctor_set(v___x_1538_, 1, v_val_1548_);
lean_ctor_set(v___x_1538_, 0, v_val_1554_);
v___x_1556_ = v___x_1538_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1554_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_val_1548_);
v___x_1556_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; uint8_t v___y_1559_; 
v___x_1557_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1556_);
if (v_strict_1515_ == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = 1;
v___y_1559_ = v___x_1563_;
goto v___jp_1558_;
}
else
{
v___y_1559_ = v_eqTrue_1516_;
goto v___jp_1558_;
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1560_, 0, v_e_1512_);
lean_ctor_set(v___x_1560_, 1, v_id_1540_);
lean_ctor_set(v___x_1560_, 2, v_val_1548_);
lean_ctor_set(v___x_1560_, 3, v_val_1554_);
v___x_1561_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*2, v___y_1559_);
v___x_1562_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1561_, v_structId_1541_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_structId_1541_);
return v___x_1562_;
}
}
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; 
v_val_1565_ = lean_ctor_get(v_a_1550_, 0);
lean_inc_n(v_val_1565_, 2);
lean_dec_ref_known(v_a_1550_, 1);
lean_inc(v_val_1548_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 3);
lean_ctor_set(v___x_1538_, 1, v_val_1565_);
lean_ctor_set(v___x_1538_, 0, v_val_1548_);
v___x_1567_ = v___x_1538_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_val_1548_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_val_1565_);
v___x_1567_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1567_);
v___x_1569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1569_, 0, v_e_1512_);
lean_ctor_set(v___x_1569_, 1, v_id_1540_);
lean_ctor_set(v___x_1569_, 2, v_val_1548_);
lean_ctor_set(v___x_1569_, 3, v_val_1565_);
v___x_1570_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*2, v_strict_1515_);
v___x_1571_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1570_, v_structId_1541_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_structId_1541_);
return v___x_1571_;
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v_a_1550_);
lean_dec(v_val_1548_);
lean_dec(v_structId_1541_);
lean_dec(v_id_1540_);
lean_del_object(v___x_1538_);
lean_dec_ref(v_e_1512_);
v___x_1573_ = lean_box(0);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1573_);
v___x_1575_ = v___x_1552_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_val_1548_);
lean_dec(v_structId_1541_);
lean_dec(v_id_1540_);
lean_del_object(v___x_1538_);
lean_dec_ref(v_e_1512_);
v_a_1578_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1549_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1549_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_dec(v_a_1544_);
lean_dec(v_structId_1541_);
lean_dec(v_id_1540_);
lean_del_object(v___x_1538_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_e_1512_);
v___x_1586_ = lean_box(0);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1586_);
v___x_1588_ = v___x_1546_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
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
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_structId_1541_);
lean_dec(v_id_1540_);
lean_del_object(v___x_1538_);
lean_dec(v_fst_1536_);
lean_dec_ref(v_e_1512_);
v_a_1591_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1543_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1543_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_fst_1533_);
lean_dec(v_a_1530_);
lean_dec_ref(v_e_1512_);
v_a_1601_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1534_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1534_);
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
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1530_);
lean_dec_ref(v_rhs_1514_);
lean_dec_ref(v_e_1512_);
v_a_1609_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1531_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1531_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_rhs_1514_);
lean_dec_ref(v_lhs_1513_);
lean_dec_ref(v_e_1512_);
v_a_1617_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1529_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1529_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1625_ = _args[0];
lean_object* v_lhs_1626_ = _args[1];
lean_object* v_rhs_1627_ = _args[2];
lean_object* v_strict_1628_ = _args[3];
lean_object* v_eqTrue_1629_ = _args[4];
lean_object* v_a_1630_ = _args[5];
lean_object* v_a_1631_ = _args[6];
lean_object* v_a_1632_ = _args[7];
lean_object* v_a_1633_ = _args[8];
lean_object* v_a_1634_ = _args[9];
lean_object* v_a_1635_ = _args[10];
lean_object* v_a_1636_ = _args[11];
lean_object* v_a_1637_ = _args[12];
lean_object* v_a_1638_ = _args[13];
lean_object* v_a_1639_ = _args[14];
lean_object* v_a_1640_ = _args[15];
lean_object* v_a_1641_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1642_; uint8_t v_eqTrue_boxed_1643_; lean_object* v_res_1644_; 
v_strict_boxed_1642_ = lean_unbox(v_strict_1628_);
v_eqTrue_boxed_1643_ = lean_unbox(v_eqTrue_1629_);
v_res_1644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1625_, v_lhs_1626_, v_rhs_1627_, v_strict_boxed_1642_, v_eqTrue_boxed_1643_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec(v_a_1630_);
return v_res_1644_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 0)
{
if (lean_obj_tag(v_x_1646_) == 0)
{
uint8_t v___x_1647_; 
v___x_1647_ = 1;
return v___x_1647_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = 0;
return v___x_1648_;
}
}
else
{
if (lean_obj_tag(v_x_1646_) == 0)
{
uint8_t v___x_1649_; 
v___x_1649_ = 0;
return v___x_1649_;
}
else
{
lean_object* v_val_1650_; lean_object* v_val_1651_; uint8_t v___x_1652_; 
v_val_1650_ = lean_ctor_get(v_x_1645_, 0);
v_val_1651_ = lean_ctor_get(v_x_1646_, 0);
v___x_1652_ = lean_expr_eqv(v_val_1650_, v_val_1651_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1653_, v_x_1654_);
lean_dec(v_x_1654_);
lean_dec(v_x_1653_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0(lean_object* v_val_1657_, lean_object* v_e_1658_, lean_object* v_s_1659_){
_start:
{
lean_object* v_structs_1660_; lean_object* v_typeIdOf_1661_; lean_object* v_exprToStructId_1662_; lean_object* v_exprToStructIdEntries_1663_; lean_object* v_forbiddenNatModules_1664_; lean_object* v_natStructs_1665_; lean_object* v_natTypeIdOf_1666_; lean_object* v_exprToNatStructId_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_structs_1660_ = lean_ctor_get(v_s_1659_, 0);
v_typeIdOf_1661_ = lean_ctor_get(v_s_1659_, 1);
v_exprToStructId_1662_ = lean_ctor_get(v_s_1659_, 2);
v_exprToStructIdEntries_1663_ = lean_ctor_get(v_s_1659_, 3);
v_forbiddenNatModules_1664_ = lean_ctor_get(v_s_1659_, 4);
v_natStructs_1665_ = lean_ctor_get(v_s_1659_, 5);
v_natTypeIdOf_1666_ = lean_ctor_get(v_s_1659_, 6);
v_exprToNatStructId_1667_ = lean_ctor_get(v_s_1659_, 7);
v___x_1668_ = lean_array_get_size(v_structs_1660_);
v___x_1669_ = lean_nat_dec_lt(v_val_1657_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec_ref(v_e_1658_);
return v_s_1659_;
}
else
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1731_; 
lean_inc_ref(v_exprToNatStructId_1667_);
lean_inc_ref(v_natTypeIdOf_1666_);
lean_inc_ref(v_natStructs_1665_);
lean_inc_ref(v_forbiddenNatModules_1664_);
lean_inc_ref(v_exprToStructIdEntries_1663_);
lean_inc_ref(v_exprToStructId_1662_);
lean_inc_ref(v_typeIdOf_1661_);
lean_inc_ref(v_structs_1660_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_s_1659_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; lean_object* v_unused_1739_; 
v_unused_1732_ = lean_ctor_get(v_s_1659_, 7);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_s_1659_, 6);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_s_1659_, 5);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_s_1659_, 4);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_s_1659_, 3);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_s_1659_, 2);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_s_1659_, 1);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v_s_1659_, 0);
lean_dec(v_unused_1739_);
v___x_1671_ = v_s_1659_;
v_isShared_1672_ = v_isSharedCheck_1731_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v_s_1659_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1731_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_v_1673_; lean_object* v_id_1674_; lean_object* v_ringId_x3f_1675_; lean_object* v_type_1676_; lean_object* v_u_1677_; lean_object* v_intModuleInst_1678_; lean_object* v_leInst_x3f_1679_; lean_object* v_ltInst_x3f_1680_; lean_object* v_lawfulOrderLTInst_x3f_1681_; lean_object* v_isPreorderInst_x3f_1682_; lean_object* v_orderedAddInst_x3f_1683_; lean_object* v_isLinearInst_x3f_1684_; lean_object* v_noNatDivInst_x3f_1685_; lean_object* v_ringInst_x3f_1686_; lean_object* v_commRingInst_x3f_1687_; lean_object* v_orderedRingInst_x3f_1688_; lean_object* v_fieldInst_x3f_1689_; lean_object* v_charInst_x3f_1690_; lean_object* v_zero_1691_; lean_object* v_ofNatZero_1692_; lean_object* v_one_x3f_1693_; lean_object* v_leFn_x3f_1694_; lean_object* v_ltFn_x3f_1695_; lean_object* v_addFn_1696_; lean_object* v_zsmulFn_1697_; lean_object* v_nsmulFn_1698_; lean_object* v_zsmulFn_x3f_1699_; lean_object* v_nsmulFn_x3f_1700_; lean_object* v_homomulFn_x3f_1701_; lean_object* v_subFn_1702_; lean_object* v_negFn_1703_; lean_object* v_vars_1704_; lean_object* v_varMap_1705_; lean_object* v_lowers_1706_; lean_object* v_uppers_1707_; lean_object* v_diseqs_1708_; lean_object* v_assignment_1709_; uint8_t v_caseSplits_1710_; lean_object* v_conflict_x3f_1711_; lean_object* v_diseqSplits_1712_; lean_object* v_elimEqs_1713_; lean_object* v_elimStack_1714_; lean_object* v_occurs_1715_; lean_object* v_ignored_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1730_; 
v_v_1673_ = lean_array_fget(v_structs_1660_, v_val_1657_);
v_id_1674_ = lean_ctor_get(v_v_1673_, 0);
v_ringId_x3f_1675_ = lean_ctor_get(v_v_1673_, 1);
v_type_1676_ = lean_ctor_get(v_v_1673_, 2);
v_u_1677_ = lean_ctor_get(v_v_1673_, 3);
v_intModuleInst_1678_ = lean_ctor_get(v_v_1673_, 4);
v_leInst_x3f_1679_ = lean_ctor_get(v_v_1673_, 5);
v_ltInst_x3f_1680_ = lean_ctor_get(v_v_1673_, 6);
v_lawfulOrderLTInst_x3f_1681_ = lean_ctor_get(v_v_1673_, 7);
v_isPreorderInst_x3f_1682_ = lean_ctor_get(v_v_1673_, 8);
v_orderedAddInst_x3f_1683_ = lean_ctor_get(v_v_1673_, 9);
v_isLinearInst_x3f_1684_ = lean_ctor_get(v_v_1673_, 10);
v_noNatDivInst_x3f_1685_ = lean_ctor_get(v_v_1673_, 11);
v_ringInst_x3f_1686_ = lean_ctor_get(v_v_1673_, 12);
v_commRingInst_x3f_1687_ = lean_ctor_get(v_v_1673_, 13);
v_orderedRingInst_x3f_1688_ = lean_ctor_get(v_v_1673_, 14);
v_fieldInst_x3f_1689_ = lean_ctor_get(v_v_1673_, 15);
v_charInst_x3f_1690_ = lean_ctor_get(v_v_1673_, 16);
v_zero_1691_ = lean_ctor_get(v_v_1673_, 17);
v_ofNatZero_1692_ = lean_ctor_get(v_v_1673_, 18);
v_one_x3f_1693_ = lean_ctor_get(v_v_1673_, 19);
v_leFn_x3f_1694_ = lean_ctor_get(v_v_1673_, 20);
v_ltFn_x3f_1695_ = lean_ctor_get(v_v_1673_, 21);
v_addFn_1696_ = lean_ctor_get(v_v_1673_, 22);
v_zsmulFn_1697_ = lean_ctor_get(v_v_1673_, 23);
v_nsmulFn_1698_ = lean_ctor_get(v_v_1673_, 24);
v_zsmulFn_x3f_1699_ = lean_ctor_get(v_v_1673_, 25);
v_nsmulFn_x3f_1700_ = lean_ctor_get(v_v_1673_, 26);
v_homomulFn_x3f_1701_ = lean_ctor_get(v_v_1673_, 27);
v_subFn_1702_ = lean_ctor_get(v_v_1673_, 28);
v_negFn_1703_ = lean_ctor_get(v_v_1673_, 29);
v_vars_1704_ = lean_ctor_get(v_v_1673_, 30);
v_varMap_1705_ = lean_ctor_get(v_v_1673_, 31);
v_lowers_1706_ = lean_ctor_get(v_v_1673_, 32);
v_uppers_1707_ = lean_ctor_get(v_v_1673_, 33);
v_diseqs_1708_ = lean_ctor_get(v_v_1673_, 34);
v_assignment_1709_ = lean_ctor_get(v_v_1673_, 35);
v_caseSplits_1710_ = lean_ctor_get_uint8(v_v_1673_, sizeof(void*)*42);
v_conflict_x3f_1711_ = lean_ctor_get(v_v_1673_, 36);
v_diseqSplits_1712_ = lean_ctor_get(v_v_1673_, 37);
v_elimEqs_1713_ = lean_ctor_get(v_v_1673_, 38);
v_elimStack_1714_ = lean_ctor_get(v_v_1673_, 39);
v_occurs_1715_ = lean_ctor_get(v_v_1673_, 40);
v_ignored_1716_ = lean_ctor_get(v_v_1673_, 41);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_v_1673_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1718_ = v_v_1673_;
v_isShared_1719_ = v_isSharedCheck_1730_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_ignored_1716_);
lean_inc(v_occurs_1715_);
lean_inc(v_elimStack_1714_);
lean_inc(v_elimEqs_1713_);
lean_inc(v_diseqSplits_1712_);
lean_inc(v_conflict_x3f_1711_);
lean_inc(v_assignment_1709_);
lean_inc(v_diseqs_1708_);
lean_inc(v_uppers_1707_);
lean_inc(v_lowers_1706_);
lean_inc(v_varMap_1705_);
lean_inc(v_vars_1704_);
lean_inc(v_negFn_1703_);
lean_inc(v_subFn_1702_);
lean_inc(v_homomulFn_x3f_1701_);
lean_inc(v_nsmulFn_x3f_1700_);
lean_inc(v_zsmulFn_x3f_1699_);
lean_inc(v_nsmulFn_1698_);
lean_inc(v_zsmulFn_1697_);
lean_inc(v_addFn_1696_);
lean_inc(v_ltFn_x3f_1695_);
lean_inc(v_leFn_x3f_1694_);
lean_inc(v_one_x3f_1693_);
lean_inc(v_ofNatZero_1692_);
lean_inc(v_zero_1691_);
lean_inc(v_charInst_x3f_1690_);
lean_inc(v_fieldInst_x3f_1689_);
lean_inc(v_orderedRingInst_x3f_1688_);
lean_inc(v_commRingInst_x3f_1687_);
lean_inc(v_ringInst_x3f_1686_);
lean_inc(v_noNatDivInst_x3f_1685_);
lean_inc(v_isLinearInst_x3f_1684_);
lean_inc(v_orderedAddInst_x3f_1683_);
lean_inc(v_isPreorderInst_x3f_1682_);
lean_inc(v_lawfulOrderLTInst_x3f_1681_);
lean_inc(v_ltInst_x3f_1680_);
lean_inc(v_leInst_x3f_1679_);
lean_inc(v_intModuleInst_1678_);
lean_inc(v_u_1677_);
lean_inc(v_type_1676_);
lean_inc(v_ringId_x3f_1675_);
lean_inc(v_id_1674_);
lean_dec(v_v_1673_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1730_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v_xs_x27_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1720_ = lean_box(0);
v_xs_x27_1721_ = lean_array_fset(v_structs_1660_, v_val_1657_, v___x_1720_);
v___x_1722_ = l_Lean_PersistentArray_push___redArg(v_ignored_1716_, v_e_1658_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 41, v___x_1722_);
v___x_1724_ = v___x_1718_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_id_1674_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_ringId_x3f_1675_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_type_1676_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_u_1677_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_intModuleInst_1678_);
lean_ctor_set(v_reuseFailAlloc_1729_, 5, v_leInst_x3f_1679_);
lean_ctor_set(v_reuseFailAlloc_1729_, 6, v_ltInst_x3f_1680_);
lean_ctor_set(v_reuseFailAlloc_1729_, 7, v_lawfulOrderLTInst_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1729_, 8, v_isPreorderInst_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1729_, 9, v_orderedAddInst_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1729_, 10, v_isLinearInst_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1729_, 11, v_noNatDivInst_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1729_, 12, v_ringInst_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1729_, 13, v_commRingInst_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1729_, 14, v_orderedRingInst_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1729_, 15, v_fieldInst_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1729_, 16, v_charInst_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1729_, 17, v_zero_1691_);
lean_ctor_set(v_reuseFailAlloc_1729_, 18, v_ofNatZero_1692_);
lean_ctor_set(v_reuseFailAlloc_1729_, 19, v_one_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1729_, 20, v_leFn_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1729_, 21, v_ltFn_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1729_, 22, v_addFn_1696_);
lean_ctor_set(v_reuseFailAlloc_1729_, 23, v_zsmulFn_1697_);
lean_ctor_set(v_reuseFailAlloc_1729_, 24, v_nsmulFn_1698_);
lean_ctor_set(v_reuseFailAlloc_1729_, 25, v_zsmulFn_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1729_, 26, v_nsmulFn_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1729_, 27, v_homomulFn_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1729_, 28, v_subFn_1702_);
lean_ctor_set(v_reuseFailAlloc_1729_, 29, v_negFn_1703_);
lean_ctor_set(v_reuseFailAlloc_1729_, 30, v_vars_1704_);
lean_ctor_set(v_reuseFailAlloc_1729_, 31, v_varMap_1705_);
lean_ctor_set(v_reuseFailAlloc_1729_, 32, v_lowers_1706_);
lean_ctor_set(v_reuseFailAlloc_1729_, 33, v_uppers_1707_);
lean_ctor_set(v_reuseFailAlloc_1729_, 34, v_diseqs_1708_);
lean_ctor_set(v_reuseFailAlloc_1729_, 35, v_assignment_1709_);
lean_ctor_set(v_reuseFailAlloc_1729_, 36, v_conflict_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1729_, 37, v_diseqSplits_1712_);
lean_ctor_set(v_reuseFailAlloc_1729_, 38, v_elimEqs_1713_);
lean_ctor_set(v_reuseFailAlloc_1729_, 39, v_elimStack_1714_);
lean_ctor_set(v_reuseFailAlloc_1729_, 40, v_occurs_1715_);
lean_ctor_set(v_reuseFailAlloc_1729_, 41, v___x_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1729_, sizeof(void*)*42, v_caseSplits_1710_);
v___x_1724_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_array_fset(v_xs_x27_1721_, v_val_1657_, v___x_1724_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1725_);
v___x_1727_ = v___x_1671_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_typeIdOf_1661_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_exprToStructId_1662_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_exprToStructIdEntries_1663_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_forbiddenNatModules_1664_);
lean_ctor_set(v_reuseFailAlloc_1728_, 5, v_natStructs_1665_);
lean_ctor_set(v_reuseFailAlloc_1728_, 6, v_natTypeIdOf_1666_);
lean_ctor_set(v_reuseFailAlloc_1728_, 7, v_exprToNatStructId_1667_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0___boxed(lean_object* v_val_1740_, lean_object* v_e_1741_, lean_object* v_s_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0(v_val_1740_, v_e_1741_, v_s_1742_);
lean_dec(v_val_1740_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1744_, uint8_t v_eqTrue_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1748_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1960_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1960_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1960_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v_linarith_1762_; 
v_linarith_1762_ = lean_ctor_get_uint8(v_a_1758_, sizeof(void*)*14 + 23);
lean_dec(v_a_1758_);
if (v_linarith_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref(v_e_1744_);
v___x_1763_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_Expr_getAppNumArgs(v_e_1744_);
v___x_1768_ = lean_unsigned_to_nat(4u);
v___x_1769_ = lean_nat_dec_eq(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v___x_1767_);
lean_dec_ref(v_e_1744_);
v___x_1770_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1770_);
v___x_1772_ = v___x_1760_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___x_1813_; 
lean_del_object(v___x_1760_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_sub(v___x_1767_, v___x_1774_);
lean_inc(v___x_1775_);
v___x_1776_ = l_Lean_Expr_getRevArg_x21(v_e_1744_, v___x_1775_);
v___x_1777_ = lean_nat_sub(v___x_1775_, v___x_1774_);
lean_dec(v___x_1775_);
v___x_1778_ = l_Lean_Expr_getRevArg_x21(v_e_1744_, v___x_1777_);
v___x_1779_ = lean_unsigned_to_nat(2u);
v___x_1780_ = lean_nat_sub(v___x_1767_, v___x_1779_);
v___x_1781_ = lean_nat_sub(v___x_1780_, v___x_1774_);
lean_dec(v___x_1780_);
v___x_1782_ = l_Lean_Expr_getRevArg_x21(v_e_1744_, v___x_1781_);
v___x_1783_ = lean_unsigned_to_nat(3u);
v___x_1784_ = lean_nat_sub(v___x_1767_, v___x_1783_);
lean_dec(v___x_1767_);
v___x_1785_ = lean_nat_sub(v___x_1784_, v___x_1774_);
lean_dec(v___x_1784_);
v___x_1786_ = l_Lean_Expr_getRevArg_x21(v_e_1744_, v___x_1785_);
lean_inc_ref(v___x_1776_);
v___x_1813_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1776_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1951_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1951_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1951_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
if (lean_obj_tag(v_a_1814_) == 1)
{
lean_object* v_val_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1776_);
v_val_1818_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v_a_1814_, 1);
v___x_1819_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1818_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1846_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1846_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1846_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_lawfulOrderLTInst_x3f_1824_; lean_object* v_leFn_x3f_1825_; lean_object* v_ltFn_x3f_1826_; uint8_t v___x_1827_; 
v_lawfulOrderLTInst_x3f_1824_ = lean_ctor_get(v_a_1820_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1824_);
v_leFn_x3f_1825_ = lean_ctor_get(v_a_1820_, 20);
lean_inc(v_leFn_x3f_1825_);
v_ltFn_x3f_1826_ = lean_ctor_get(v_a_1820_, 21);
lean_inc(v_ltFn_x3f_1826_);
lean_dec(v_a_1820_);
v___x_1827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1825_, v___x_1778_);
lean_dec(v_leFn_x3f_1825_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1826_, v___x_1778_);
lean_dec_ref(v___x_1778_);
lean_dec(v_ltFn_x3f_1826_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec(v_lawfulOrderLTInst_x3f_1824_);
lean_dec(v_val_1818_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_e_1744_);
v___x_1829_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1829_);
v___x_1831_ = v___x_1822_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_del_object(v___x_1822_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1824_) == 0)
{
lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_propagateIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1833_, 0, v_val_1818_);
lean_closure_set(v___f_1833_, 1, v_e_1744_);
v___x_1834_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1835_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1834_, v___f_1833_, v_a_1746_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v___x_1835_, 0);
lean_dec(v_unused_1844_);
v___x_1837_ = v___x_1835_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_dec(v___x_1835_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_box(0);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
return v___x_1835_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1824_, 1);
v___y_1788_ = v_a_1746_;
v___y_1789_ = v_a_1751_;
v___y_1790_ = v_a_1747_;
v___y_1791_ = v_a_1753_;
v___y_1792_ = v_a_1750_;
v___y_1793_ = v___x_1769_;
v___y_1794_ = v_val_1818_;
v___y_1795_ = v_a_1754_;
v___y_1796_ = v_a_1755_;
v___y_1797_ = v_a_1748_;
v___y_1798_ = v_a_1752_;
v___y_1799_ = v_a_1749_;
goto v___jp_1787_;
}
}
}
else
{
uint8_t v___x_1845_; 
lean_dec(v_ltFn_x3f_1826_);
lean_dec(v_lawfulOrderLTInst_x3f_1824_);
lean_del_object(v___x_1822_);
lean_dec_ref(v___x_1778_);
v___x_1845_ = 0;
v___y_1788_ = v_a_1746_;
v___y_1789_ = v_a_1751_;
v___y_1790_ = v_a_1747_;
v___y_1791_ = v_a_1753_;
v___y_1792_ = v_a_1750_;
v___y_1793_ = v___x_1845_;
v___y_1794_ = v_val_1818_;
v___y_1795_ = v_a_1754_;
v___y_1796_ = v_a_1755_;
v___y_1797_ = v_a_1748_;
v___y_1798_ = v_a_1752_;
v___y_1799_ = v_a_1749_;
goto v___jp_1787_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_val_1818_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
v_a_1847_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1819_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1819_);
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
lean_object* v___x_1855_; 
lean_dec(v_a_1814_);
v___x_1855_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1776_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1942_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1942_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1942_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
if (lean_obj_tag(v_a_1856_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1861_; 
v_val_1860_ = lean_ctor_get(v_a_1856_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v_a_1856_, 1);
v___x_1861_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1860_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1929_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1929_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1929_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_leInst_x3f_1871_; lean_object* v_ltInst_x3f_1872_; lean_object* v_lawfulOrderLTInst_x3f_1873_; lean_object* v_isPreorderInst_x3f_1874_; lean_object* v_orderedAddInst_x3f_1875_; lean_object* v_isLinearInst_x3f_1876_; lean_object* v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1896_; lean_object* v___y_1897_; uint8_t v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1908_; 
v_leInst_x3f_1871_ = lean_ctor_get(v_a_1862_, 5);
lean_inc(v_leInst_x3f_1871_);
v_ltInst_x3f_1872_ = lean_ctor_get(v_a_1862_, 6);
lean_inc(v_ltInst_x3f_1872_);
v_lawfulOrderLTInst_x3f_1873_ = lean_ctor_get(v_a_1862_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1873_);
v_isPreorderInst_x3f_1874_ = lean_ctor_get(v_a_1862_, 8);
lean_inc(v_isPreorderInst_x3f_1874_);
v_orderedAddInst_x3f_1875_ = lean_ctor_get(v_a_1862_, 9);
lean_inc(v_orderedAddInst_x3f_1875_);
v_isLinearInst_x3f_1876_ = lean_ctor_get(v_a_1862_, 10);
lean_inc(v_isLinearInst_x3f_1876_);
lean_dec(v_a_1862_);
if (lean_obj_tag(v_leInst_x3f_1871_) == 0)
{
lean_dec(v_isLinearInst_x3f_1876_);
lean_dec(v_orderedAddInst_x3f_1875_);
lean_dec(v_isPreorderInst_x3f_1874_);
lean_dec(v_lawfulOrderLTInst_x3f_1873_);
lean_dec(v_ltInst_x3f_1872_);
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
goto v___jp_1866_;
}
else
{
if (lean_obj_tag(v_isPreorderInst_x3f_1874_) == 0)
{
lean_dec_ref_known(v_leInst_x3f_1871_, 1);
lean_dec(v_isLinearInst_x3f_1876_);
lean_dec(v_orderedAddInst_x3f_1875_);
lean_dec(v_lawfulOrderLTInst_x3f_1873_);
lean_dec(v_ltInst_x3f_1872_);
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
goto v___jp_1866_;
}
else
{
lean_dec_ref_known(v_isPreorderInst_x3f_1874_, 1);
if (lean_obj_tag(v_orderedAddInst_x3f_1875_) == 0)
{
lean_dec_ref_known(v_leInst_x3f_1871_, 1);
lean_dec(v_isLinearInst_x3f_1876_);
lean_dec(v_lawfulOrderLTInst_x3f_1873_);
lean_dec(v_ltInst_x3f_1872_);
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
goto v___jp_1866_;
}
else
{
lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1927_; 
lean_del_object(v___x_1864_);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_orderedAddInst_x3f_1875_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_orderedAddInst_x3f_1875_, 0);
lean_dec(v_unused_1928_);
v___x_1911_ = v_orderedAddInst_x3f_1875_;
v_isShared_1912_ = v_isSharedCheck_1927_;
goto v_resetjp_1910_;
}
else
{
lean_dec(v_orderedAddInst_x3f_1875_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1927_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
uint8_t v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = 0;
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1778_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1778_);
v___x_1915_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1915_, v_leInst_x3f_1871_);
lean_dec_ref_known(v_leInst_x3f_1871_, 1);
if (v___x_1916_ == 0)
{
uint8_t v___x_1917_; 
v___x_1917_ = l_instBEqOption_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1915_, v_ltInst_x3f_1872_);
lean_dec(v_ltInst_x3f_1872_);
lean_dec_ref(v___x_1915_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec(v_isLinearInst_x3f_1876_);
lean_dec(v_lawfulOrderLTInst_x3f_1873_);
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_e_1744_);
v___x_1918_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1918_);
v___x_1920_ = v___x_1816_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1873_) == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec(v_isLinearInst_x3f_1876_);
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_e_1744_);
v___x_1922_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1922_);
v___x_1924_ = v___x_1816_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1873_, 1);
lean_del_object(v___x_1816_);
v___y_1896_ = v_a_1748_;
v___y_1897_ = v_a_1750_;
v___y_1898_ = v___x_1769_;
v___y_1899_ = v_val_1860_;
v___y_1900_ = v_a_1749_;
v___y_1901_ = v_a_1752_;
v___y_1902_ = v_a_1753_;
v___y_1903_ = v_a_1746_;
v___y_1904_ = v_a_1747_;
v___y_1905_ = v_a_1751_;
v___y_1906_ = v_a_1755_;
v___y_1907_ = v_a_1754_;
v___y_1908_ = v___x_1913_;
goto v___jp_1895_;
}
}
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec(v_lawfulOrderLTInst_x3f_1873_);
lean_dec(v_ltInst_x3f_1872_);
lean_del_object(v___x_1816_);
v___y_1896_ = v_a_1748_;
v___y_1897_ = v_a_1750_;
v___y_1898_ = v___x_1913_;
v___y_1899_ = v_val_1860_;
v___y_1900_ = v_a_1749_;
v___y_1901_ = v_a_1752_;
v___y_1902_ = v_a_1753_;
v___y_1903_ = v_a_1746_;
v___y_1904_ = v_a_1747_;
v___y_1905_ = v_a_1751_;
v___y_1906_ = v_a_1755_;
v___y_1907_ = v_a_1754_;
v___y_1908_ = v___x_1913_;
goto v___jp_1895_;
}
}
}
}
}
}
v___jp_1866_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1867_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
v___jp_1877_:
{
if (lean_obj_tag(v_isLinearInst_x3f_1876_) == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_dec(v___y_1881_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_e_1744_);
v___x_1890_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1890_);
v___x_1892_ = v___x_1858_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
else
{
lean_object* v___x_1894_; 
lean_dec_ref_known(v_isLinearInst_x3f_1876_, 1);
lean_del_object(v___x_1858_);
v___x_1894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1744_, v___x_1782_, v___x_1786_, v___y_1880_, v_eqTrue_1745_, v___y_1881_, v___y_1885_, v___y_1886_, v___y_1878_, v___y_1882_, v___y_1879_, v___y_1887_, v___y_1883_, v___y_1884_, v___y_1889_, v___y_1888_);
lean_dec(v___y_1881_);
return v___x_1894_;
}
}
v___jp_1895_:
{
if (v_eqTrue_1745_ == 0)
{
v___y_1878_ = v___y_1896_;
v___y_1879_ = v___y_1897_;
v___y_1880_ = v___y_1898_;
v___y_1881_ = v___y_1899_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1901_;
v___y_1884_ = v___y_1902_;
v___y_1885_ = v___y_1903_;
v___y_1886_ = v___y_1904_;
v___y_1887_ = v___y_1905_;
v___y_1888_ = v___y_1906_;
v___y_1889_ = v___y_1907_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1909_; 
lean_dec(v_isLinearInst_x3f_1876_);
lean_del_object(v___x_1858_);
v___x_1909_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1744_, v___x_1782_, v___x_1786_, v___y_1898_, v_eqTrue_1745_, v___y_1899_, v___y_1903_, v___y_1904_, v___y_1896_, v___y_1900_, v___y_1897_, v___y_1905_, v___y_1901_, v___y_1902_, v___y_1907_, v___y_1906_);
lean_dec(v___y_1899_);
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_val_1860_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
v_a_1930_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1861_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1861_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v_a_1856_);
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
v___x_1938_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1938_);
v___x_1940_ = v___x_1858_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1816_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1744_);
v_a_1943_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1855_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1855_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v_e_1744_);
v_a_1952_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1813_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1813_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
v___jp_1787_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1794_, v___y_1788_, v___y_1790_, v___y_1797_, v___y_1799_, v___y_1792_, v___y_1789_, v___y_1798_, v___y_1791_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; uint8_t v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1744_, v___x_1782_, v___x_1786_, v___y_1793_, v_eqTrue_1745_, v___y_1794_, v___y_1788_, v___y_1790_, v___y_1797_, v___y_1799_, v___y_1792_, v___y_1789_, v___y_1798_, v___y_1791_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1794_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1744_, v___x_1782_, v___x_1786_, v___y_1793_, v_eqTrue_1745_, v___y_1794_, v___y_1788_, v___y_1790_, v___y_1797_, v___y_1799_, v___y_1792_, v___y_1789_, v___y_1798_, v___y_1791_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1794_);
return v___x_1804_;
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v___y_1794_);
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_e_1744_);
v_a_1805_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1800_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1800_);
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
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_e_1744_);
v_a_1961_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1757_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1757_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1969_, lean_object* v_eqTrue_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
uint8_t v_eqTrue_boxed_1982_; lean_object* v_res_1983_; 
v_eqTrue_boxed_1982_ = lean_unbox(v_eqTrue_1970_);
v_res_1983_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1969_, v_eqTrue_boxed_1982_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec(v_a_1971_);
return v_res_1983_;
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
