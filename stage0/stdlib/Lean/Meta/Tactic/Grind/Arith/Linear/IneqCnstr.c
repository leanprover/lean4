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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__6_value),LEAN_SCALAR_PTR_LITERAL(30, 205, 246, 167, 183, 132, 208, 174)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(lean_object* v_cls_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_options_17_; uint8_t v_hasTrace_18_; 
v_options_17_ = lean_ctor_get(v___y_15_, 2);
v_hasTrace_18_ = lean_ctor_get_uint8(v_options_17_, sizeof(void*)*1);
if (v_hasTrace_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_cls_14_);
v___x_19_ = lean_box(v_hasTrace_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
else
{
lean_object* v_inheritedTraceOptions_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_inheritedTraceOptions_21_ = lean_ctor_get(v___y_15_, 13);
v___x_22_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1));
v___x_23_ = l_Lean_Name_append(v___x_22_, v_cls_14_);
v___x_24_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_21_, v_options_17_, v___x_23_);
lean_dec(v___x_23_);
v___x_25_ = lean_box(v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___boxed(lean_object* v_cls_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v_cls_27_, v___y_28_);
lean_dec_ref(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* v_cls_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v_cls_31_, v___y_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* v_cls_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(v_cls_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec(v___y_47_);
lean_dec(v___y_46_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(lean_object* v_c_59_, lean_object* v_x_60_, size_t v_x_61_, size_t v_x_62_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_cs_63_; size_t v_j_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_cs_63_ = lean_ctor_get(v_x_60_, 0);
v_j_64_ = lean_usize_shift_right(v_x_61_, v_x_62_);
v___x_65_ = lean_usize_to_nat(v_j_64_);
v___x_66_ = lean_array_get_size(v_cs_63_);
v___x_67_ = lean_nat_dec_lt(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec(v___x_65_);
lean_dec_ref(v_c_59_);
return v_x_60_;
}
else
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_85_; 
lean_inc_ref(v_cs_63_);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_x_60_, 0);
lean_dec(v_unused_86_);
v___x_69_ = v_x_60_;
v_isShared_70_ = v_isSharedCheck_85_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_x_60_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_85_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v_i_74_; size_t v___x_75_; size_t v_shift_76_; lean_object* v_v_77_; lean_object* v___x_78_; lean_object* v_xs_x27_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_shift_left(v___x_71_, v_x_62_);
v___x_73_ = lean_usize_sub(v___x_72_, v___x_71_);
v_i_74_ = lean_usize_land(v_x_61_, v___x_73_);
v___x_75_ = ((size_t)5ULL);
v_shift_76_ = lean_usize_sub(v_x_62_, v___x_75_);
v_v_77_ = lean_array_fget(v_cs_63_, v___x_65_);
v___x_78_ = lean_box(0);
v_xs_x27_79_ = lean_array_fset(v_cs_63_, v___x_65_, v___x_78_);
v___x_80_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(v_c_59_, v_v_77_, v_i_74_, v_shift_76_);
v___x_81_ = lean_array_fset(v_xs_x27_79_, v___x_65_, v___x_80_);
lean_dec(v___x_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_81_);
v___x_83_ = v___x_69_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
else
{
lean_object* v_vs_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_vs_87_ = lean_ctor_get(v_x_60_, 0);
v___x_88_ = lean_usize_to_nat(v_x_61_);
v___x_89_ = lean_array_get_size(v_vs_87_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v___x_88_);
lean_dec_ref(v_c_59_);
return v_x_60_;
}
else
{
lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_vs_87_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_x_60_, 0);
lean_dec(v_unused_103_);
v___x_92_ = v_x_60_;
v_isShared_93_ = v_isSharedCheck_102_;
goto v_resetjp_91_;
}
else
{
lean_dec(v_x_60_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_102_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_v_94_; lean_object* v___x_95_; lean_object* v_xs_x27_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v_v_94_ = lean_array_fget(v_vs_87_, v___x_88_);
v___x_95_ = lean_box(0);
v_xs_x27_96_ = lean_array_fset(v_vs_87_, v___x_88_, v___x_95_);
v___x_97_ = l_Lean_PersistentArray_push___redArg(v_v_94_, v_c_59_);
v___x_98_ = lean_array_fset(v_xs_x27_96_, v___x_88_, v___x_97_);
lean_dec(v___x_88_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_98_);
v___x_100_ = v___x_92_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg___boxed(lean_object* v_c_104_, lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
size_t v_x_68087__boxed_108_; size_t v_x_68088__boxed_109_; lean_object* v_res_110_; 
v_x_68087__boxed_108_ = lean_unbox_usize(v_x_106_);
lean_dec(v_x_106_);
v_x_68088__boxed_109_ = lean_unbox_usize(v_x_107_);
lean_dec(v_x_107_);
v_res_110_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(v_c_104_, v_x_105_, v_x_68087__boxed_108_, v_x_68088__boxed_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(lean_object* v_c_111_, lean_object* v_inst_112_, lean_object* v_t_113_, lean_object* v_i_114_){
_start:
{
lean_object* v_root_115_; lean_object* v_tail_116_; lean_object* v_size_117_; size_t v_shift_118_; lean_object* v_tailOff_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_root_115_ = lean_ctor_get(v_t_113_, 0);
v_tail_116_ = lean_ctor_get(v_t_113_, 1);
v_size_117_ = lean_ctor_get(v_t_113_, 2);
v_shift_118_ = lean_ctor_get_usize(v_t_113_, 4);
v_tailOff_119_ = lean_ctor_get(v_t_113_, 3);
v_isSharedCheck_143_ = !lean_is_exclusive(v_t_113_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v_t_113_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_tailOff_119_);
lean_inc(v_size_117_);
lean_inc(v_tail_116_);
lean_inc(v_root_115_);
lean_dec(v_t_113_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_le(v_tailOff_119_, v_i_114_);
if (v___x_123_ == 0)
{
size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_124_ = lean_usize_of_nat(v_i_114_);
v___x_125_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(v_c_111_, v_root_115_, v___x_124_, v_shift_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_125_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_tail_116_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_size_117_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_tailOff_119_);
lean_ctor_set_usize(v_reuseFailAlloc_128_, 4, v_shift_118_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = lean_nat_sub(v_i_114_, v_tailOff_119_);
v___x_130_ = lean_array_get_size(v_tail_116_);
v___x_131_ = lean_nat_dec_lt(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_133_; 
lean_dec(v___x_129_);
lean_dec_ref(v_c_111_);
if (v_isShared_122_ == 0)
{
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_root_115_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_tail_116_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_size_117_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_tailOff_119_);
lean_ctor_set_usize(v_reuseFailAlloc_134_, 4, v_shift_118_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v_v_135_; lean_object* v___x_136_; lean_object* v_xs_x27_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v_v_135_ = lean_array_fget(v_tail_116_, v___x_129_);
v___x_136_ = lean_box(0);
v_xs_x27_137_ = lean_array_fset(v_tail_116_, v___x_129_, v___x_136_);
v___x_138_ = l_Lean_PersistentArray_push___redArg(v_v_135_, v_c_111_);
v___x_139_ = lean_array_fset(v_xs_x27_137_, v___x_129_, v___x_138_);
lean_dec(v___x_129_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_139_);
v___x_141_ = v___x_121_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_root_115_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_size_117_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_tailOff_119_);
lean_ctor_set_usize(v_reuseFailAlloc_142_, 4, v_shift_118_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3___boxed(lean_object* v_c_144_, lean_object* v_inst_145_, lean_object* v_t_146_, lean_object* v_i_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(v_c_144_, v_inst_145_, v_t_146_, v_i_147_);
lean_dec(v_i_147_);
lean_dec_ref(v_inst_145_);
return v_res_148_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object* v___y_150_, lean_object* v_c_151_, lean_object* v_v_152_, lean_object* v_s_153_){
_start:
{
lean_object* v_structs_154_; lean_object* v_typeIdOf_155_; lean_object* v_exprToStructId_156_; lean_object* v_exprToStructIdEntries_157_; lean_object* v_forbiddenNatModules_158_; lean_object* v_natStructs_159_; lean_object* v_natTypeIdOf_160_; lean_object* v_exprToNatStructId_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_structs_154_ = lean_ctor_get(v_s_153_, 0);
v_typeIdOf_155_ = lean_ctor_get(v_s_153_, 1);
v_exprToStructId_156_ = lean_ctor_get(v_s_153_, 2);
v_exprToStructIdEntries_157_ = lean_ctor_get(v_s_153_, 3);
v_forbiddenNatModules_158_ = lean_ctor_get(v_s_153_, 4);
v_natStructs_159_ = lean_ctor_get(v_s_153_, 5);
v_natTypeIdOf_160_ = lean_ctor_get(v_s_153_, 6);
v_exprToNatStructId_161_ = lean_ctor_get(v_s_153_, 7);
v___x_162_ = lean_array_get_size(v_structs_154_);
v___x_163_ = lean_nat_dec_lt(v___y_150_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec_ref(v_c_151_);
return v_s_153_;
}
else
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_226_; 
lean_inc_ref(v_exprToNatStructId_161_);
lean_inc_ref(v_natTypeIdOf_160_);
lean_inc_ref(v_natStructs_159_);
lean_inc_ref(v_forbiddenNatModules_158_);
lean_inc_ref(v_exprToStructIdEntries_157_);
lean_inc_ref(v_exprToStructId_156_);
lean_inc_ref(v_typeIdOf_155_);
lean_inc_ref(v_structs_154_);
v_isSharedCheck_226_ = !lean_is_exclusive(v_s_153_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_227_ = lean_ctor_get(v_s_153_, 7);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_s_153_, 6);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_s_153_, 5);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_s_153_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_s_153_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_s_153_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_s_153_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_s_153_, 0);
lean_dec(v_unused_234_);
v___x_165_ = v_s_153_;
v_isShared_166_ = v_isSharedCheck_226_;
goto v_resetjp_164_;
}
else
{
lean_dec(v_s_153_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_226_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_v_167_; lean_object* v_id_168_; lean_object* v_ringId_x3f_169_; lean_object* v_type_170_; lean_object* v_u_171_; lean_object* v_intModuleInst_172_; lean_object* v_leInst_x3f_173_; lean_object* v_ltInst_x3f_174_; lean_object* v_lawfulOrderLTInst_x3f_175_; lean_object* v_isPreorderInst_x3f_176_; lean_object* v_orderedAddInst_x3f_177_; lean_object* v_isLinearInst_x3f_178_; lean_object* v_noNatDivInst_x3f_179_; lean_object* v_ringInst_x3f_180_; lean_object* v_commRingInst_x3f_181_; lean_object* v_orderedRingInst_x3f_182_; lean_object* v_fieldInst_x3f_183_; lean_object* v_charInst_x3f_184_; lean_object* v_zero_185_; lean_object* v_ofNatZero_186_; lean_object* v_one_x3f_187_; lean_object* v_leFn_x3f_188_; lean_object* v_ltFn_x3f_189_; lean_object* v_addFn_190_; lean_object* v_zsmulFn_191_; lean_object* v_nsmulFn_192_; lean_object* v_zsmulFn_x3f_193_; lean_object* v_nsmulFn_x3f_194_; lean_object* v_homomulFn_x3f_195_; lean_object* v_subFn_196_; lean_object* v_negFn_197_; lean_object* v_vars_198_; lean_object* v_varMap_199_; lean_object* v_lowers_200_; lean_object* v_uppers_201_; lean_object* v_diseqs_202_; lean_object* v_assignment_203_; uint8_t v_caseSplits_204_; lean_object* v_conflict_x3f_205_; lean_object* v_diseqSplits_206_; lean_object* v_elimEqs_207_; lean_object* v_elimStack_208_; lean_object* v_occurs_209_; lean_object* v_ignored_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_v_167_ = lean_array_fget(v_structs_154_, v___y_150_);
v_id_168_ = lean_ctor_get(v_v_167_, 0);
v_ringId_x3f_169_ = lean_ctor_get(v_v_167_, 1);
v_type_170_ = lean_ctor_get(v_v_167_, 2);
v_u_171_ = lean_ctor_get(v_v_167_, 3);
v_intModuleInst_172_ = lean_ctor_get(v_v_167_, 4);
v_leInst_x3f_173_ = lean_ctor_get(v_v_167_, 5);
v_ltInst_x3f_174_ = lean_ctor_get(v_v_167_, 6);
v_lawfulOrderLTInst_x3f_175_ = lean_ctor_get(v_v_167_, 7);
v_isPreorderInst_x3f_176_ = lean_ctor_get(v_v_167_, 8);
v_orderedAddInst_x3f_177_ = lean_ctor_get(v_v_167_, 9);
v_isLinearInst_x3f_178_ = lean_ctor_get(v_v_167_, 10);
v_noNatDivInst_x3f_179_ = lean_ctor_get(v_v_167_, 11);
v_ringInst_x3f_180_ = lean_ctor_get(v_v_167_, 12);
v_commRingInst_x3f_181_ = lean_ctor_get(v_v_167_, 13);
v_orderedRingInst_x3f_182_ = lean_ctor_get(v_v_167_, 14);
v_fieldInst_x3f_183_ = lean_ctor_get(v_v_167_, 15);
v_charInst_x3f_184_ = lean_ctor_get(v_v_167_, 16);
v_zero_185_ = lean_ctor_get(v_v_167_, 17);
v_ofNatZero_186_ = lean_ctor_get(v_v_167_, 18);
v_one_x3f_187_ = lean_ctor_get(v_v_167_, 19);
v_leFn_x3f_188_ = lean_ctor_get(v_v_167_, 20);
v_ltFn_x3f_189_ = lean_ctor_get(v_v_167_, 21);
v_addFn_190_ = lean_ctor_get(v_v_167_, 22);
v_zsmulFn_191_ = lean_ctor_get(v_v_167_, 23);
v_nsmulFn_192_ = lean_ctor_get(v_v_167_, 24);
v_zsmulFn_x3f_193_ = lean_ctor_get(v_v_167_, 25);
v_nsmulFn_x3f_194_ = lean_ctor_get(v_v_167_, 26);
v_homomulFn_x3f_195_ = lean_ctor_get(v_v_167_, 27);
v_subFn_196_ = lean_ctor_get(v_v_167_, 28);
v_negFn_197_ = lean_ctor_get(v_v_167_, 29);
v_vars_198_ = lean_ctor_get(v_v_167_, 30);
v_varMap_199_ = lean_ctor_get(v_v_167_, 31);
v_lowers_200_ = lean_ctor_get(v_v_167_, 32);
v_uppers_201_ = lean_ctor_get(v_v_167_, 33);
v_diseqs_202_ = lean_ctor_get(v_v_167_, 34);
v_assignment_203_ = lean_ctor_get(v_v_167_, 35);
v_caseSplits_204_ = lean_ctor_get_uint8(v_v_167_, sizeof(void*)*42);
v_conflict_x3f_205_ = lean_ctor_get(v_v_167_, 36);
v_diseqSplits_206_ = lean_ctor_get(v_v_167_, 37);
v_elimEqs_207_ = lean_ctor_get(v_v_167_, 38);
v_elimStack_208_ = lean_ctor_get(v_v_167_, 39);
v_occurs_209_ = lean_ctor_get(v_v_167_, 40);
v_ignored_210_ = lean_ctor_get(v_v_167_, 41);
v_isSharedCheck_225_ = !lean_is_exclusive(v_v_167_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v_v_167_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_ignored_210_);
lean_inc(v_occurs_209_);
lean_inc(v_elimStack_208_);
lean_inc(v_elimEqs_207_);
lean_inc(v_diseqSplits_206_);
lean_inc(v_conflict_x3f_205_);
lean_inc(v_assignment_203_);
lean_inc(v_diseqs_202_);
lean_inc(v_uppers_201_);
lean_inc(v_lowers_200_);
lean_inc(v_varMap_199_);
lean_inc(v_vars_198_);
lean_inc(v_negFn_197_);
lean_inc(v_subFn_196_);
lean_inc(v_homomulFn_x3f_195_);
lean_inc(v_nsmulFn_x3f_194_);
lean_inc(v_zsmulFn_x3f_193_);
lean_inc(v_nsmulFn_192_);
lean_inc(v_zsmulFn_191_);
lean_inc(v_addFn_190_);
lean_inc(v_ltFn_x3f_189_);
lean_inc(v_leFn_x3f_188_);
lean_inc(v_one_x3f_187_);
lean_inc(v_ofNatZero_186_);
lean_inc(v_zero_185_);
lean_inc(v_charInst_x3f_184_);
lean_inc(v_fieldInst_x3f_183_);
lean_inc(v_orderedRingInst_x3f_182_);
lean_inc(v_commRingInst_x3f_181_);
lean_inc(v_ringInst_x3f_180_);
lean_inc(v_noNatDivInst_x3f_179_);
lean_inc(v_isLinearInst_x3f_178_);
lean_inc(v_orderedAddInst_x3f_177_);
lean_inc(v_isPreorderInst_x3f_176_);
lean_inc(v_lawfulOrderLTInst_x3f_175_);
lean_inc(v_ltInst_x3f_174_);
lean_inc(v_leInst_x3f_173_);
lean_inc(v_intModuleInst_172_);
lean_inc(v_u_171_);
lean_inc(v_type_170_);
lean_inc(v_ringId_x3f_169_);
lean_inc(v_id_168_);
lean_dec(v_v_167_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_xs_x27_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_214_ = lean_box(0);
v_xs_x27_215_ = lean_array_fset(v_structs_154_, v___y_150_, v___x_214_);
v___x_216_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0);
v___x_217_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(v_c_151_, v___x_216_, v_uppers_201_, v_v_152_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 33, v___x_217_);
v___x_219_ = v___x_212_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_id_168_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_ringId_x3f_169_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_type_170_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_u_171_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_intModuleInst_172_);
lean_ctor_set(v_reuseFailAlloc_224_, 5, v_leInst_x3f_173_);
lean_ctor_set(v_reuseFailAlloc_224_, 6, v_ltInst_x3f_174_);
lean_ctor_set(v_reuseFailAlloc_224_, 7, v_lawfulOrderLTInst_x3f_175_);
lean_ctor_set(v_reuseFailAlloc_224_, 8, v_isPreorderInst_x3f_176_);
lean_ctor_set(v_reuseFailAlloc_224_, 9, v_orderedAddInst_x3f_177_);
lean_ctor_set(v_reuseFailAlloc_224_, 10, v_isLinearInst_x3f_178_);
lean_ctor_set(v_reuseFailAlloc_224_, 11, v_noNatDivInst_x3f_179_);
lean_ctor_set(v_reuseFailAlloc_224_, 12, v_ringInst_x3f_180_);
lean_ctor_set(v_reuseFailAlloc_224_, 13, v_commRingInst_x3f_181_);
lean_ctor_set(v_reuseFailAlloc_224_, 14, v_orderedRingInst_x3f_182_);
lean_ctor_set(v_reuseFailAlloc_224_, 15, v_fieldInst_x3f_183_);
lean_ctor_set(v_reuseFailAlloc_224_, 16, v_charInst_x3f_184_);
lean_ctor_set(v_reuseFailAlloc_224_, 17, v_zero_185_);
lean_ctor_set(v_reuseFailAlloc_224_, 18, v_ofNatZero_186_);
lean_ctor_set(v_reuseFailAlloc_224_, 19, v_one_x3f_187_);
lean_ctor_set(v_reuseFailAlloc_224_, 20, v_leFn_x3f_188_);
lean_ctor_set(v_reuseFailAlloc_224_, 21, v_ltFn_x3f_189_);
lean_ctor_set(v_reuseFailAlloc_224_, 22, v_addFn_190_);
lean_ctor_set(v_reuseFailAlloc_224_, 23, v_zsmulFn_191_);
lean_ctor_set(v_reuseFailAlloc_224_, 24, v_nsmulFn_192_);
lean_ctor_set(v_reuseFailAlloc_224_, 25, v_zsmulFn_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_224_, 26, v_nsmulFn_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_224_, 27, v_homomulFn_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_224_, 28, v_subFn_196_);
lean_ctor_set(v_reuseFailAlloc_224_, 29, v_negFn_197_);
lean_ctor_set(v_reuseFailAlloc_224_, 30, v_vars_198_);
lean_ctor_set(v_reuseFailAlloc_224_, 31, v_varMap_199_);
lean_ctor_set(v_reuseFailAlloc_224_, 32, v_lowers_200_);
lean_ctor_set(v_reuseFailAlloc_224_, 33, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 34, v_diseqs_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 35, v_assignment_203_);
lean_ctor_set(v_reuseFailAlloc_224_, 36, v_conflict_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_224_, 37, v_diseqSplits_206_);
lean_ctor_set(v_reuseFailAlloc_224_, 38, v_elimEqs_207_);
lean_ctor_set(v_reuseFailAlloc_224_, 39, v_elimStack_208_);
lean_ctor_set(v_reuseFailAlloc_224_, 40, v_occurs_209_);
lean_ctor_set(v_reuseFailAlloc_224_, 41, v_ignored_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*42, v_caseSplits_204_);
v___x_219_ = v_reuseFailAlloc_224_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_array_fset(v_xs_x27_215_, v___y_150_, v___x_219_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_220_);
v___x_222_ = v___x_165_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_typeIdOf_155_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_exprToStructId_156_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_exprToStructIdEntries_157_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v_forbiddenNatModules_158_);
lean_ctor_set(v_reuseFailAlloc_223_, 5, v_natStructs_159_);
lean_ctor_set(v_reuseFailAlloc_223_, 6, v_natTypeIdOf_160_);
lean_ctor_set(v_reuseFailAlloc_223_, 7, v_exprToNatStructId_161_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object* v___y_235_, lean_object* v_c_236_, lean_object* v_v_237_, lean_object* v_s_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(v___y_235_, v_c_236_, v_v_237_, v_s_238_);
lean_dec(v_v_237_);
lean_dec(v___y_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object* v___y_240_, lean_object* v_c_241_, lean_object* v_v_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_structs_244_; lean_object* v_typeIdOf_245_; lean_object* v_exprToStructId_246_; lean_object* v_exprToStructIdEntries_247_; lean_object* v_forbiddenNatModules_248_; lean_object* v_natStructs_249_; lean_object* v_natTypeIdOf_250_; lean_object* v_exprToNatStructId_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_structs_244_ = lean_ctor_get(v_s_243_, 0);
v_typeIdOf_245_ = lean_ctor_get(v_s_243_, 1);
v_exprToStructId_246_ = lean_ctor_get(v_s_243_, 2);
v_exprToStructIdEntries_247_ = lean_ctor_get(v_s_243_, 3);
v_forbiddenNatModules_248_ = lean_ctor_get(v_s_243_, 4);
v_natStructs_249_ = lean_ctor_get(v_s_243_, 5);
v_natTypeIdOf_250_ = lean_ctor_get(v_s_243_, 6);
v_exprToNatStructId_251_ = lean_ctor_get(v_s_243_, 7);
v___x_252_ = lean_array_get_size(v_structs_244_);
v___x_253_ = lean_nat_dec_lt(v___y_240_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec_ref(v_c_241_);
return v_s_243_;
}
else
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_316_; 
lean_inc_ref(v_exprToNatStructId_251_);
lean_inc_ref(v_natTypeIdOf_250_);
lean_inc_ref(v_natStructs_249_);
lean_inc_ref(v_forbiddenNatModules_248_);
lean_inc_ref(v_exprToStructIdEntries_247_);
lean_inc_ref(v_exprToStructId_246_);
lean_inc_ref(v_typeIdOf_245_);
lean_inc_ref(v_structs_244_);
v_isSharedCheck_316_ = !lean_is_exclusive(v_s_243_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_317_ = lean_ctor_get(v_s_243_, 7);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_s_243_, 6);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_s_243_, 5);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_s_243_, 4);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_243_, 3);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_243_, 2);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_243_, 1);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_243_, 0);
lean_dec(v_unused_324_);
v___x_255_ = v_s_243_;
v_isShared_256_ = v_isSharedCheck_316_;
goto v_resetjp_254_;
}
else
{
lean_dec(v_s_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_316_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v_v_257_; lean_object* v_id_258_; lean_object* v_ringId_x3f_259_; lean_object* v_type_260_; lean_object* v_u_261_; lean_object* v_intModuleInst_262_; lean_object* v_leInst_x3f_263_; lean_object* v_ltInst_x3f_264_; lean_object* v_lawfulOrderLTInst_x3f_265_; lean_object* v_isPreorderInst_x3f_266_; lean_object* v_orderedAddInst_x3f_267_; lean_object* v_isLinearInst_x3f_268_; lean_object* v_noNatDivInst_x3f_269_; lean_object* v_ringInst_x3f_270_; lean_object* v_commRingInst_x3f_271_; lean_object* v_orderedRingInst_x3f_272_; lean_object* v_fieldInst_x3f_273_; lean_object* v_charInst_x3f_274_; lean_object* v_zero_275_; lean_object* v_ofNatZero_276_; lean_object* v_one_x3f_277_; lean_object* v_leFn_x3f_278_; lean_object* v_ltFn_x3f_279_; lean_object* v_addFn_280_; lean_object* v_zsmulFn_281_; lean_object* v_nsmulFn_282_; lean_object* v_zsmulFn_x3f_283_; lean_object* v_nsmulFn_x3f_284_; lean_object* v_homomulFn_x3f_285_; lean_object* v_subFn_286_; lean_object* v_negFn_287_; lean_object* v_vars_288_; lean_object* v_varMap_289_; lean_object* v_lowers_290_; lean_object* v_uppers_291_; lean_object* v_diseqs_292_; lean_object* v_assignment_293_; uint8_t v_caseSplits_294_; lean_object* v_conflict_x3f_295_; lean_object* v_diseqSplits_296_; lean_object* v_elimEqs_297_; lean_object* v_elimStack_298_; lean_object* v_occurs_299_; lean_object* v_ignored_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_315_; 
v_v_257_ = lean_array_fget(v_structs_244_, v___y_240_);
v_id_258_ = lean_ctor_get(v_v_257_, 0);
v_ringId_x3f_259_ = lean_ctor_get(v_v_257_, 1);
v_type_260_ = lean_ctor_get(v_v_257_, 2);
v_u_261_ = lean_ctor_get(v_v_257_, 3);
v_intModuleInst_262_ = lean_ctor_get(v_v_257_, 4);
v_leInst_x3f_263_ = lean_ctor_get(v_v_257_, 5);
v_ltInst_x3f_264_ = lean_ctor_get(v_v_257_, 6);
v_lawfulOrderLTInst_x3f_265_ = lean_ctor_get(v_v_257_, 7);
v_isPreorderInst_x3f_266_ = lean_ctor_get(v_v_257_, 8);
v_orderedAddInst_x3f_267_ = lean_ctor_get(v_v_257_, 9);
v_isLinearInst_x3f_268_ = lean_ctor_get(v_v_257_, 10);
v_noNatDivInst_x3f_269_ = lean_ctor_get(v_v_257_, 11);
v_ringInst_x3f_270_ = lean_ctor_get(v_v_257_, 12);
v_commRingInst_x3f_271_ = lean_ctor_get(v_v_257_, 13);
v_orderedRingInst_x3f_272_ = lean_ctor_get(v_v_257_, 14);
v_fieldInst_x3f_273_ = lean_ctor_get(v_v_257_, 15);
v_charInst_x3f_274_ = lean_ctor_get(v_v_257_, 16);
v_zero_275_ = lean_ctor_get(v_v_257_, 17);
v_ofNatZero_276_ = lean_ctor_get(v_v_257_, 18);
v_one_x3f_277_ = lean_ctor_get(v_v_257_, 19);
v_leFn_x3f_278_ = lean_ctor_get(v_v_257_, 20);
v_ltFn_x3f_279_ = lean_ctor_get(v_v_257_, 21);
v_addFn_280_ = lean_ctor_get(v_v_257_, 22);
v_zsmulFn_281_ = lean_ctor_get(v_v_257_, 23);
v_nsmulFn_282_ = lean_ctor_get(v_v_257_, 24);
v_zsmulFn_x3f_283_ = lean_ctor_get(v_v_257_, 25);
v_nsmulFn_x3f_284_ = lean_ctor_get(v_v_257_, 26);
v_homomulFn_x3f_285_ = lean_ctor_get(v_v_257_, 27);
v_subFn_286_ = lean_ctor_get(v_v_257_, 28);
v_negFn_287_ = lean_ctor_get(v_v_257_, 29);
v_vars_288_ = lean_ctor_get(v_v_257_, 30);
v_varMap_289_ = lean_ctor_get(v_v_257_, 31);
v_lowers_290_ = lean_ctor_get(v_v_257_, 32);
v_uppers_291_ = lean_ctor_get(v_v_257_, 33);
v_diseqs_292_ = lean_ctor_get(v_v_257_, 34);
v_assignment_293_ = lean_ctor_get(v_v_257_, 35);
v_caseSplits_294_ = lean_ctor_get_uint8(v_v_257_, sizeof(void*)*42);
v_conflict_x3f_295_ = lean_ctor_get(v_v_257_, 36);
v_diseqSplits_296_ = lean_ctor_get(v_v_257_, 37);
v_elimEqs_297_ = lean_ctor_get(v_v_257_, 38);
v_elimStack_298_ = lean_ctor_get(v_v_257_, 39);
v_occurs_299_ = lean_ctor_get(v_v_257_, 40);
v_ignored_300_ = lean_ctor_get(v_v_257_, 41);
v_isSharedCheck_315_ = !lean_is_exclusive(v_v_257_);
if (v_isSharedCheck_315_ == 0)
{
v___x_302_ = v_v_257_;
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_ignored_300_);
lean_inc(v_occurs_299_);
lean_inc(v_elimStack_298_);
lean_inc(v_elimEqs_297_);
lean_inc(v_diseqSplits_296_);
lean_inc(v_conflict_x3f_295_);
lean_inc(v_assignment_293_);
lean_inc(v_diseqs_292_);
lean_inc(v_uppers_291_);
lean_inc(v_lowers_290_);
lean_inc(v_varMap_289_);
lean_inc(v_vars_288_);
lean_inc(v_negFn_287_);
lean_inc(v_subFn_286_);
lean_inc(v_homomulFn_x3f_285_);
lean_inc(v_nsmulFn_x3f_284_);
lean_inc(v_zsmulFn_x3f_283_);
lean_inc(v_nsmulFn_282_);
lean_inc(v_zsmulFn_281_);
lean_inc(v_addFn_280_);
lean_inc(v_ltFn_x3f_279_);
lean_inc(v_leFn_x3f_278_);
lean_inc(v_one_x3f_277_);
lean_inc(v_ofNatZero_276_);
lean_inc(v_zero_275_);
lean_inc(v_charInst_x3f_274_);
lean_inc(v_fieldInst_x3f_273_);
lean_inc(v_orderedRingInst_x3f_272_);
lean_inc(v_commRingInst_x3f_271_);
lean_inc(v_ringInst_x3f_270_);
lean_inc(v_noNatDivInst_x3f_269_);
lean_inc(v_isLinearInst_x3f_268_);
lean_inc(v_orderedAddInst_x3f_267_);
lean_inc(v_isPreorderInst_x3f_266_);
lean_inc(v_lawfulOrderLTInst_x3f_265_);
lean_inc(v_ltInst_x3f_264_);
lean_inc(v_leInst_x3f_263_);
lean_inc(v_intModuleInst_262_);
lean_inc(v_u_261_);
lean_inc(v_type_260_);
lean_inc(v_ringId_x3f_259_);
lean_inc(v_id_258_);
lean_dec(v_v_257_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v_xs_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_304_ = lean_box(0);
v_xs_x27_305_ = lean_array_fset(v_structs_244_, v___y_240_, v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0);
v___x_307_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(v_c_241_, v___x_306_, v_lowers_290_, v_v_242_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 32, v___x_307_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_id_258_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_ringId_x3f_259_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_type_260_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_u_261_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_intModuleInst_262_);
lean_ctor_set(v_reuseFailAlloc_314_, 5, v_leInst_x3f_263_);
lean_ctor_set(v_reuseFailAlloc_314_, 6, v_ltInst_x3f_264_);
lean_ctor_set(v_reuseFailAlloc_314_, 7, v_lawfulOrderLTInst_x3f_265_);
lean_ctor_set(v_reuseFailAlloc_314_, 8, v_isPreorderInst_x3f_266_);
lean_ctor_set(v_reuseFailAlloc_314_, 9, v_orderedAddInst_x3f_267_);
lean_ctor_set(v_reuseFailAlloc_314_, 10, v_isLinearInst_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_314_, 11, v_noNatDivInst_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_314_, 12, v_ringInst_x3f_270_);
lean_ctor_set(v_reuseFailAlloc_314_, 13, v_commRingInst_x3f_271_);
lean_ctor_set(v_reuseFailAlloc_314_, 14, v_orderedRingInst_x3f_272_);
lean_ctor_set(v_reuseFailAlloc_314_, 15, v_fieldInst_x3f_273_);
lean_ctor_set(v_reuseFailAlloc_314_, 16, v_charInst_x3f_274_);
lean_ctor_set(v_reuseFailAlloc_314_, 17, v_zero_275_);
lean_ctor_set(v_reuseFailAlloc_314_, 18, v_ofNatZero_276_);
lean_ctor_set(v_reuseFailAlloc_314_, 19, v_one_x3f_277_);
lean_ctor_set(v_reuseFailAlloc_314_, 20, v_leFn_x3f_278_);
lean_ctor_set(v_reuseFailAlloc_314_, 21, v_ltFn_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_314_, 22, v_addFn_280_);
lean_ctor_set(v_reuseFailAlloc_314_, 23, v_zsmulFn_281_);
lean_ctor_set(v_reuseFailAlloc_314_, 24, v_nsmulFn_282_);
lean_ctor_set(v_reuseFailAlloc_314_, 25, v_zsmulFn_x3f_283_);
lean_ctor_set(v_reuseFailAlloc_314_, 26, v_nsmulFn_x3f_284_);
lean_ctor_set(v_reuseFailAlloc_314_, 27, v_homomulFn_x3f_285_);
lean_ctor_set(v_reuseFailAlloc_314_, 28, v_subFn_286_);
lean_ctor_set(v_reuseFailAlloc_314_, 29, v_negFn_287_);
lean_ctor_set(v_reuseFailAlloc_314_, 30, v_vars_288_);
lean_ctor_set(v_reuseFailAlloc_314_, 31, v_varMap_289_);
lean_ctor_set(v_reuseFailAlloc_314_, 32, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_314_, 33, v_uppers_291_);
lean_ctor_set(v_reuseFailAlloc_314_, 34, v_diseqs_292_);
lean_ctor_set(v_reuseFailAlloc_314_, 35, v_assignment_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 36, v_conflict_x3f_295_);
lean_ctor_set(v_reuseFailAlloc_314_, 37, v_diseqSplits_296_);
lean_ctor_set(v_reuseFailAlloc_314_, 38, v_elimEqs_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 39, v_elimStack_298_);
lean_ctor_set(v_reuseFailAlloc_314_, 40, v_occurs_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 41, v_ignored_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_314_, sizeof(void*)*42, v_caseSplits_294_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_array_fset(v_xs_x27_305_, v___y_240_, v___x_309_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_310_);
v___x_312_ = v___x_255_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_typeIdOf_245_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_exprToStructId_246_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_exprToStructIdEntries_247_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_forbiddenNatModules_248_);
lean_ctor_set(v_reuseFailAlloc_313_, 5, v_natStructs_249_);
lean_ctor_set(v_reuseFailAlloc_313_, 6, v_natTypeIdOf_250_);
lean_ctor_set(v_reuseFailAlloc_313_, 7, v_exprToNatStructId_251_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object* v___y_325_, lean_object* v_c_326_, lean_object* v_v_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(v___y_325_, v_c_326_, v_v_327_, v_s_328_);
lean_dec(v_v_327_);
lean_dec(v___y_325_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(lean_object* v_msgData_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v_env_337_; lean_object* v___x_338_; lean_object* v_mctx_339_; lean_object* v_lctx_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_336_ = lean_st_ref_get(v___y_334_);
v_env_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_env_337_);
lean_dec(v___x_336_);
v___x_338_ = lean_st_ref_get(v___y_332_);
v_mctx_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_mctx_339_);
lean_dec(v___x_338_);
v_lctx_340_ = lean_ctor_get(v___y_331_, 2);
v_options_341_ = lean_ctor_get(v___y_333_, 2);
lean_inc_ref(v_options_341_);
lean_inc_ref(v_lctx_340_);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v_env_337_);
lean_ctor_set(v___x_342_, 1, v_mctx_339_);
lean_ctor_set(v___x_342_, 2, v_lctx_340_);
lean_ctor_set(v___x_342_, 3, v_options_341_);
v___x_343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_msgData_330_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3___boxed(lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(v_msgData_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_352_; double v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_float_of_nat(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(lean_object* v_cls_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_410_; 
v_ref_364_ = lean_ctor_get(v___y_361_, 5);
v___x_365_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(v_msg_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_410_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v_traceState_371_; lean_object* v_env_372_; lean_object* v_nextMacroScope_373_; lean_object* v_ngen_374_; lean_object* v_auxDeclNGen_375_; lean_object* v_cache_376_; lean_object* v_messages_377_; lean_object* v_infoState_378_; lean_object* v_snapshotTasks_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_409_; 
v___x_370_ = lean_st_ref_take(v___y_362_);
v_traceState_371_ = lean_ctor_get(v___x_370_, 4);
v_env_372_ = lean_ctor_get(v___x_370_, 0);
v_nextMacroScope_373_ = lean_ctor_get(v___x_370_, 1);
v_ngen_374_ = lean_ctor_get(v___x_370_, 2);
v_auxDeclNGen_375_ = lean_ctor_get(v___x_370_, 3);
v_cache_376_ = lean_ctor_get(v___x_370_, 5);
v_messages_377_ = lean_ctor_get(v___x_370_, 6);
v_infoState_378_ = lean_ctor_get(v___x_370_, 7);
v_snapshotTasks_379_ = lean_ctor_get(v___x_370_, 8);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_409_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snapshotTasks_379_);
lean_inc(v_infoState_378_);
lean_inc(v_messages_377_);
lean_inc(v_cache_376_);
lean_inc(v_traceState_371_);
lean_inc(v_auxDeclNGen_375_);
lean_inc(v_ngen_374_);
lean_inc(v_nextMacroScope_373_);
lean_inc(v_env_372_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint64_t v_tid_383_; lean_object* v_traces_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_408_; 
v_tid_383_ = lean_ctor_get_uint64(v_traceState_371_, sizeof(void*)*1);
v_traces_384_ = lean_ctor_get(v_traceState_371_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_traceState_371_);
if (v_isSharedCheck_408_ == 0)
{
v___x_386_ = v_traceState_371_;
v_isShared_387_ = v_isSharedCheck_408_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_traces_384_);
lean_dec(v_traceState_371_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_408_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; double v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_388_ = lean_box(0);
v___x_389_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0);
v___x_390_ = 0;
v___x_391_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1));
v___x_392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_392_, 0, v_cls_357_);
lean_ctor_set(v___x_392_, 1, v___x_388_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3, v___x_389_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3 + 8, v___x_389_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*3 + 16, v___x_390_);
v___x_393_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2));
v___x_394_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v_a_366_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_inc(v_ref_364_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_ref_364_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_PersistentArray_push___redArg(v_traces_384_, v___x_395_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_396_);
v___x_398_ = v___x_386_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_396_);
lean_ctor_set_uint64(v_reuseFailAlloc_407_, sizeof(void*)*1, v_tid_383_);
v___x_398_ = v_reuseFailAlloc_407_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v___x_398_);
v___x_400_ = v___x_381_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_env_372_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_nextMacroScope_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_ngen_374_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_auxDeclNGen_375_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_messages_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_infoState_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v_snapshotTasks_379_);
v___x_400_ = v_reuseFailAlloc_406_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_st_ref_set(v___y_362_, v___x_400_);
v___x_402_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_402_);
v___x_404_ = v___x_368_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___boxed(lean_object* v_cls_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v_cls_411_, v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_ref_425_; lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
v_ref_425_ = lean_ctor_get(v___y_422_, 5);
v___x_426_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_435_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_ref_425_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_ref_425_);
lean_ctor_set(v___x_431_, 1, v_a_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 1);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(v_msg_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_470_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_470_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_ltFn_x3f_463_; 
v_ltFn_x3f_463_ = lean_ctor_get(v_a_459_, 21);
lean_inc(v_ltFn_x3f_463_);
lean_dec(v_a_459_);
if (lean_obj_tag(v_ltFn_x3f_463_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_466_; 
v_val_464_ = lean_ctor_get(v_ltFn_x3f_463_, 0);
lean_inc(v_val_464_);
lean_dec_ref(v_ltFn_x3f_463_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_val_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_val_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_ltFn_x3f_463_);
lean_del_object(v___x_461_);
v___x_468_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1);
v___x_469_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(v___x_468_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_469_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_458_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_458_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___boxed(lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
return v_res_491_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_519_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_519_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_leFn_x3f_512_; 
v_leFn_x3f_512_ = lean_ctor_get(v_a_508_, 20);
lean_inc(v_leFn_x3f_512_);
lean_dec(v_a_508_);
if (lean_obj_tag(v_leFn_x3f_512_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_515_; 
v_val_513_ = lean_ctor_get(v_leFn_x3f_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref(v_leFn_x3f_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v_val_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_val_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_leFn_x3f_512_);
lean_del_object(v___x_510_);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1);
v___x_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(v___x_517_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_518_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_507_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_507_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___boxed(lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec(v___y_529_);
lean_dec(v___y_528_);
return v_res_540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_to_int(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(lean_object* v_k_543_, lean_object* v_x_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0);
v___x_558_ = lean_int_dec_eq(v_k_543_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_580_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_580_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_580_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_580_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_vars_566_; lean_object* v_zsmulFn_567_; lean_object* v_size_568_; lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_vars_566_ = lean_ctor_get(v_a_562_, 30);
lean_inc_ref(v_vars_566_);
lean_dec(v_a_562_);
v_zsmulFn_567_ = lean_ctor_get(v_a_560_, 23);
lean_inc_ref(v_zsmulFn_567_);
lean_dec(v_a_560_);
v_size_568_ = lean_ctor_get(v_vars_566_, 2);
v___x_569_ = l_Lean_mkIntLit(v_k_543_);
v___x_576_ = l_Lean_instInhabitedExpr;
v___x_577_ = lean_nat_dec_lt(v_x_544_, v_size_568_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec_ref(v_vars_566_);
v___x_578_ = l_outOfBounds___redArg(v___x_576_);
v___y_571_ = v___x_578_;
goto v___jp_570_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentArray_get_x21___redArg(v___x_576_, v_vars_566_, v_x_544_);
v___y_571_ = v___x_579_;
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_mkAppB(v_zsmulFn_567_, v___x_569_, v___y_571_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_572_);
v___x_574_ = v___x_564_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_560_);
v_a_581_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_561_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_561_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_559_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_559_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_614_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_614_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_vars_602_; lean_object* v_size_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_vars_602_ = lean_ctor_get(v_a_598_, 30);
lean_inc_ref(v_vars_602_);
lean_dec(v_a_598_);
v_size_603_ = lean_ctor_get(v_vars_602_, 2);
v___x_604_ = l_Lean_instInhabitedExpr;
v___x_605_ = lean_nat_dec_lt(v_x_544_, v_size_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref(v_vars_602_);
v___x_606_ = l_outOfBounds___redArg(v___x_604_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_606_);
v___x_608_ = v___x_600_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_PersistentArray_get_x21___redArg(v___x_604_, v_vars_602_, v_x_544_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_610_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_597_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_597_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___boxed(lean_object* v_k_623_, lean_object* v_x_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(v_k_623_, v_x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec(v_x_624_);
lean_dec(v_k_623_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(lean_object* v_p_638_, lean_object* v_acc_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
if (lean_obj_tag(v_p_638_) == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_acc_639_);
return v___x_652_;
}
else
{
lean_object* v_k_653_; lean_object* v_v_654_; lean_object* v_p_655_; lean_object* v___x_656_; 
v_k_653_ = lean_ctor_get(v_p_638_, 0);
v_v_654_ = lean_ctor_get(v_p_638_, 1);
v_p_655_ = lean_ctor_get(v_p_638_, 2);
v___x_656_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v___x_656_);
v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(v_k_653_, v_v_654_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_addFn_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v_addFn_660_ = lean_ctor_get(v_a_657_, 22);
lean_inc_ref(v_addFn_660_);
lean_dec(v_a_657_);
v___x_661_ = l_Lean_mkAppB(v_addFn_660_, v_acc_639_, v_a_659_);
v_p_638_ = v_p_655_;
v_acc_639_ = v___x_661_;
goto _start;
}
else
{
lean_dec(v_a_657_);
lean_dec_ref(v_acc_639_);
return v___x_658_;
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_acc_639_);
v_a_663_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_656_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_p_671_, lean_object* v_acc_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(v_p_671_, v_acc_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v_p_671_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(lean_object* v_p_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
if (lean_obj_tag(v_p_686_) == 0)
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_zero_704_; lean_object* v___x_706_; 
v_zero_704_ = lean_ctor_get(v_a_700_, 17);
lean_inc_ref(v_zero_704_);
lean_dec(v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v_zero_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_zero_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_699_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_699_);
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
lean_object* v_k_717_; lean_object* v_v_718_; lean_object* v_p_719_; lean_object* v___x_720_; 
v_k_717_ = lean_ctor_get(v_p_686_, 0);
v_v_718_ = lean_ctor_get(v_p_686_, 1);
v_p_719_ = lean_ctor_get(v_p_686_, 2);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(v_k_717_, v_v_718_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(v_p_719_, v_a_721_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_722_;
}
else
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3___boxed(lean_object* v_p_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(v_p_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v_p_723_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(lean_object* v_p_737_, uint8_t v_strict_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
if (v_strict_738_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(v_p_737_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref(v___x_753_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_765_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_765_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_ofNatZero_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v_ofNatZero_760_ = lean_ctor_get(v_a_756_, 18);
lean_inc_ref(v_ofNatZero_760_);
lean_dec(v_a_756_);
v___x_761_ = l_Lean_mkAppB(v_a_752_, v_a_754_, v_ofNatZero_760_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_761_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_754_);
lean_dec(v_a_752_);
v_a_766_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_755_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_755_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_dec(v_a_752_);
return v___x_753_;
}
}
else
{
return v___x_751_;
}
}
else
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(v_p_737_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_788_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_ofNatZero_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_ofNatZero_783_ = lean_ctor_get(v_a_779_, 18);
lean_inc_ref(v_ofNatZero_783_);
lean_dec(v_a_779_);
v___x_784_ = l_Lean_mkAppB(v_a_775_, v_a_777_, v_ofNatZero_783_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_a_777_);
lean_dec(v_a_775_);
v_a_789_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_778_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_778_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_dec(v_a_775_);
return v___x_776_;
}
}
else
{
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1___boxed(lean_object* v_p_797_, lean_object* v_strict_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_strict_boxed_811_; lean_object* v_res_812_; 
v_strict_boxed_811_ = lean_unbox(v_strict_798_);
v_res_812_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(v_p_797_, v_strict_boxed_811_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v_p_797_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* v_c_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_p_826_; uint8_t v_strict_827_; lean_object* v___x_828_; 
v_p_826_ = lean_ctor_get(v_c_813_, 0);
v_strict_827_ = lean_ctor_get_uint8(v_c_813_, sizeof(void*)*2);
v___x_828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(v_p_826_, v_strict_827_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* v_c_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_c_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v_c_829_);
return v_res_842_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_nat_to_int(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* v_c_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v_cls_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; uint8_t v___x_1030_; 
v_cls_1027_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
v___x_1028_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v_cls_1027_, v_a_878_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1030_ == 0)
{
v___y_956_ = v_a_869_;
v___y_957_ = v_a_870_;
v___y_958_ = v_a_871_;
v___y_959_ = v_a_872_;
v___y_960_ = v_a_873_;
v___y_961_ = v_a_874_;
v___y_962_ = v_a_875_;
v___y_963_ = v_a_876_;
v___y_964_ = v_a_877_;
v___y_965_ = v_a_878_;
v___y_966_ = v_a_879_;
goto v___jp_955_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_c_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_Lean_MessageData_ofExpr(v_a_1032_);
v___x_1034_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v_cls_1027_, v___x_1033_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref(v___x_1034_);
v___y_956_ = v_a_869_;
v___y_957_ = v_a_870_;
v___y_958_ = v_a_871_;
v___y_959_ = v_a_872_;
v___y_960_ = v_a_873_;
v___y_961_ = v_a_874_;
v___y_962_ = v_a_875_;
v___y_963_ = v_a_876_;
v___y_964_ = v_a_877_;
v___y_965_ = v_a_878_;
v___y_966_ = v_a_879_;
goto v___jp_955_;
}
else
{
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_c_868_);
return v___x_1034_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_c_868_);
v_a_1035_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1031_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1031_);
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
v___jp_881_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_c_868_);
v___x_894_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_893_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
v___jp_895_:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_868_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_913_ = 0;
v___x_914_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
v___x_915_ = l_Lean_instBEqLBool_beq(v___x_914_, v___x_913_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v___y_898_);
lean_dec(v___y_897_);
lean_dec(v___y_896_);
v___x_916_ = lean_box(0);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_916_);
v___x_918_ = v___x_911_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
lean_object* v___x_920_; 
lean_del_object(v___x_911_);
v___x_920_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
return v___x_920_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v___y_898_);
lean_dec(v___y_897_);
lean_dec(v___y_896_);
v_a_922_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_908_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_908_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
v___jp_930_:
{
lean_object* v___x_946_; 
lean_inc(v___y_935_);
v___x_946_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; uint8_t v___x_948_; 
lean_dec_ref(v___x_946_);
v___x_947_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0, &l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
v___x_948_ = lean_int_dec_lt(v___y_932_, v___x_947_);
lean_dec(v___y_932_);
if (v___x_948_ == 0)
{
lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_inc_ref(v_c_868_);
lean_inc(v___y_935_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_949_, 0, v___y_935_);
lean_closure_set(v___f_949_, 1, v_c_868_);
lean_closure_set(v___f_949_, 2, v___y_931_);
v___x_950_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_951_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_950_, v___f_949_, v___y_936_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_dec_ref(v___x_951_);
v___y_896_ = v___y_933_;
v___y_897_ = v___y_935_;
v___y_898_ = v___y_936_;
v___y_899_ = v___y_937_;
v___y_900_ = v___y_938_;
v___y_901_ = v___y_939_;
v___y_902_ = v___y_940_;
v___y_903_ = v___y_941_;
v___y_904_ = v___y_942_;
v___y_905_ = v___y_943_;
v___y_906_ = v___y_944_;
v___y_907_ = v___y_945_;
goto v___jp_895_;
}
else
{
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_933_);
lean_dec_ref(v_c_868_);
return v___x_951_;
}
}
else
{
lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_inc_ref(v_c_868_);
lean_inc(v___y_935_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(v___f_952_, 0, v___y_935_);
lean_closure_set(v___f_952_, 1, v_c_868_);
lean_closure_set(v___f_952_, 2, v___y_931_);
v___x_953_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_954_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_953_, v___f_952_, v___y_936_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_dec_ref(v___x_954_);
v___y_896_ = v___y_933_;
v___y_897_ = v___y_935_;
v___y_898_ = v___y_936_;
v___y_899_ = v___y_937_;
v___y_900_ = v___y_938_;
v___y_901_ = v___y_939_;
v___y_902_ = v___y_940_;
v___y_903_ = v___y_941_;
v___y_904_ = v___y_942_;
v___y_905_ = v___y_943_;
v___y_906_ = v___y_944_;
v___y_907_ = v___y_945_;
goto v___jp_895_;
}
else
{
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_933_);
lean_dec_ref(v_c_868_);
return v___x_954_;
}
}
}
else
{
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v_c_868_);
return v___x_946_;
}
}
v___jp_955_:
{
lean_object* v_p_967_; 
v_p_967_ = lean_ctor_get(v_c_868_, 0);
if (lean_obj_tag(v_p_967_) == 0)
{
uint8_t v_strict_968_; 
v_strict_968_ = lean_ctor_get_uint8(v_c_868_, sizeof(void*)*2);
if (v_strict_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_992_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
v___x_970_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v___x_969_, v___y_965_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_992_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_992_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_992_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
uint8_t v___x_975_; 
v___x_975_ = lean_unbox(v_a_971_);
lean_dec(v_a_971_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
v___x_976_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_976_);
v___x_978_ = v___x_973_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v___x_980_; 
lean_del_object(v___x_973_);
v___x_980_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_c_868_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = l_Lean_MessageData_ofExpr(v_a_981_);
v___x_983_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v___x_969_, v___x_982_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v___x_983_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
v_a_984_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_980_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_980_);
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
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_a_995_; uint8_t v___x_996_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
v___x_994_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v___x_993_, v___y_965_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = lean_unbox(v_a_995_);
lean_dec(v_a_995_);
if (v___x_996_ == 0)
{
v___y_882_ = v___y_956_;
v___y_883_ = v___y_957_;
v___y_884_ = v___y_958_;
v___y_885_ = v___y_959_;
v___y_886_ = v___y_960_;
v___y_887_ = v___y_961_;
v___y_888_ = v___y_962_;
v___y_889_ = v___y_963_;
v___y_890_ = v___y_964_;
v___y_891_ = v___y_965_;
v___y_892_ = v___y_966_;
goto v___jp_881_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_c_868_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_MessageData_ofExpr(v_a_998_);
v___x_1000_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v___x_993_, v___x_999_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref(v___x_1000_);
v___y_882_ = v___y_956_;
v___y_883_ = v___y_957_;
v___y_884_ = v___y_958_;
v___y_885_ = v___y_959_;
v___y_886_ = v___y_960_;
v___y_887_ = v___y_961_;
v___y_888_ = v___y_962_;
v___y_889_ = v___y_963_;
v___y_890_ = v___y_964_;
v___y_891_ = v___y_965_;
v___y_892_ = v___y_966_;
goto v___jp_881_;
}
else
{
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
return v___x_1000_;
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
v_a_1001_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_997_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_997_);
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
}
}
else
{
lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; uint8_t v___x_1014_; 
v_k_1009_ = lean_ctor_get(v_p_967_, 0);
v_v_1010_ = lean_ctor_get(v_p_967_, 1);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9));
v___x_1012_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(v___x_1011_, v___y_965_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_unbox(v_a_1013_);
lean_dec(v_a_1013_);
if (v___x_1014_ == 0)
{
lean_inc_ref(v_p_967_);
lean_inc(v_k_1009_);
lean_inc_n(v_v_1010_, 2);
v___y_931_ = v_v_1010_;
v___y_932_ = v_k_1009_;
v___y_933_ = v_v_1010_;
v___y_934_ = v_p_967_;
v___y_935_ = v___y_956_;
v___y_936_ = v___y_957_;
v___y_937_ = v___y_958_;
v___y_938_ = v___y_959_;
v___y_939_ = v___y_960_;
v___y_940_ = v___y_961_;
v___y_941_ = v___y_962_;
v___y_942_ = v___y_963_;
v___y_943_ = v___y_964_;
v___y_944_ = v___y_965_;
v___y_945_ = v___y_966_;
goto v___jp_930_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(v_c_868_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofExpr(v_a_1016_);
v___x_1018_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v___x_1011_, v___x_1017_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec_ref(v___x_1018_);
lean_inc_ref(v_p_967_);
lean_inc(v_k_1009_);
lean_inc_n(v_v_1010_, 2);
v___y_931_ = v_v_1010_;
v___y_932_ = v_k_1009_;
v___y_933_ = v_v_1010_;
v___y_934_ = v_p_967_;
v___y_935_ = v___y_956_;
v___y_936_ = v___y_957_;
v___y_937_ = v___y_958_;
v___y_938_ = v___y_959_;
v___y_939_ = v___y_960_;
v___y_940_ = v___y_961_;
v___y_941_ = v___y_962_;
v___y_942_ = v___y_963_;
v___y_943_ = v___y_964_;
v___y_944_ = v___y_965_;
v___y_945_ = v___y_966_;
goto v___jp_930_;
}
else
{
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
return v___x_1018_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_c_868_);
v_a_1019_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1015_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* v_c_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_c_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object* v_cls_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(v_cls_1057_, v_msg_1058_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object* v_cls_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(v_cls_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5(lean_object* v_c_1087_, lean_object* v_inst_1088_, lean_object* v_x_1089_, size_t v_x_1090_, size_t v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(v_c_1087_, v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___boxed(lean_object* v_c_1093_, lean_object* v_inst_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
size_t v_x_69645__boxed_1098_; size_t v_x_69646__boxed_1099_; lean_object* v_res_1100_; 
v_x_69645__boxed_1098_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_x_69646__boxed_1099_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1100_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5(v_c_1093_, v_inst_1094_, v_x_1095_, v_x_69645__boxed_1098_, v_x_69646__boxed_1099_);
lean_dec_ref(v_inst_1094_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b1_1101_, lean_object* v_msg_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(v_msg_1102_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6(v_00_u03b1_1116_, v_msg_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* v_a_1131_, lean_object* v_e_1132_, lean_object* v_s_1133_){
_start:
{
lean_object* v_structs_1134_; lean_object* v_typeIdOf_1135_; lean_object* v_exprToStructId_1136_; lean_object* v_exprToStructIdEntries_1137_; lean_object* v_forbiddenNatModules_1138_; lean_object* v_natStructs_1139_; lean_object* v_natTypeIdOf_1140_; lean_object* v_exprToNatStructId_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v_structs_1134_ = lean_ctor_get(v_s_1133_, 0);
v_typeIdOf_1135_ = lean_ctor_get(v_s_1133_, 1);
v_exprToStructId_1136_ = lean_ctor_get(v_s_1133_, 2);
v_exprToStructIdEntries_1137_ = lean_ctor_get(v_s_1133_, 3);
v_forbiddenNatModules_1138_ = lean_ctor_get(v_s_1133_, 4);
v_natStructs_1139_ = lean_ctor_get(v_s_1133_, 5);
v_natTypeIdOf_1140_ = lean_ctor_get(v_s_1133_, 6);
v_exprToNatStructId_1141_ = lean_ctor_get(v_s_1133_, 7);
v___x_1142_ = lean_array_get_size(v_structs_1134_);
v___x_1143_ = lean_nat_dec_lt(v_a_1131_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_dec_ref(v_e_1132_);
return v_s_1133_;
}
else
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1205_; 
lean_inc_ref(v_exprToNatStructId_1141_);
lean_inc_ref(v_natTypeIdOf_1140_);
lean_inc_ref(v_natStructs_1139_);
lean_inc_ref(v_forbiddenNatModules_1138_);
lean_inc_ref(v_exprToStructIdEntries_1137_);
lean_inc_ref(v_exprToStructId_1136_);
lean_inc_ref(v_typeIdOf_1135_);
lean_inc_ref(v_structs_1134_);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_s_1133_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1206_ = lean_ctor_get(v_s_1133_, 7);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_s_1133_, 6);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_s_1133_, 5);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_s_1133_, 4);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_s_1133_, 3);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_s_1133_, 2);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_s_1133_, 1);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_s_1133_, 0);
lean_dec(v_unused_1213_);
v___x_1145_ = v_s_1133_;
v_isShared_1146_ = v_isSharedCheck_1205_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v_s_1133_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1205_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_v_1147_; lean_object* v_id_1148_; lean_object* v_ringId_x3f_1149_; lean_object* v_type_1150_; lean_object* v_u_1151_; lean_object* v_intModuleInst_1152_; lean_object* v_leInst_x3f_1153_; lean_object* v_ltInst_x3f_1154_; lean_object* v_lawfulOrderLTInst_x3f_1155_; lean_object* v_isPreorderInst_x3f_1156_; lean_object* v_orderedAddInst_x3f_1157_; lean_object* v_isLinearInst_x3f_1158_; lean_object* v_noNatDivInst_x3f_1159_; lean_object* v_ringInst_x3f_1160_; lean_object* v_commRingInst_x3f_1161_; lean_object* v_orderedRingInst_x3f_1162_; lean_object* v_fieldInst_x3f_1163_; lean_object* v_charInst_x3f_1164_; lean_object* v_zero_1165_; lean_object* v_ofNatZero_1166_; lean_object* v_one_x3f_1167_; lean_object* v_leFn_x3f_1168_; lean_object* v_ltFn_x3f_1169_; lean_object* v_addFn_1170_; lean_object* v_zsmulFn_1171_; lean_object* v_nsmulFn_1172_; lean_object* v_zsmulFn_x3f_1173_; lean_object* v_nsmulFn_x3f_1174_; lean_object* v_homomulFn_x3f_1175_; lean_object* v_subFn_1176_; lean_object* v_negFn_1177_; lean_object* v_vars_1178_; lean_object* v_varMap_1179_; lean_object* v_lowers_1180_; lean_object* v_uppers_1181_; lean_object* v_diseqs_1182_; lean_object* v_assignment_1183_; uint8_t v_caseSplits_1184_; lean_object* v_conflict_x3f_1185_; lean_object* v_diseqSplits_1186_; lean_object* v_elimEqs_1187_; lean_object* v_elimStack_1188_; lean_object* v_occurs_1189_; lean_object* v_ignored_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1204_; 
v_v_1147_ = lean_array_fget(v_structs_1134_, v_a_1131_);
v_id_1148_ = lean_ctor_get(v_v_1147_, 0);
v_ringId_x3f_1149_ = lean_ctor_get(v_v_1147_, 1);
v_type_1150_ = lean_ctor_get(v_v_1147_, 2);
v_u_1151_ = lean_ctor_get(v_v_1147_, 3);
v_intModuleInst_1152_ = lean_ctor_get(v_v_1147_, 4);
v_leInst_x3f_1153_ = lean_ctor_get(v_v_1147_, 5);
v_ltInst_x3f_1154_ = lean_ctor_get(v_v_1147_, 6);
v_lawfulOrderLTInst_x3f_1155_ = lean_ctor_get(v_v_1147_, 7);
v_isPreorderInst_x3f_1156_ = lean_ctor_get(v_v_1147_, 8);
v_orderedAddInst_x3f_1157_ = lean_ctor_get(v_v_1147_, 9);
v_isLinearInst_x3f_1158_ = lean_ctor_get(v_v_1147_, 10);
v_noNatDivInst_x3f_1159_ = lean_ctor_get(v_v_1147_, 11);
v_ringInst_x3f_1160_ = lean_ctor_get(v_v_1147_, 12);
v_commRingInst_x3f_1161_ = lean_ctor_get(v_v_1147_, 13);
v_orderedRingInst_x3f_1162_ = lean_ctor_get(v_v_1147_, 14);
v_fieldInst_x3f_1163_ = lean_ctor_get(v_v_1147_, 15);
v_charInst_x3f_1164_ = lean_ctor_get(v_v_1147_, 16);
v_zero_1165_ = lean_ctor_get(v_v_1147_, 17);
v_ofNatZero_1166_ = lean_ctor_get(v_v_1147_, 18);
v_one_x3f_1167_ = lean_ctor_get(v_v_1147_, 19);
v_leFn_x3f_1168_ = lean_ctor_get(v_v_1147_, 20);
v_ltFn_x3f_1169_ = lean_ctor_get(v_v_1147_, 21);
v_addFn_1170_ = lean_ctor_get(v_v_1147_, 22);
v_zsmulFn_1171_ = lean_ctor_get(v_v_1147_, 23);
v_nsmulFn_1172_ = lean_ctor_get(v_v_1147_, 24);
v_zsmulFn_x3f_1173_ = lean_ctor_get(v_v_1147_, 25);
v_nsmulFn_x3f_1174_ = lean_ctor_get(v_v_1147_, 26);
v_homomulFn_x3f_1175_ = lean_ctor_get(v_v_1147_, 27);
v_subFn_1176_ = lean_ctor_get(v_v_1147_, 28);
v_negFn_1177_ = lean_ctor_get(v_v_1147_, 29);
v_vars_1178_ = lean_ctor_get(v_v_1147_, 30);
v_varMap_1179_ = lean_ctor_get(v_v_1147_, 31);
v_lowers_1180_ = lean_ctor_get(v_v_1147_, 32);
v_uppers_1181_ = lean_ctor_get(v_v_1147_, 33);
v_diseqs_1182_ = lean_ctor_get(v_v_1147_, 34);
v_assignment_1183_ = lean_ctor_get(v_v_1147_, 35);
v_caseSplits_1184_ = lean_ctor_get_uint8(v_v_1147_, sizeof(void*)*42);
v_conflict_x3f_1185_ = lean_ctor_get(v_v_1147_, 36);
v_diseqSplits_1186_ = lean_ctor_get(v_v_1147_, 37);
v_elimEqs_1187_ = lean_ctor_get(v_v_1147_, 38);
v_elimStack_1188_ = lean_ctor_get(v_v_1147_, 39);
v_occurs_1189_ = lean_ctor_get(v_v_1147_, 40);
v_ignored_1190_ = lean_ctor_get(v_v_1147_, 41);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_v_1147_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1192_ = v_v_1147_;
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_ignored_1190_);
lean_inc(v_occurs_1189_);
lean_inc(v_elimStack_1188_);
lean_inc(v_elimEqs_1187_);
lean_inc(v_diseqSplits_1186_);
lean_inc(v_conflict_x3f_1185_);
lean_inc(v_assignment_1183_);
lean_inc(v_diseqs_1182_);
lean_inc(v_uppers_1181_);
lean_inc(v_lowers_1180_);
lean_inc(v_varMap_1179_);
lean_inc(v_vars_1178_);
lean_inc(v_negFn_1177_);
lean_inc(v_subFn_1176_);
lean_inc(v_homomulFn_x3f_1175_);
lean_inc(v_nsmulFn_x3f_1174_);
lean_inc(v_zsmulFn_x3f_1173_);
lean_inc(v_nsmulFn_1172_);
lean_inc(v_zsmulFn_1171_);
lean_inc(v_addFn_1170_);
lean_inc(v_ltFn_x3f_1169_);
lean_inc(v_leFn_x3f_1168_);
lean_inc(v_one_x3f_1167_);
lean_inc(v_ofNatZero_1166_);
lean_inc(v_zero_1165_);
lean_inc(v_charInst_x3f_1164_);
lean_inc(v_fieldInst_x3f_1163_);
lean_inc(v_orderedRingInst_x3f_1162_);
lean_inc(v_commRingInst_x3f_1161_);
lean_inc(v_ringInst_x3f_1160_);
lean_inc(v_noNatDivInst_x3f_1159_);
lean_inc(v_isLinearInst_x3f_1158_);
lean_inc(v_orderedAddInst_x3f_1157_);
lean_inc(v_isPreorderInst_x3f_1156_);
lean_inc(v_lawfulOrderLTInst_x3f_1155_);
lean_inc(v_ltInst_x3f_1154_);
lean_inc(v_leInst_x3f_1153_);
lean_inc(v_intModuleInst_1152_);
lean_inc(v_u_1151_);
lean_inc(v_type_1150_);
lean_inc(v_ringId_x3f_1149_);
lean_inc(v_id_1148_);
lean_dec(v_v_1147_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v_xs_x27_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1194_ = lean_box(0);
v_xs_x27_1195_ = lean_array_fset(v_structs_1134_, v_a_1131_, v___x_1194_);
v___x_1196_ = l_Lean_PersistentArray_push___redArg(v_ignored_1190_, v_e_1132_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 41, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_id_1148_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_ringId_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_type_1150_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_u_1151_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_intModuleInst_1152_);
lean_ctor_set(v_reuseFailAlloc_1203_, 5, v_leInst_x3f_1153_);
lean_ctor_set(v_reuseFailAlloc_1203_, 6, v_ltInst_x3f_1154_);
lean_ctor_set(v_reuseFailAlloc_1203_, 7, v_lawfulOrderLTInst_x3f_1155_);
lean_ctor_set(v_reuseFailAlloc_1203_, 8, v_isPreorderInst_x3f_1156_);
lean_ctor_set(v_reuseFailAlloc_1203_, 9, v_orderedAddInst_x3f_1157_);
lean_ctor_set(v_reuseFailAlloc_1203_, 10, v_isLinearInst_x3f_1158_);
lean_ctor_set(v_reuseFailAlloc_1203_, 11, v_noNatDivInst_x3f_1159_);
lean_ctor_set(v_reuseFailAlloc_1203_, 12, v_ringInst_x3f_1160_);
lean_ctor_set(v_reuseFailAlloc_1203_, 13, v_commRingInst_x3f_1161_);
lean_ctor_set(v_reuseFailAlloc_1203_, 14, v_orderedRingInst_x3f_1162_);
lean_ctor_set(v_reuseFailAlloc_1203_, 15, v_fieldInst_x3f_1163_);
lean_ctor_set(v_reuseFailAlloc_1203_, 16, v_charInst_x3f_1164_);
lean_ctor_set(v_reuseFailAlloc_1203_, 17, v_zero_1165_);
lean_ctor_set(v_reuseFailAlloc_1203_, 18, v_ofNatZero_1166_);
lean_ctor_set(v_reuseFailAlloc_1203_, 19, v_one_x3f_1167_);
lean_ctor_set(v_reuseFailAlloc_1203_, 20, v_leFn_x3f_1168_);
lean_ctor_set(v_reuseFailAlloc_1203_, 21, v_ltFn_x3f_1169_);
lean_ctor_set(v_reuseFailAlloc_1203_, 22, v_addFn_1170_);
lean_ctor_set(v_reuseFailAlloc_1203_, 23, v_zsmulFn_1171_);
lean_ctor_set(v_reuseFailAlloc_1203_, 24, v_nsmulFn_1172_);
lean_ctor_set(v_reuseFailAlloc_1203_, 25, v_zsmulFn_x3f_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 26, v_nsmulFn_x3f_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 27, v_homomulFn_x3f_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 28, v_subFn_1176_);
lean_ctor_set(v_reuseFailAlloc_1203_, 29, v_negFn_1177_);
lean_ctor_set(v_reuseFailAlloc_1203_, 30, v_vars_1178_);
lean_ctor_set(v_reuseFailAlloc_1203_, 31, v_varMap_1179_);
lean_ctor_set(v_reuseFailAlloc_1203_, 32, v_lowers_1180_);
lean_ctor_set(v_reuseFailAlloc_1203_, 33, v_uppers_1181_);
lean_ctor_set(v_reuseFailAlloc_1203_, 34, v_diseqs_1182_);
lean_ctor_set(v_reuseFailAlloc_1203_, 35, v_assignment_1183_);
lean_ctor_set(v_reuseFailAlloc_1203_, 36, v_conflict_x3f_1185_);
lean_ctor_set(v_reuseFailAlloc_1203_, 37, v_diseqSplits_1186_);
lean_ctor_set(v_reuseFailAlloc_1203_, 38, v_elimEqs_1187_);
lean_ctor_set(v_reuseFailAlloc_1203_, 39, v_elimStack_1188_);
lean_ctor_set(v_reuseFailAlloc_1203_, 40, v_occurs_1189_);
lean_ctor_set(v_reuseFailAlloc_1203_, 41, v___x_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*42, v_caseSplits_1184_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_array_fset(v_xs_x27_1195_, v_a_1131_, v___x_1198_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1199_);
v___x_1201_ = v___x_1145_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_typeIdOf_1135_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_exprToStructId_1136_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_exprToStructIdEntries_1137_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_forbiddenNatModules_1138_);
lean_ctor_set(v_reuseFailAlloc_1202_, 5, v_natStructs_1139_);
lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_natTypeIdOf_1140_);
lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_exprToNatStructId_1141_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* v_a_1214_, lean_object* v_e_1215_, lean_object* v_s_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(v_a_1214_, v_e_1215_, v_s_1216_);
lean_dec(v_a_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* v_e_1218_, lean_object* v_lhs_1219_, lean_object* v_rhs_1220_, uint8_t v_strict_1221_, uint8_t v_eqTrue_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1235_ = 0;
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_box(v___x_1235_);
v___x_1238_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1238_, 0, v_lhs_1219_);
lean_closure_set(v___x_1238_, 1, v___x_1237_);
lean_closure_set(v___x_1238_, 2, v___x_1236_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
v___x_1239_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1238_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1394_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1394_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1394_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_a_1240_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_del_object(v___x_1242_);
v_val_1244_ = lean_ctor_get(v_a_1240_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v_a_1240_);
v___x_1245_ = lean_box(v___x_1235_);
v___x_1246_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_1246_, 0, v_rhs_1220_);
lean_closure_set(v___x_1246_, 1, v___x_1245_);
lean_closure_set(v___x_1246_, 2, v___x_1236_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
v___x_1247_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_1246_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1381_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1381_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1381_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_a_1248_) == 1)
{
lean_object* v_val_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1250_);
v_val_1252_ = lean_ctor_get(v_a_1248_, 0);
lean_inc(v_val_1252_);
lean_dec_ref(v_a_1248_);
v___x_1253_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1218_, v_a_1224_);
if (lean_obj_tag(v___x_1253_) == 0)
{
if (v_eqTrue_1222_ == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; uint8_t v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = lean_unbox(v_a_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_a_1256_);
lean_dec(v_a_1254_);
lean_dec(v_val_1252_);
lean_dec(v_val_1244_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1258_, 0, v_a_1223_);
lean_closure_set(v___f_1258_, 1, v_e_1218_);
v___x_1259_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1260_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1259_, v___f_1258_, v_a_1224_);
lean_dec(v_a_1224_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___y_1264_; 
lean_inc(v_val_1244_);
lean_inc(v_val_1252_);
v___x_1261_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_val_1252_);
lean_ctor_set(v___x_1261_, 1, v_val_1244_);
v___x_1262_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1261_);
if (v_strict_1221_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_unbox(v_a_1256_);
lean_dec(v_a_1256_);
v___y_1264_ = v___x_1311_;
goto v___jp_1263_;
}
else
{
lean_dec(v_a_1256_);
v___y_1264_ = v_eqTrue_1222_;
goto v___jp_1263_;
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1265_, 0, v_e_1218_);
lean_ctor_set(v___x_1265_, 1, v_val_1244_);
lean_ctor_set(v___x_1265_, 2, v_val_1252_);
v___x_1266_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1262_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*2, v___y_1264_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
v___x_1267_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1266_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_p_1269_; lean_object* v___x_1270_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref(v___x_1267_);
v_p_1269_ = lean_ctor_get(v_a_1268_, 0);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc(v_a_1254_);
lean_inc_ref(v_p_1269_);
v___x_1270_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1269_, v_a_1254_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc(v_a_1223_);
v___x_1272_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1271_, v___x_1235_, v_a_1254_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1286_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1286_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1286_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
if (lean_obj_tag(v_a_1273_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_del_object(v___x_1275_);
v_val_1277_ = lean_ctor_get(v_a_1273_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v_a_1273_);
lean_inc(v_val_1277_);
v___x_1278_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1277_);
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1268_);
lean_ctor_set(v___x_1279_, 1, v_val_1277_);
v___x_1280_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*2, v___y_1264_);
v___x_1281_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1280_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_dec(v_a_1273_);
lean_dec(v_a_1268_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v___x_1282_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1282_);
v___x_1284_ = v___x_1275_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
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
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1268_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1287_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1272_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1272_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1268_);
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1295_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1270_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1270_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
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
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1303_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1267_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1267_);
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
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1254_);
lean_dec(v_val_1252_);
lean_dec(v_val_1244_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_e_1218_);
v_a_1312_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1255_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1255_);
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
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1320_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1253_);
lean_inc(v_val_1252_);
lean_inc(v_val_1244_);
v___x_1321_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_val_1244_);
lean_ctor_set(v___x_1321_, 1, v_val_1252_);
v___x_1322_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1323_, 0, v_e_1218_);
lean_ctor_set(v___x_1323_, 1, v_val_1244_);
lean_ctor_set(v___x_1323_, 2, v_val_1252_);
v___x_1324_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*2, v_strict_1221_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
v___x_1325_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v___x_1324_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_p_1327_; lean_object* v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v_p_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc(v_a_1320_);
lean_inc_ref(v_p_1327_);
v___x_1328_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_1327_, v_a_1320_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc(v_a_1223_);
v___x_1330_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1329_, v___x_1235_, v_a_1320_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1344_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
if (lean_obj_tag(v_a_1331_) == 1)
{
lean_object* v_val_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_del_object(v___x_1333_);
v_val_1335_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_val_1335_);
lean_dec_ref(v_a_1331_);
lean_inc(v_val_1335_);
v___x_1336_ = l_Lean_Grind_Linarith_Expr_norm(v_val_1335_);
v___x_1337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1326_);
lean_ctor_set(v___x_1337_, 1, v_val_1335_);
v___x_1338_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*2, v_strict_1221_);
v___x_1339_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1338_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec(v_a_1331_);
lean_dec(v_a_1326_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v___x_1340_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1340_);
v___x_1342_ = v___x_1333_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
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
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_a_1326_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1345_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1330_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1330_);
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
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_a_1326_);
lean_dec(v_a_1320_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1353_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1328_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1328_);
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
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1320_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
v_a_1361_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1325_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1325_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_val_1252_);
lean_dec(v_val_1244_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_e_1218_);
v_a_1369_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1253_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1253_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec(v_a_1248_);
lean_dec(v_val_1244_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_e_1218_);
v___x_1377_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1377_);
v___x_1379_ = v___x_1250_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_val_1244_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_e_1218_);
v_a_1382_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1247_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1247_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_a_1240_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_rhs_1220_);
lean_dec_ref(v_e_1218_);
v___x_1390_ = lean_box(0);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1390_);
v___x_1392_ = v___x_1242_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_rhs_1220_);
lean_dec_ref(v_e_1218_);
v_a_1395_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1239_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1239_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args){
lean_object* v_e_1403_ = _args[0];
lean_object* v_lhs_1404_ = _args[1];
lean_object* v_rhs_1405_ = _args[2];
lean_object* v_strict_1406_ = _args[3];
lean_object* v_eqTrue_1407_ = _args[4];
lean_object* v_a_1408_ = _args[5];
lean_object* v_a_1409_ = _args[6];
lean_object* v_a_1410_ = _args[7];
lean_object* v_a_1411_ = _args[8];
lean_object* v_a_1412_ = _args[9];
lean_object* v_a_1413_ = _args[10];
lean_object* v_a_1414_ = _args[11];
lean_object* v_a_1415_ = _args[12];
lean_object* v_a_1416_ = _args[13];
lean_object* v_a_1417_ = _args[14];
lean_object* v_a_1418_ = _args[15];
lean_object* v_a_1419_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1420_; uint8_t v_eqTrue_boxed_1421_; lean_object* v_res_1422_; 
v_strict_boxed_1420_ = lean_unbox(v_strict_1406_);
v_eqTrue_boxed_1421_ = lean_unbox(v_eqTrue_1407_);
v_res_1422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1403_, v_lhs_1404_, v_rhs_1405_, v_strict_boxed_1420_, v_eqTrue_boxed_1421_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* v_e_1423_, lean_object* v_lhs_1424_, lean_object* v_rhs_1425_, uint8_t v_strict_1426_, uint8_t v_eqTrue_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1424_, v_a_1429_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = 0;
lean_inc(v_a_1438_);
lean_inc_ref(v_a_1437_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
lean_inc(v_a_1434_);
lean_inc_ref(v_a_1433_);
lean_inc(v_a_1432_);
lean_inc_ref(v_a_1431_);
lean_inc(v_a_1430_);
lean_inc(v_a_1429_);
lean_inc(v_a_1428_);
v___x_1443_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_lhs_1424_, v___x_1442_, v_a_1441_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1510_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1510_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1510_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
if (lean_obj_tag(v_a_1444_) == 1)
{
lean_object* v_val_1448_; lean_object* v___x_1449_; 
lean_del_object(v___x_1446_);
v_val_1448_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_val_1448_);
lean_dec_ref(v_a_1444_);
v___x_1449_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1425_, v_a_1429_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
lean_inc(v_a_1438_);
lean_inc_ref(v_a_1437_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
lean_inc(v_a_1434_);
lean_inc_ref(v_a_1433_);
lean_inc(v_a_1432_);
lean_inc_ref(v_a_1431_);
lean_inc(v_a_1430_);
lean_inc(v_a_1429_);
lean_inc(v_a_1428_);
v___x_1451_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_rhs_1425_, v___x_1442_, v_a_1450_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1489_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1489_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1489_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
if (lean_obj_tag(v_a_1452_) == 1)
{
lean_del_object(v___x_1454_);
if (v_eqTrue_1427_ == 0)
{
lean_object* v_val_1456_; lean_object* v___x_1457_; 
v_val_1456_ = lean_ctor_get(v_a_1452_, 0);
lean_inc(v_val_1456_);
lean_dec_ref(v_a_1452_);
v___x_1457_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; uint8_t v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = lean_unbox(v_a_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v_a_1458_);
lean_dec(v_val_1456_);
lean_dec(v_val_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
v___f_1460_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1460_, 0, v_a_1428_);
lean_closure_set(v___f_1460_, 1, v_e_1423_);
v___x_1461_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1462_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1461_, v___f_1460_, v_a_1429_);
lean_dec(v_a_1429_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___y_1466_; 
lean_inc(v_val_1448_);
lean_inc(v_val_1456_);
v___x_1463_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_val_1456_);
lean_ctor_set(v___x_1463_, 1, v_val_1448_);
v___x_1464_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1463_);
if (v_strict_1426_ == 0)
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
v___y_1466_ = v___x_1470_;
goto v___jp_1465_;
}
else
{
lean_dec(v_a_1458_);
v___y_1466_ = v_eqTrue_1427_;
goto v___jp_1465_;
}
v___jp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v_e_1423_);
lean_ctor_set(v___x_1467_, 1, v_val_1448_);
lean_ctor_set(v___x_1467_, 2, v_val_1456_);
v___x_1468_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1464_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*2, v___y_1466_);
v___x_1469_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1468_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_val_1456_);
lean_dec(v_val_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_e_1423_);
v_a_1471_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1457_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1457_);
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
lean_object* v_val_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_val_1479_ = lean_ctor_get(v_a_1452_, 0);
lean_inc(v_val_1479_);
lean_dec_ref(v_a_1452_);
lean_inc(v_val_1479_);
lean_inc(v_val_1448_);
v___x_1480_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_val_1448_);
lean_ctor_set(v___x_1480_, 1, v_val_1479_);
v___x_1481_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v_e_1423_);
lean_ctor_set(v___x_1482_, 1, v_val_1448_);
lean_ctor_set(v___x_1482_, 2, v_val_1479_);
v___x_1483_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*2, v_strict_1426_);
v___x_1484_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1483_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_dec(v_a_1452_);
lean_dec(v_val_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_e_1423_);
v___x_1485_ = lean_box(0);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1485_);
v___x_1487_ = v___x_1454_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_val_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_e_1423_);
v_a_1490_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1451_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1451_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_val_1448_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_e_1423_);
v_a_1498_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1449_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1449_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_dec(v_a_1444_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_e_1423_);
v___x_1506_ = lean_box(0);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1506_);
v___x_1508_ = v___x_1446_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_e_1423_);
v_a_1511_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1443_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1443_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
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
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_lhs_1424_);
lean_dec_ref(v_e_1423_);
v_a_1519_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1440_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1440_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1527_ = _args[0];
lean_object* v_lhs_1528_ = _args[1];
lean_object* v_rhs_1529_ = _args[2];
lean_object* v_strict_1530_ = _args[3];
lean_object* v_eqTrue_1531_ = _args[4];
lean_object* v_a_1532_ = _args[5];
lean_object* v_a_1533_ = _args[6];
lean_object* v_a_1534_ = _args[7];
lean_object* v_a_1535_ = _args[8];
lean_object* v_a_1536_ = _args[9];
lean_object* v_a_1537_ = _args[10];
lean_object* v_a_1538_ = _args[11];
lean_object* v_a_1539_ = _args[12];
lean_object* v_a_1540_ = _args[13];
lean_object* v_a_1541_ = _args[14];
lean_object* v_a_1542_ = _args[15];
lean_object* v_a_1543_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1544_; uint8_t v_eqTrue_boxed_1545_; lean_object* v_res_1546_; 
v_strict_boxed_1544_ = lean_unbox(v_strict_1530_);
v_eqTrue_boxed_1545_ = lean_unbox(v_eqTrue_1531_);
v_res_1546_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1527_, v_lhs_1528_, v_rhs_1529_, v_strict_boxed_1544_, v_eqTrue_boxed_1545_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* v_e_1547_, lean_object* v_lhs_1548_, lean_object* v_rhs_1549_, uint8_t v_strict_1550_, uint8_t v_eqTrue_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc(v_a_1552_);
lean_inc_ref(v_lhs_1548_);
v___x_1566_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_lhs_1548_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_fst_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v_fst_1568_ = lean_ctor_get(v_a_1567_, 0);
lean_inc(v_fst_1568_);
lean_dec(v_a_1567_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_rhs_1549_);
v___x_1569_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_rhs_1549_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_fst_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1654_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v_fst_1571_ = lean_ctor_get(v_a_1570_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_a_1570_, 1);
lean_dec(v_unused_1655_);
v___x_1573_ = v_a_1570_;
v_isShared_1574_ = v_isSharedCheck_1654_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_fst_1571_);
lean_dec(v_a_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1654_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Grind_getGeneration___redArg(v_lhs_1548_, v_a_1553_);
lean_dec_ref(v_lhs_1548_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_id_1577_; lean_object* v_structId_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
v_id_1577_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_id_1577_);
v_structId_1578_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_structId_1578_);
lean_dec(v_a_1565_);
v___x_1579_ = 0;
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc(v_structId_1578_);
v___x_1580_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1568_, v___x_1579_, v_a_1576_, v_structId_1578_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1637_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1637_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1637_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; 
lean_del_object(v___x_1583_);
v_val_1585_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1585_);
lean_dec_ref(v_a_1581_);
v___x_1586_ = l_Lean_Meta_Grind_getGeneration___redArg(v_rhs_1549_, v_a_1553_);
lean_dec_ref(v_rhs_1549_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc(v_structId_1578_);
v___x_1588_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_1571_, v___x_1579_, v_a_1587_, v_structId_1578_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1616_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1616_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1616_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
if (lean_obj_tag(v_a_1589_) == 1)
{
lean_del_object(v___x_1591_);
if (v_eqTrue_1551_ == 0)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; 
v_val_1593_ = lean_ctor_get(v_a_1589_, 0);
lean_inc(v_val_1593_);
lean_dec_ref(v_a_1589_);
lean_inc(v_val_1585_);
lean_inc(v_val_1593_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 3);
lean_ctor_set(v___x_1573_, 1, v_val_1585_);
lean_ctor_set(v___x_1573_, 0, v_val_1593_);
v___x_1595_ = v___x_1573_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_val_1585_);
v___x_1595_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; uint8_t v___y_1598_; 
v___x_1596_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1595_);
if (v_strict_1550_ == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = 1;
v___y_1598_ = v___x_1602_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v_eqTrue_1551_;
goto v___jp_1597_;
}
v___jp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1599_, 0, v_e_1547_);
lean_ctor_set(v___x_1599_, 1, v_id_1577_);
lean_ctor_set(v___x_1599_, 2, v_val_1585_);
lean_ctor_set(v___x_1599_, 3, v_val_1593_);
v___x_1600_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1600_, 0, v___x_1596_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*2, v___y_1598_);
v___x_1601_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1600_, v_structId_1578_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
return v___x_1601_;
}
}
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
v_val_1604_ = lean_ctor_get(v_a_1589_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v_a_1589_);
lean_inc(v_val_1604_);
lean_inc(v_val_1585_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 3);
lean_ctor_set(v___x_1573_, 1, v_val_1604_);
lean_ctor_set(v___x_1573_, 0, v_val_1585_);
v___x_1606_ = v___x_1573_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_val_1585_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1608_, 0, v_e_1547_);
lean_ctor_set(v___x_1608_, 1, v_id_1577_);
lean_ctor_set(v___x_1608_, 2, v_val_1585_);
lean_ctor_set(v___x_1608_, 3, v_val_1604_);
v___x_1609_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_ctor_set_uint8(v___x_1609_, sizeof(void*)*2, v_strict_1550_);
v___x_1610_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1609_, v_structId_1578_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
return v___x_1610_;
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
lean_dec(v_a_1589_);
lean_dec(v_val_1585_);
lean_dec(v_structId_1578_);
lean_dec(v_id_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_e_1547_);
v___x_1612_ = lean_box(0);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1612_);
v___x_1614_ = v___x_1591_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
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
lean_dec(v_val_1585_);
lean_dec(v_structId_1578_);
lean_dec(v_id_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_e_1547_);
v_a_1617_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1588_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1588_);
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
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_val_1585_);
lean_dec(v_structId_1578_);
lean_dec(v_id_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_fst_1571_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_e_1547_);
v_a_1625_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1586_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1586_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_a_1581_);
lean_dec(v_structId_1578_);
lean_dec(v_id_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_fst_1571_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_e_1547_);
v___x_1633_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1633_);
v___x_1635_ = v___x_1583_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
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
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_structId_1578_);
lean_dec(v_id_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_fst_1571_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_e_1547_);
v_a_1638_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1580_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1580_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_del_object(v___x_1573_);
lean_dec(v_fst_1571_);
lean_dec(v_fst_1568_);
lean_dec(v_a_1565_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_e_1547_);
v_a_1646_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1575_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1575_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_fst_1568_);
lean_dec(v_a_1565_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_lhs_1548_);
lean_dec_ref(v_e_1547_);
v_a_1656_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1569_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1569_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_lhs_1548_);
lean_dec_ref(v_e_1547_);
v_a_1664_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1566_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1566_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_rhs_1549_);
lean_dec_ref(v_lhs_1548_);
lean_dec_ref(v_e_1547_);
v_a_1672_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1564_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1564_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args){
lean_object* v_e_1680_ = _args[0];
lean_object* v_lhs_1681_ = _args[1];
lean_object* v_rhs_1682_ = _args[2];
lean_object* v_strict_1683_ = _args[3];
lean_object* v_eqTrue_1684_ = _args[4];
lean_object* v_a_1685_ = _args[5];
lean_object* v_a_1686_ = _args[6];
lean_object* v_a_1687_ = _args[7];
lean_object* v_a_1688_ = _args[8];
lean_object* v_a_1689_ = _args[9];
lean_object* v_a_1690_ = _args[10];
lean_object* v_a_1691_ = _args[11];
lean_object* v_a_1692_ = _args[12];
lean_object* v_a_1693_ = _args[13];
lean_object* v_a_1694_ = _args[14];
lean_object* v_a_1695_ = _args[15];
lean_object* v_a_1696_ = _args[16];
_start:
{
uint8_t v_strict_boxed_1697_; uint8_t v_eqTrue_boxed_1698_; lean_object* v_res_1699_; 
v_strict_boxed_1697_ = lean_unbox(v_strict_1683_);
v_eqTrue_boxed_1698_ = lean_unbox(v_eqTrue_1684_);
v_res_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1680_, v_lhs_1681_, v_rhs_1682_, v_strict_boxed_1697_, v_eqTrue_boxed_1698_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v_res_1699_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 0)
{
if (lean_obj_tag(v_x_1701_) == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = 1;
return v___x_1702_;
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = 0;
return v___x_1703_;
}
}
else
{
if (lean_obj_tag(v_x_1701_) == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = 0;
return v___x_1704_;
}
else
{
lean_object* v_val_1705_; lean_object* v_val_1706_; uint8_t v___x_1707_; 
v_val_1705_ = lean_ctor_get(v_x_1700_, 0);
v_val_1706_ = lean_ctor_get(v_x_1701_, 0);
v___x_1707_ = lean_expr_eqv(v_val_1705_, v_val_1706_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v_x_1708_, v_x_1709_);
lean_dec(v_x_1709_);
lean_dec(v_x_1708_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* v_e_1712_, uint8_t v_eqTrue_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1716_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1937_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1937_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1937_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
uint8_t v_linarith_1730_; 
v_linarith_1730_ = lean_ctor_get_uint8(v_a_1726_, sizeof(void*)*11 + 22);
lean_dec(v_a_1726_);
if (v_linarith_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v___x_1731_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = l_Lean_Expr_getAppNumArgs(v_e_1712_);
v___x_1736_ = lean_unsigned_to_nat(4u);
v___x_1737_ = lean_nat_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_dec(v___x_1735_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v___x_1738_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1738_);
v___x_1740_ = v___x_1728_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_sub(v___x_1735_, v___x_1742_);
lean_inc(v___x_1743_);
v___x_1744_ = l_Lean_Expr_getRevArg_x21(v_e_1712_, v___x_1743_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc(v_a_1719_);
lean_inc_ref(v_a_1718_);
lean_inc(v_a_1717_);
lean_inc_ref(v_a_1716_);
lean_inc(v_a_1715_);
lean_inc(v_a_1714_);
lean_inc_ref(v___x_1744_);
v___x_1745_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v___x_1744_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1928_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1928_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1928_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v_strict_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; 
v___x_1750_ = lean_nat_sub(v___x_1743_, v___x_1742_);
lean_dec(v___x_1743_);
v___x_1751_ = l_Lean_Expr_getRevArg_x21(v_e_1712_, v___x_1750_);
v___x_1752_ = lean_unsigned_to_nat(2u);
v___x_1753_ = lean_nat_sub(v___x_1735_, v___x_1752_);
v___x_1754_ = lean_nat_sub(v___x_1753_, v___x_1742_);
lean_dec(v___x_1753_);
v___x_1755_ = l_Lean_Expr_getRevArg_x21(v_e_1712_, v___x_1754_);
v___x_1756_ = lean_unsigned_to_nat(3u);
v___x_1757_ = lean_nat_sub(v___x_1735_, v___x_1756_);
lean_dec(v___x_1735_);
v___x_1758_ = lean_nat_sub(v___x_1757_, v___x_1742_);
lean_dec(v___x_1757_);
v___x_1759_ = l_Lean_Expr_getRevArg_x21(v_e_1712_, v___x_1758_);
if (lean_obj_tag(v_a_1746_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
lean_del_object(v___x_1748_);
lean_dec_ref(v___x_1744_);
lean_del_object(v___x_1728_);
v_val_1786_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_val_1786_);
lean_dec_ref(v_a_1746_);
v___x_1787_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_val_1786_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_leFn_x3f_1792_; lean_object* v_ltFn_x3f_1793_; uint8_t v___x_1794_; 
v_leFn_x3f_1792_ = lean_ctor_get(v_a_1788_, 20);
lean_inc(v_leFn_x3f_1792_);
v_ltFn_x3f_1793_ = lean_ctor_get(v_a_1788_, 21);
lean_inc(v_ltFn_x3f_1793_);
lean_dec(v_a_1788_);
v___x_1794_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_leFn_x3f_1792_, v___x_1751_);
lean_dec(v_leFn_x3f_1792_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
v___x_1795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(v_ltFn_x3f_1793_, v___x_1751_);
lean_dec_ref(v___x_1751_);
lean_dec(v_ltFn_x3f_1793_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec(v_val_1786_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v___x_1796_ = lean_box(0);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1796_);
v___x_1798_ = v___x_1790_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
else
{
lean_del_object(v___x_1790_);
v_strict_1761_ = v___x_1737_;
v___y_1762_ = v_val_1786_;
v___y_1763_ = v_a_1714_;
v___y_1764_ = v_a_1715_;
v___y_1765_ = v_a_1716_;
v___y_1766_ = v_a_1717_;
v___y_1767_ = v_a_1718_;
v___y_1768_ = v_a_1719_;
v___y_1769_ = v_a_1720_;
v___y_1770_ = v_a_1721_;
v___y_1771_ = v_a_1722_;
v___y_1772_ = v_a_1723_;
goto v___jp_1760_;
}
}
else
{
uint8_t v___x_1800_; 
lean_dec(v_ltFn_x3f_1793_);
lean_del_object(v___x_1790_);
lean_dec_ref(v___x_1751_);
v___x_1800_ = 0;
v_strict_1761_ = v___x_1800_;
v___y_1762_ = v_val_1786_;
v___y_1763_ = v_a_1714_;
v___y_1764_ = v_a_1715_;
v___y_1765_ = v_a_1716_;
v___y_1766_ = v_a_1717_;
v___y_1767_ = v_a_1718_;
v___y_1768_ = v_a_1719_;
v___y_1769_ = v_a_1720_;
v___y_1770_ = v_a_1721_;
v___y_1771_ = v_a_1722_;
v___y_1772_ = v_a_1723_;
goto v___jp_1760_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_val_1786_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v_a_1802_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1787_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1787_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_a_1746_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc(v_a_1719_);
lean_inc_ref(v_a_1718_);
lean_inc(v_a_1717_);
lean_inc_ref(v_a_1716_);
lean_inc(v_a_1715_);
lean_inc(v_a_1714_);
v___x_1810_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v___x_1744_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1919_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1919_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1919_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
if (lean_obj_tag(v_a_1811_) == 1)
{
lean_object* v_val_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1914_; 
v_val_1815_ = lean_ctor_get(v_a_1811_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_a_1811_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1817_ = v_a_1811_;
v_isShared_1818_ = v_isSharedCheck_1914_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_val_1815_);
lean_dec(v_a_1811_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1914_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_1815_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1905_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1905_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1905_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_leInst_x3f_1829_; lean_object* v_ltInst_x3f_1830_; lean_object* v_lawfulOrderLTInst_x3f_1831_; lean_object* v_isPreorderInst_x3f_1832_; lean_object* v_orderedAddInst_x3f_1833_; lean_object* v_isLinearInst_x3f_1834_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; uint8_t v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1848_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; uint8_t v___y_1870_; uint8_t v_strict_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1888_; uint8_t v___y_1899_; uint8_t v___y_1901_; uint8_t v___y_1903_; 
v_leInst_x3f_1829_ = lean_ctor_get(v_a_1820_, 5);
lean_inc(v_leInst_x3f_1829_);
v_ltInst_x3f_1830_ = lean_ctor_get(v_a_1820_, 6);
lean_inc(v_ltInst_x3f_1830_);
v_lawfulOrderLTInst_x3f_1831_ = lean_ctor_get(v_a_1820_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1831_);
v_isPreorderInst_x3f_1832_ = lean_ctor_get(v_a_1820_, 8);
lean_inc(v_isPreorderInst_x3f_1832_);
v_orderedAddInst_x3f_1833_ = lean_ctor_get(v_a_1820_, 9);
lean_inc(v_orderedAddInst_x3f_1833_);
v_isLinearInst_x3f_1834_ = lean_ctor_get(v_a_1820_, 10);
lean_inc(v_isLinearInst_x3f_1834_);
lean_dec(v_a_1820_);
if (lean_obj_tag(v_leInst_x3f_1829_) == 0)
{
if (v___x_1737_ == 0)
{
v___y_1903_ = v___x_1737_;
goto v___jp_1902_;
}
else
{
lean_dec(v_isPreorderInst_x3f_1832_);
v___y_1901_ = v___x_1737_;
goto v___jp_1900_;
}
}
else
{
uint8_t v___x_1904_; 
v___x_1904_ = 0;
v___y_1903_ = v___x_1904_;
goto v___jp_1902_;
}
v___jp_1824_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
v___jp_1835_:
{
if (v___y_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_isLinearInst_x3f_1834_);
lean_del_object(v___x_1813_);
v___x_1849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1712_, v___x_1755_, v___x_1759_, v___y_1843_, v_eqTrue_1713_, v___y_1847_, v___y_1846_, v___y_1842_, v___y_1836_, v___y_1841_, v___y_1840_, v___y_1845_, v___y_1839_, v___y_1837_, v___y_1838_, v___y_1844_);
return v___x_1849_;
}
else
{
if (lean_obj_tag(v_isLinearInst_x3f_1834_) == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v_e_1712_);
v___x_1850_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1850_);
v___x_1852_ = v___x_1813_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; 
lean_dec_ref(v_isLinearInst_x3f_1834_);
lean_del_object(v___x_1813_);
v___x_1854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(v_e_1712_, v___x_1755_, v___x_1759_, v___y_1843_, v_eqTrue_1713_, v___y_1847_, v___y_1846_, v___y_1842_, v___y_1836_, v___y_1841_, v___y_1840_, v___y_1845_, v___y_1839_, v___y_1837_, v___y_1838_, v___y_1844_);
return v___x_1854_;
}
}
}
v___jp_1855_:
{
if (v_eqTrue_1713_ == 0)
{
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___y_1857_;
v___y_1838_ = v___y_1858_;
v___y_1839_ = v___y_1859_;
v___y_1840_ = v___y_1860_;
v___y_1841_ = v___y_1861_;
v___y_1842_ = v___y_1862_;
v___y_1843_ = v___y_1863_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___y_1865_;
v___y_1846_ = v___y_1866_;
v___y_1847_ = v___y_1867_;
v___y_1848_ = v___x_1737_;
goto v___jp_1835_;
}
else
{
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___y_1857_;
v___y_1838_ = v___y_1858_;
v___y_1839_ = v___y_1859_;
v___y_1840_ = v___y_1860_;
v___y_1841_ = v___y_1861_;
v___y_1842_ = v___y_1862_;
v___y_1843_ = v___y_1863_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___y_1865_;
v___y_1846_ = v___y_1866_;
v___y_1847_ = v___y_1867_;
v___y_1848_ = v___y_1868_;
goto v___jp_1835_;
}
}
v___jp_1869_:
{
if (v_strict_1871_ == 0)
{
lean_dec(v_lawfulOrderLTInst_x3f_1831_);
lean_del_object(v___x_1748_);
v___y_1856_ = v___y_1875_;
v___y_1857_ = v___y_1880_;
v___y_1858_ = v___y_1881_;
v___y_1859_ = v___y_1879_;
v___y_1860_ = v___y_1877_;
v___y_1861_ = v___y_1876_;
v___y_1862_ = v___y_1874_;
v___y_1863_ = v_strict_1871_;
v___y_1864_ = v___y_1882_;
v___y_1865_ = v___y_1878_;
v___y_1866_ = v___y_1873_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v_strict_1871_;
goto v___jp_1855_;
}
else
{
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1831_) == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v_isLinearInst_x3f_1834_);
lean_del_object(v___x_1813_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v_e_1712_);
v___x_1883_ = lean_box(0);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1883_);
v___x_1885_ = v___x_1748_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
else
{
lean_dec_ref(v_lawfulOrderLTInst_x3f_1831_);
lean_del_object(v___x_1748_);
v___y_1856_ = v___y_1875_;
v___y_1857_ = v___y_1880_;
v___y_1858_ = v___y_1881_;
v___y_1859_ = v___y_1879_;
v___y_1860_ = v___y_1877_;
v___y_1861_ = v___y_1876_;
v___y_1862_ = v___y_1874_;
v___y_1863_ = v_strict_1871_;
v___y_1864_ = v___y_1882_;
v___y_1865_ = v___y_1878_;
v___y_1866_ = v___y_1873_;
v___y_1867_ = v___y_1872_;
v___y_1868_ = v___y_1870_;
goto v___jp_1855_;
}
}
}
v___jp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1751_);
v___x_1890_ = v___x_1817_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1751_);
v___x_1890_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1890_, v_leInst_x3f_1829_);
lean_dec(v_leInst_x3f_1829_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_1890_, v_ltInst_x3f_1830_);
lean_dec(v_ltInst_x3f_1830_);
lean_dec_ref(v___x_1890_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_isLinearInst_x3f_1834_);
lean_dec(v_lawfulOrderLTInst_x3f_1831_);
lean_dec(v_val_1815_);
lean_del_object(v___x_1813_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_del_object(v___x_1748_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v___x_1893_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1893_);
v___x_1895_ = v___x_1728_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_del_object(v___x_1728_);
v___y_1870_ = v___y_1888_;
v_strict_1871_ = v___x_1737_;
v___y_1872_ = v_val_1815_;
v___y_1873_ = v_a_1714_;
v___y_1874_ = v_a_1715_;
v___y_1875_ = v_a_1716_;
v___y_1876_ = v_a_1717_;
v___y_1877_ = v_a_1718_;
v___y_1878_ = v_a_1719_;
v___y_1879_ = v_a_1720_;
v___y_1880_ = v_a_1721_;
v___y_1881_ = v_a_1722_;
v___y_1882_ = v_a_1723_;
goto v___jp_1869_;
}
}
else
{
lean_dec_ref(v___x_1890_);
lean_dec(v_ltInst_x3f_1830_);
lean_del_object(v___x_1728_);
v___y_1870_ = v___y_1888_;
v_strict_1871_ = v___y_1888_;
v___y_1872_ = v_val_1815_;
v___y_1873_ = v_a_1714_;
v___y_1874_ = v_a_1715_;
v___y_1875_ = v_a_1716_;
v___y_1876_ = v_a_1717_;
v___y_1877_ = v_a_1718_;
v___y_1878_ = v_a_1719_;
v___y_1879_ = v_a_1720_;
v___y_1880_ = v_a_1721_;
v___y_1881_ = v_a_1722_;
v___y_1882_ = v_a_1723_;
goto v___jp_1869_;
}
}
}
v___jp_1898_:
{
if (lean_obj_tag(v_orderedAddInst_x3f_1833_) == 0)
{
if (v___x_1737_ == 0)
{
lean_del_object(v___x_1822_);
v___y_1888_ = v___x_1737_;
goto v___jp_1887_;
}
else
{
lean_dec(v_isLinearInst_x3f_1834_);
lean_dec(v_lawfulOrderLTInst_x3f_1831_);
lean_dec(v_ltInst_x3f_1830_);
lean_dec(v_leInst_x3f_1829_);
lean_del_object(v___x_1817_);
lean_dec(v_val_1815_);
lean_del_object(v___x_1813_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_del_object(v___x_1748_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
goto v___jp_1824_;
}
}
else
{
lean_dec_ref(v_orderedAddInst_x3f_1833_);
lean_del_object(v___x_1822_);
v___y_1888_ = v___y_1899_;
goto v___jp_1887_;
}
}
v___jp_1900_:
{
if (v___y_1901_ == 0)
{
v___y_1899_ = v___y_1901_;
goto v___jp_1898_;
}
else
{
lean_dec(v_isLinearInst_x3f_1834_);
lean_dec(v_orderedAddInst_x3f_1833_);
lean_dec(v_lawfulOrderLTInst_x3f_1831_);
lean_dec(v_ltInst_x3f_1830_);
lean_dec(v_leInst_x3f_1829_);
lean_del_object(v___x_1817_);
lean_dec(v_val_1815_);
lean_del_object(v___x_1813_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_del_object(v___x_1748_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
goto v___jp_1824_;
}
}
v___jp_1902_:
{
if (lean_obj_tag(v_isPreorderInst_x3f_1832_) == 0)
{
v___y_1901_ = v___x_1737_;
goto v___jp_1900_;
}
else
{
lean_dec_ref(v_isPreorderInst_x3f_1832_);
v___y_1899_ = v___y_1903_;
goto v___jp_1898_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1817_);
lean_dec(v_val_1815_);
lean_del_object(v___x_1813_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_del_object(v___x_1748_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v_a_1906_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1819_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1819_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v_a_1811_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_del_object(v___x_1748_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v___x_1915_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1915_);
v___x_1917_ = v___x_1813_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1751_);
lean_del_object(v___x_1748_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v_a_1920_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1810_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1810_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
v___jp_1760_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; uint8_t v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = lean_unbox(v_a_1774_);
lean_dec(v_a_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(v_e_1712_, v___x_1755_, v___x_1759_, v_strict_1761_, v_eqTrue_1713_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(v_e_1712_, v___x_1755_, v___x_1759_, v_strict_1761_, v_eqTrue_1713_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1777_;
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v_e_1712_);
v_a_1778_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1773_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1773_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1743_);
lean_dec(v___x_1735_);
lean_del_object(v___x_1728_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v_a_1929_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1745_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1745_);
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
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_e_1712_);
v_a_1938_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1725_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1725_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* v_e_1946_, lean_object* v_eqTrue_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
uint8_t v_eqTrue_boxed_1959_; lean_object* v_res_1960_; 
v_eqTrue_boxed_1959_ = lean_unbox(v_eqTrue_1947_);
v_res_1960_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(v_e_1946_, v_eqTrue_boxed_1959_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v_res_1960_;
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
