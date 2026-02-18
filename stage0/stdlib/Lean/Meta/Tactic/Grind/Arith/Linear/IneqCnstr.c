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
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0_value;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__4_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10_value;
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object**);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Expr_appArg_x21(x_3);
x_5 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_2);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_23 = 1;
x_24 = lean_usize_shift_left(x_23, x_4);
x_25 = lean_usize_sub(x_24, x_23);
x_26 = lean_usize_land(x_3, x_25);
x_27 = 5;
x_28 = lean_usize_sub(x_4, x_27);
x_29 = lean_array_fget(x_5, x_7);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_7, x_30);
x_32 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_29, x_26, x_28);
x_33 = lean_array_fset(x_31, x_7, x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_39; 
lean_inc_ref(x_35);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = l_Lean_PersistentArray_push___redArg(x_41, x_1);
x_45 = lean_array_fset(x_43, x_36, x_44);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_45);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_46 = lean_array_fget(x_35, x_36);
x_47 = lean_box(0);
x_48 = lean_array_fset(x_35, x_36, x_47);
x_49 = l_Lean_PersistentArray_push___redArg(x_46, x_1);
x_50 = lean_array_fset(x_48, x_36, x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = l_Lean_PersistentArray_push___redArg(x_16, x_1);
x_20 = lean_array_fset(x_18, x_13, x_19);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_20);
return x_3;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get_usize(x_3, 4);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_nat_dec_le(x_25, x_4);
if (x_26 == 0)
{
size_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_4);
x_28 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_21, x_27, x_24);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set_usize(x_29, 4, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_nat_sub(x_4, x_25);
x_31 = lean_array_get_size(x_22);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec_ref(x_1);
x_33 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_usize(x_33, 4, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_fget(x_22, x_30);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_22, x_30, x_35);
x_37 = l_Lean_PersistentArray_push___redArg(x_34, x_1);
x_38 = lean_array_fset(x_36, x_30, x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_25);
lean_ctor_set_usize(x_39, 4, x_24);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_24, 33);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_30 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_29, x_26, x_3);
lean_ctor_set(x_24, 33, x_30);
x_31 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 2);
x_35 = lean_ctor_get(x_24, 3);
x_36 = lean_ctor_get(x_24, 4);
x_37 = lean_ctor_get(x_24, 5);
x_38 = lean_ctor_get(x_24, 6);
x_39 = lean_ctor_get(x_24, 7);
x_40 = lean_ctor_get(x_24, 8);
x_41 = lean_ctor_get(x_24, 9);
x_42 = lean_ctor_get(x_24, 10);
x_43 = lean_ctor_get(x_24, 11);
x_44 = lean_ctor_get(x_24, 12);
x_45 = lean_ctor_get(x_24, 13);
x_46 = lean_ctor_get(x_24, 14);
x_47 = lean_ctor_get(x_24, 15);
x_48 = lean_ctor_get(x_24, 16);
x_49 = lean_ctor_get(x_24, 17);
x_50 = lean_ctor_get(x_24, 18);
x_51 = lean_ctor_get(x_24, 19);
x_52 = lean_ctor_get(x_24, 20);
x_53 = lean_ctor_get(x_24, 21);
x_54 = lean_ctor_get(x_24, 22);
x_55 = lean_ctor_get(x_24, 23);
x_56 = lean_ctor_get(x_24, 24);
x_57 = lean_ctor_get(x_24, 25);
x_58 = lean_ctor_get(x_24, 26);
x_59 = lean_ctor_get(x_24, 27);
x_60 = lean_ctor_get(x_24, 28);
x_61 = lean_ctor_get(x_24, 29);
x_62 = lean_ctor_get(x_24, 30);
x_63 = lean_ctor_get(x_24, 31);
x_64 = lean_ctor_get(x_24, 32);
x_65 = lean_ctor_get(x_24, 33);
x_66 = lean_ctor_get(x_24, 34);
x_67 = lean_ctor_get(x_24, 35);
x_68 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_69 = lean_ctor_get(x_24, 36);
x_70 = lean_ctor_get(x_24, 37);
x_71 = lean_ctor_get(x_24, 38);
x_72 = lean_ctor_get(x_24, 39);
x_73 = lean_ctor_get(x_24, 40);
x_74 = lean_ctor_get(x_24, 41);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_75 = lean_box(0);
x_76 = lean_array_fset(x_5, x_1, x_75);
x_77 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_78 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_77, x_65, x_3);
x_79 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_33);
lean_ctor_set(x_79, 2, x_34);
lean_ctor_set(x_79, 3, x_35);
lean_ctor_set(x_79, 4, x_36);
lean_ctor_set(x_79, 5, x_37);
lean_ctor_set(x_79, 6, x_38);
lean_ctor_set(x_79, 7, x_39);
lean_ctor_set(x_79, 8, x_40);
lean_ctor_set(x_79, 9, x_41);
lean_ctor_set(x_79, 10, x_42);
lean_ctor_set(x_79, 11, x_43);
lean_ctor_set(x_79, 12, x_44);
lean_ctor_set(x_79, 13, x_45);
lean_ctor_set(x_79, 14, x_46);
lean_ctor_set(x_79, 15, x_47);
lean_ctor_set(x_79, 16, x_48);
lean_ctor_set(x_79, 17, x_49);
lean_ctor_set(x_79, 18, x_50);
lean_ctor_set(x_79, 19, x_51);
lean_ctor_set(x_79, 20, x_52);
lean_ctor_set(x_79, 21, x_53);
lean_ctor_set(x_79, 22, x_54);
lean_ctor_set(x_79, 23, x_55);
lean_ctor_set(x_79, 24, x_56);
lean_ctor_set(x_79, 25, x_57);
lean_ctor_set(x_79, 26, x_58);
lean_ctor_set(x_79, 27, x_59);
lean_ctor_set(x_79, 28, x_60);
lean_ctor_set(x_79, 29, x_61);
lean_ctor_set(x_79, 30, x_62);
lean_ctor_set(x_79, 31, x_63);
lean_ctor_set(x_79, 32, x_64);
lean_ctor_set(x_79, 33, x_78);
lean_ctor_set(x_79, 34, x_66);
lean_ctor_set(x_79, 35, x_67);
lean_ctor_set(x_79, 36, x_69);
lean_ctor_set(x_79, 37, x_70);
lean_ctor_set(x_79, 38, x_71);
lean_ctor_set(x_79, 39, x_72);
lean_ctor_set(x_79, 40, x_73);
lean_ctor_set(x_79, 41, x_74);
lean_ctor_set_uint8(x_79, sizeof(void*)*42, x_68);
x_80 = lean_array_fset(x_76, x_1, x_79);
lean_ctor_set(x_4, 0, x_80);
return x_4;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_4);
x_81 = lean_array_fget(x_5, x_1);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_81, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 4);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_81, 5);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 6);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 7);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 8);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 9);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 10);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 11);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 12);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 13);
lean_inc(x_95);
x_96 = lean_ctor_get(x_81, 14);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 15);
lean_inc(x_97);
x_98 = lean_ctor_get(x_81, 16);
lean_inc(x_98);
x_99 = lean_ctor_get(x_81, 17);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_81, 18);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_81, 19);
lean_inc(x_101);
x_102 = lean_ctor_get(x_81, 20);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 21);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 22);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_81, 23);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_81, 24);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_81, 25);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 26);
lean_inc(x_108);
x_109 = lean_ctor_get(x_81, 27);
lean_inc(x_109);
x_110 = lean_ctor_get(x_81, 28);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_81, 29);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_81, 30);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_81, 31);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_81, 32);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_81, 33);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_81, 34);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_81, 35);
lean_inc_ref(x_117);
x_118 = lean_ctor_get_uint8(x_81, sizeof(void*)*42);
x_119 = lean_ctor_get(x_81, 36);
lean_inc(x_119);
x_120 = lean_ctor_get(x_81, 37);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_81, 38);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_81, 39);
lean_inc(x_122);
x_123 = lean_ctor_get(x_81, 40);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_81, 41);
lean_inc_ref(x_124);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 lean_ctor_release(x_81, 6);
 lean_ctor_release(x_81, 7);
 lean_ctor_release(x_81, 8);
 lean_ctor_release(x_81, 9);
 lean_ctor_release(x_81, 10);
 lean_ctor_release(x_81, 11);
 lean_ctor_release(x_81, 12);
 lean_ctor_release(x_81, 13);
 lean_ctor_release(x_81, 14);
 lean_ctor_release(x_81, 15);
 lean_ctor_release(x_81, 16);
 lean_ctor_release(x_81, 17);
 lean_ctor_release(x_81, 18);
 lean_ctor_release(x_81, 19);
 lean_ctor_release(x_81, 20);
 lean_ctor_release(x_81, 21);
 lean_ctor_release(x_81, 22);
 lean_ctor_release(x_81, 23);
 lean_ctor_release(x_81, 24);
 lean_ctor_release(x_81, 25);
 lean_ctor_release(x_81, 26);
 lean_ctor_release(x_81, 27);
 lean_ctor_release(x_81, 28);
 lean_ctor_release(x_81, 29);
 lean_ctor_release(x_81, 30);
 lean_ctor_release(x_81, 31);
 lean_ctor_release(x_81, 32);
 lean_ctor_release(x_81, 33);
 lean_ctor_release(x_81, 34);
 lean_ctor_release(x_81, 35);
 lean_ctor_release(x_81, 36);
 lean_ctor_release(x_81, 37);
 lean_ctor_release(x_81, 38);
 lean_ctor_release(x_81, 39);
 lean_ctor_release(x_81, 40);
 lean_ctor_release(x_81, 41);
 x_125 = x_81;
} else {
 lean_dec_ref(x_81);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
x_127 = lean_array_fset(x_5, x_1, x_126);
x_128 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_129 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_128, x_115, x_3);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 42, 1);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_82);
lean_ctor_set(x_130, 1, x_83);
lean_ctor_set(x_130, 2, x_84);
lean_ctor_set(x_130, 3, x_85);
lean_ctor_set(x_130, 4, x_86);
lean_ctor_set(x_130, 5, x_87);
lean_ctor_set(x_130, 6, x_88);
lean_ctor_set(x_130, 7, x_89);
lean_ctor_set(x_130, 8, x_90);
lean_ctor_set(x_130, 9, x_91);
lean_ctor_set(x_130, 10, x_92);
lean_ctor_set(x_130, 11, x_93);
lean_ctor_set(x_130, 12, x_94);
lean_ctor_set(x_130, 13, x_95);
lean_ctor_set(x_130, 14, x_96);
lean_ctor_set(x_130, 15, x_97);
lean_ctor_set(x_130, 16, x_98);
lean_ctor_set(x_130, 17, x_99);
lean_ctor_set(x_130, 18, x_100);
lean_ctor_set(x_130, 19, x_101);
lean_ctor_set(x_130, 20, x_102);
lean_ctor_set(x_130, 21, x_103);
lean_ctor_set(x_130, 22, x_104);
lean_ctor_set(x_130, 23, x_105);
lean_ctor_set(x_130, 24, x_106);
lean_ctor_set(x_130, 25, x_107);
lean_ctor_set(x_130, 26, x_108);
lean_ctor_set(x_130, 27, x_109);
lean_ctor_set(x_130, 28, x_110);
lean_ctor_set(x_130, 29, x_111);
lean_ctor_set(x_130, 30, x_112);
lean_ctor_set(x_130, 31, x_113);
lean_ctor_set(x_130, 32, x_114);
lean_ctor_set(x_130, 33, x_129);
lean_ctor_set(x_130, 34, x_116);
lean_ctor_set(x_130, 35, x_117);
lean_ctor_set(x_130, 36, x_119);
lean_ctor_set(x_130, 37, x_120);
lean_ctor_set(x_130, 38, x_121);
lean_ctor_set(x_130, 39, x_122);
lean_ctor_set(x_130, 40, x_123);
lean_ctor_set(x_130, 41, x_124);
lean_ctor_set_uint8(x_130, sizeof(void*)*42, x_118);
x_131 = lean_array_fset(x_127, x_1, x_130);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_6);
lean_ctor_set(x_132, 2, x_7);
lean_ctor_set(x_132, 3, x_8);
lean_ctor_set(x_132, 4, x_9);
lean_ctor_set(x_132, 5, x_10);
lean_ctor_set(x_132, 6, x_11);
lean_ctor_set(x_132, 7, x_12);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_24, 32);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_30 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_29, x_26, x_3);
lean_ctor_set(x_24, 32, x_30);
x_31 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 2);
x_35 = lean_ctor_get(x_24, 3);
x_36 = lean_ctor_get(x_24, 4);
x_37 = lean_ctor_get(x_24, 5);
x_38 = lean_ctor_get(x_24, 6);
x_39 = lean_ctor_get(x_24, 7);
x_40 = lean_ctor_get(x_24, 8);
x_41 = lean_ctor_get(x_24, 9);
x_42 = lean_ctor_get(x_24, 10);
x_43 = lean_ctor_get(x_24, 11);
x_44 = lean_ctor_get(x_24, 12);
x_45 = lean_ctor_get(x_24, 13);
x_46 = lean_ctor_get(x_24, 14);
x_47 = lean_ctor_get(x_24, 15);
x_48 = lean_ctor_get(x_24, 16);
x_49 = lean_ctor_get(x_24, 17);
x_50 = lean_ctor_get(x_24, 18);
x_51 = lean_ctor_get(x_24, 19);
x_52 = lean_ctor_get(x_24, 20);
x_53 = lean_ctor_get(x_24, 21);
x_54 = lean_ctor_get(x_24, 22);
x_55 = lean_ctor_get(x_24, 23);
x_56 = lean_ctor_get(x_24, 24);
x_57 = lean_ctor_get(x_24, 25);
x_58 = lean_ctor_get(x_24, 26);
x_59 = lean_ctor_get(x_24, 27);
x_60 = lean_ctor_get(x_24, 28);
x_61 = lean_ctor_get(x_24, 29);
x_62 = lean_ctor_get(x_24, 30);
x_63 = lean_ctor_get(x_24, 31);
x_64 = lean_ctor_get(x_24, 32);
x_65 = lean_ctor_get(x_24, 33);
x_66 = lean_ctor_get(x_24, 34);
x_67 = lean_ctor_get(x_24, 35);
x_68 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_69 = lean_ctor_get(x_24, 36);
x_70 = lean_ctor_get(x_24, 37);
x_71 = lean_ctor_get(x_24, 38);
x_72 = lean_ctor_get(x_24, 39);
x_73 = lean_ctor_get(x_24, 40);
x_74 = lean_ctor_get(x_24, 41);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_75 = lean_box(0);
x_76 = lean_array_fset(x_5, x_1, x_75);
x_77 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_78 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_77, x_64, x_3);
x_79 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_33);
lean_ctor_set(x_79, 2, x_34);
lean_ctor_set(x_79, 3, x_35);
lean_ctor_set(x_79, 4, x_36);
lean_ctor_set(x_79, 5, x_37);
lean_ctor_set(x_79, 6, x_38);
lean_ctor_set(x_79, 7, x_39);
lean_ctor_set(x_79, 8, x_40);
lean_ctor_set(x_79, 9, x_41);
lean_ctor_set(x_79, 10, x_42);
lean_ctor_set(x_79, 11, x_43);
lean_ctor_set(x_79, 12, x_44);
lean_ctor_set(x_79, 13, x_45);
lean_ctor_set(x_79, 14, x_46);
lean_ctor_set(x_79, 15, x_47);
lean_ctor_set(x_79, 16, x_48);
lean_ctor_set(x_79, 17, x_49);
lean_ctor_set(x_79, 18, x_50);
lean_ctor_set(x_79, 19, x_51);
lean_ctor_set(x_79, 20, x_52);
lean_ctor_set(x_79, 21, x_53);
lean_ctor_set(x_79, 22, x_54);
lean_ctor_set(x_79, 23, x_55);
lean_ctor_set(x_79, 24, x_56);
lean_ctor_set(x_79, 25, x_57);
lean_ctor_set(x_79, 26, x_58);
lean_ctor_set(x_79, 27, x_59);
lean_ctor_set(x_79, 28, x_60);
lean_ctor_set(x_79, 29, x_61);
lean_ctor_set(x_79, 30, x_62);
lean_ctor_set(x_79, 31, x_63);
lean_ctor_set(x_79, 32, x_78);
lean_ctor_set(x_79, 33, x_65);
lean_ctor_set(x_79, 34, x_66);
lean_ctor_set(x_79, 35, x_67);
lean_ctor_set(x_79, 36, x_69);
lean_ctor_set(x_79, 37, x_70);
lean_ctor_set(x_79, 38, x_71);
lean_ctor_set(x_79, 39, x_72);
lean_ctor_set(x_79, 40, x_73);
lean_ctor_set(x_79, 41, x_74);
lean_ctor_set_uint8(x_79, sizeof(void*)*42, x_68);
x_80 = lean_array_fset(x_76, x_1, x_79);
lean_ctor_set(x_4, 0, x_80);
return x_4;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_4);
x_81 = lean_array_fget(x_5, x_1);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_81, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 4);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_81, 5);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 6);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 7);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 8);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 9);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 10);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 11);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 12);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 13);
lean_inc(x_95);
x_96 = lean_ctor_get(x_81, 14);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 15);
lean_inc(x_97);
x_98 = lean_ctor_get(x_81, 16);
lean_inc(x_98);
x_99 = lean_ctor_get(x_81, 17);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_81, 18);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_81, 19);
lean_inc(x_101);
x_102 = lean_ctor_get(x_81, 20);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 21);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 22);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_81, 23);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_81, 24);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_81, 25);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 26);
lean_inc(x_108);
x_109 = lean_ctor_get(x_81, 27);
lean_inc(x_109);
x_110 = lean_ctor_get(x_81, 28);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_81, 29);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_81, 30);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_81, 31);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_81, 32);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_81, 33);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_81, 34);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_81, 35);
lean_inc_ref(x_117);
x_118 = lean_ctor_get_uint8(x_81, sizeof(void*)*42);
x_119 = lean_ctor_get(x_81, 36);
lean_inc(x_119);
x_120 = lean_ctor_get(x_81, 37);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_81, 38);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_81, 39);
lean_inc(x_122);
x_123 = lean_ctor_get(x_81, 40);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_81, 41);
lean_inc_ref(x_124);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 lean_ctor_release(x_81, 6);
 lean_ctor_release(x_81, 7);
 lean_ctor_release(x_81, 8);
 lean_ctor_release(x_81, 9);
 lean_ctor_release(x_81, 10);
 lean_ctor_release(x_81, 11);
 lean_ctor_release(x_81, 12);
 lean_ctor_release(x_81, 13);
 lean_ctor_release(x_81, 14);
 lean_ctor_release(x_81, 15);
 lean_ctor_release(x_81, 16);
 lean_ctor_release(x_81, 17);
 lean_ctor_release(x_81, 18);
 lean_ctor_release(x_81, 19);
 lean_ctor_release(x_81, 20);
 lean_ctor_release(x_81, 21);
 lean_ctor_release(x_81, 22);
 lean_ctor_release(x_81, 23);
 lean_ctor_release(x_81, 24);
 lean_ctor_release(x_81, 25);
 lean_ctor_release(x_81, 26);
 lean_ctor_release(x_81, 27);
 lean_ctor_release(x_81, 28);
 lean_ctor_release(x_81, 29);
 lean_ctor_release(x_81, 30);
 lean_ctor_release(x_81, 31);
 lean_ctor_release(x_81, 32);
 lean_ctor_release(x_81, 33);
 lean_ctor_release(x_81, 34);
 lean_ctor_release(x_81, 35);
 lean_ctor_release(x_81, 36);
 lean_ctor_release(x_81, 37);
 lean_ctor_release(x_81, 38);
 lean_ctor_release(x_81, 39);
 lean_ctor_release(x_81, 40);
 lean_ctor_release(x_81, 41);
 x_125 = x_81;
} else {
 lean_dec_ref(x_81);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
x_127 = lean_array_fset(x_5, x_1, x_126);
x_128 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0;
x_129 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3(x_2, x_128, x_114, x_3);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 42, 1);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_82);
lean_ctor_set(x_130, 1, x_83);
lean_ctor_set(x_130, 2, x_84);
lean_ctor_set(x_130, 3, x_85);
lean_ctor_set(x_130, 4, x_86);
lean_ctor_set(x_130, 5, x_87);
lean_ctor_set(x_130, 6, x_88);
lean_ctor_set(x_130, 7, x_89);
lean_ctor_set(x_130, 8, x_90);
lean_ctor_set(x_130, 9, x_91);
lean_ctor_set(x_130, 10, x_92);
lean_ctor_set(x_130, 11, x_93);
lean_ctor_set(x_130, 12, x_94);
lean_ctor_set(x_130, 13, x_95);
lean_ctor_set(x_130, 14, x_96);
lean_ctor_set(x_130, 15, x_97);
lean_ctor_set(x_130, 16, x_98);
lean_ctor_set(x_130, 17, x_99);
lean_ctor_set(x_130, 18, x_100);
lean_ctor_set(x_130, 19, x_101);
lean_ctor_set(x_130, 20, x_102);
lean_ctor_set(x_130, 21, x_103);
lean_ctor_set(x_130, 22, x_104);
lean_ctor_set(x_130, 23, x_105);
lean_ctor_set(x_130, 24, x_106);
lean_ctor_set(x_130, 25, x_107);
lean_ctor_set(x_130, 26, x_108);
lean_ctor_set(x_130, 27, x_109);
lean_ctor_set(x_130, 28, x_110);
lean_ctor_set(x_130, 29, x_111);
lean_ctor_set(x_130, 30, x_112);
lean_ctor_set(x_130, 31, x_113);
lean_ctor_set(x_130, 32, x_129);
lean_ctor_set(x_130, 33, x_115);
lean_ctor_set(x_130, 34, x_116);
lean_ctor_set(x_130, 35, x_117);
lean_ctor_set(x_130, 36, x_119);
lean_ctor_set(x_130, 37, x_120);
lean_ctor_set(x_130, 38, x_121);
lean_ctor_set(x_130, 39, x_122);
lean_ctor_set(x_130, 40, x_123);
lean_ctor_set(x_130, 41, x_124);
lean_ctor_set_uint8(x_130, sizeof(void*)*42, x_118);
x_131 = lean_array_fset(x_127, x_1, x_130);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_6);
lean_ctor_set(x_132, 2, x_7);
lean_ctor_set(x_132, 3, x_8);
lean_ctor_set(x_132, 4, x_9);
lean_ctor_set(x_132, 5, x_10);
lean_ctor_set(x_132, 6, x_11);
lean_ctor_set(x_132, 7, x_12);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 21);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_free_object(x_13);
x_18 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1;
x_19 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 21);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1;
x_25 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_24, x_8, x_9, x_10, x_11);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 20);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_free_object(x_13);
x_18 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1;
x_19 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 20);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1;
x_25 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_24, x_8, x_9, x_10, x_11);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0;
x_16 = lean_int_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; uint8_t x_31; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_20, 30);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_18, 23);
lean_inc_ref(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_22, 2);
x_25 = l_Lean_mkIntLit(x_1);
x_30 = l_Lean_instInhabitedExpr;
x_31 = lean_nat_dec_lt(x_2, x_24);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_22);
x_32 = l_outOfBounds___redArg(x_30);
x_26 = x_32;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_PersistentArray_get_x21___redArg(x_30, x_22, x_2);
x_26 = x_33;
goto block_29;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_mkAppB(x_23, x_25, x_26);
if (lean_is_scalar(x_21)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_21;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_42, 30);
lean_inc_ref(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 2);
x_45 = l_Lean_instInhabitedExpr;
x_46 = lean_nat_dec_lt(x_2, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec_ref(x_43);
x_47 = l_outOfBounds___redArg(x_45);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_PersistentArray_get_x21___redArg(x_45, x_43, x_2);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_ctor_get(x_49, 30);
lean_inc_ref(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 2);
x_52 = l_Lean_instInhabitedExpr;
x_53 = lean_nat_dec_lt(x_2, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_50);
x_54 = l_outOfBounds___redArg(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_PersistentArray_get_x21___redArg(x_52, x_50, x_2);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_40, 0);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_20, 22);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = l_Lean_mkAppB(x_23, x_2, x_22);
x_1 = x_18;
x_2 = x_24;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 17);
lean_inc_ref(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 17);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__9(x_26, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
else
{
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_2 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 18);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = l_Lean_mkAppB(x_16, x_18, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 18);
lean_inc_ref(x_25);
lean_dec(x_24);
x_26 = l_Lean_mkAppB(x_16, x_18, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_dec(x_16);
return x_17;
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 18);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = l_Lean_mkAppB(x_32, x_34, x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_40, 18);
lean_inc_ref(x_41);
lean_dec(x_40);
x_42 = l_Lean_mkAppB(x_32, x_34, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_32);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_dec(x_32);
return x_33;
}
}
else
{
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__10));
x_151 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_150, x_11);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_10;
x_96 = x_11;
x_97 = x_12;
x_98 = lean_box(0);
goto block_149;
}
else
{
lean_object* x_154; 
x_154 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = l_Lean_MessageData_ofExpr(x_155);
x_157 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_150, x_156, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_157) == 0)
{
lean_dec_ref(x_157);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_10;
x_96 = x_11;
x_97 = x_12;
x_98 = lean_box(0);
goto block_149;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_158 = !lean_is_exclusive(x_154);
if (x_158 == 0)
{
return x_154;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
lean_dec(x_154);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(x_26, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_27;
}
block_60:
{
lean_object* x_42; 
x_42 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = 0;
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Lean_instBEqLBool_beq(x_46, x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_48 = lean_box(0);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; 
lean_free_object(x_42);
x_49 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_29, x_30, x_31);
lean_dec(x_31);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = 0;
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_53 = l_Lean_instBEqLBool_beq(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_29, x_30, x_31);
lean_dec(x_31);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_42, 0);
lean_inc(x_58);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
block_86:
{
lean_object* x_77; 
lean_inc(x_65);
x_77 = l_Lean_Grind_Linarith_Poly_updateOccs(x_63, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72, x_73, x_74, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_77);
x_78 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0;
x_79 = lean_int_dec_lt(x_62, x_78);
lean_dec(x_62);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc_ref(x_1);
lean_inc(x_65);
x_80 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(x_80, 0, x_65);
lean_closure_set(x_80, 1, x_1);
lean_closure_set(x_80, 2, x_61);
x_81 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_82 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_81, x_80, x_66);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
x_32 = x_67;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
x_38 = x_73;
x_39 = x_74;
x_40 = x_75;
x_41 = lean_box(0);
goto block_60;
}
else
{
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_1);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc_ref(x_1);
lean_inc(x_65);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__1___boxed), 4, 3);
lean_closure_set(x_83, 0, x_65);
lean_closure_set(x_83, 1, x_1);
lean_closure_set(x_83, 2, x_61);
x_84 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_85 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_84, x_83, x_66);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
x_32 = x_67;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
x_38 = x_73;
x_39 = x_74;
x_40 = x_75;
x_41 = lean_box(0);
goto block_60;
}
else
{
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_1);
return x_85;
}
}
}
else
{
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_1);
return x_77;
}
}
block_149:
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__5));
x_102 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_101, x_96);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
x_106 = lean_box(0);
lean_ctor_set(x_102, 0, x_106);
return x_102;
}
else
{
lean_object* x_107; 
lean_free_object(x_102);
x_107 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l_Lean_MessageData_ofExpr(x_108);
x_110 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_101, x_109, x_94, x_95, x_96, x_97);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
return x_110;
}
else
{
uint8_t x_111; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_102, 0);
lean_inc(x_114);
lean_dec(x_102);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_MessageData_ofExpr(x_119);
x_121 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_101, x_120, x_94, x_95, x_96, x_97);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__7));
x_126 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_125, x_96);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
x_14 = x_87;
x_15 = x_88;
x_16 = x_89;
x_17 = x_90;
x_18 = x_91;
x_19 = x_92;
x_20 = x_93;
x_21 = x_94;
x_22 = x_95;
x_23 = x_96;
x_24 = x_97;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_MessageData_ofExpr(x_130);
x_132 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_125, x_131, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_14 = x_87;
x_15 = x_88;
x_16 = x_89;
x_17 = x_90;
x_18 = x_91;
x_19 = x_92;
x_20 = x_93;
x_21 = x_94;
x_22 = x_95;
x_23 = x_96;
x_24 = x_97;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
return x_132;
}
}
else
{
uint8_t x_133; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_129);
if (x_133 == 0)
{
return x_129;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_136 = lean_ctor_get(x_99, 0);
x_137 = lean_ctor_get(x_99, 1);
x_138 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__9));
x_139 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__0___redArg(x_138, x_96);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_inc_ref(x_99);
lean_inc(x_136);
lean_inc_n(x_137, 2);
x_61 = x_137;
x_62 = x_136;
x_63 = x_99;
x_64 = x_137;
x_65 = x_87;
x_66 = x_88;
x_67 = x_89;
x_68 = x_90;
x_69 = x_91;
x_70 = x_92;
x_71 = x_93;
x_72 = x_94;
x_73 = x_95;
x_74 = x_96;
x_75 = x_97;
x_76 = lean_box(0);
goto block_86;
}
else
{
lean_object* x_142; 
x_142 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1(x_1, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_MessageData_ofExpr(x_143);
x_145 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_138, x_144, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_145) == 0)
{
lean_dec_ref(x_145);
lean_inc_ref(x_99);
lean_inc(x_136);
lean_inc_n(x_137, 2);
x_61 = x_137;
x_62 = x_136;
x_63 = x_99;
x_64 = x_137;
x_65 = x_87;
x_66 = x_88;
x_67 = x_89;
x_68 = x_90;
x_69 = x_91;
x_70 = x_92;
x_71 = x_93;
x_72 = x_94;
x_73 = x_95;
x_74 = x_96;
x_75 = x_97;
x_76 = lean_box(0);
goto block_86;
}
else
{
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
return x_145;
}
}
else
{
uint8_t x_146; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
x_146 = !lean_is_exclusive(x_142);
if (x_146 == 0)
{
return x_142;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg(x_1, x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__3_spec__5(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 41);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = l_Lean_PersistentArray_push___redArg(x_25, x_2);
lean_ctor_set(x_23, 41, x_28);
x_29 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
x_32 = lean_ctor_get(x_23, 2);
x_33 = lean_ctor_get(x_23, 3);
x_34 = lean_ctor_get(x_23, 4);
x_35 = lean_ctor_get(x_23, 5);
x_36 = lean_ctor_get(x_23, 6);
x_37 = lean_ctor_get(x_23, 7);
x_38 = lean_ctor_get(x_23, 8);
x_39 = lean_ctor_get(x_23, 9);
x_40 = lean_ctor_get(x_23, 10);
x_41 = lean_ctor_get(x_23, 11);
x_42 = lean_ctor_get(x_23, 12);
x_43 = lean_ctor_get(x_23, 13);
x_44 = lean_ctor_get(x_23, 14);
x_45 = lean_ctor_get(x_23, 15);
x_46 = lean_ctor_get(x_23, 16);
x_47 = lean_ctor_get(x_23, 17);
x_48 = lean_ctor_get(x_23, 18);
x_49 = lean_ctor_get(x_23, 19);
x_50 = lean_ctor_get(x_23, 20);
x_51 = lean_ctor_get(x_23, 21);
x_52 = lean_ctor_get(x_23, 22);
x_53 = lean_ctor_get(x_23, 23);
x_54 = lean_ctor_get(x_23, 24);
x_55 = lean_ctor_get(x_23, 25);
x_56 = lean_ctor_get(x_23, 26);
x_57 = lean_ctor_get(x_23, 27);
x_58 = lean_ctor_get(x_23, 28);
x_59 = lean_ctor_get(x_23, 29);
x_60 = lean_ctor_get(x_23, 30);
x_61 = lean_ctor_get(x_23, 31);
x_62 = lean_ctor_get(x_23, 32);
x_63 = lean_ctor_get(x_23, 33);
x_64 = lean_ctor_get(x_23, 34);
x_65 = lean_ctor_get(x_23, 35);
x_66 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_67 = lean_ctor_get(x_23, 36);
x_68 = lean_ctor_get(x_23, 37);
x_69 = lean_ctor_get(x_23, 38);
x_70 = lean_ctor_get(x_23, 39);
x_71 = lean_ctor_get(x_23, 40);
x_72 = lean_ctor_get(x_23, 41);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_73 = lean_box(0);
x_74 = lean_array_fset(x_4, x_1, x_73);
x_75 = l_Lean_PersistentArray_push___redArg(x_72, x_2);
x_76 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_31);
lean_ctor_set(x_76, 2, x_32);
lean_ctor_set(x_76, 3, x_33);
lean_ctor_set(x_76, 4, x_34);
lean_ctor_set(x_76, 5, x_35);
lean_ctor_set(x_76, 6, x_36);
lean_ctor_set(x_76, 7, x_37);
lean_ctor_set(x_76, 8, x_38);
lean_ctor_set(x_76, 9, x_39);
lean_ctor_set(x_76, 10, x_40);
lean_ctor_set(x_76, 11, x_41);
lean_ctor_set(x_76, 12, x_42);
lean_ctor_set(x_76, 13, x_43);
lean_ctor_set(x_76, 14, x_44);
lean_ctor_set(x_76, 15, x_45);
lean_ctor_set(x_76, 16, x_46);
lean_ctor_set(x_76, 17, x_47);
lean_ctor_set(x_76, 18, x_48);
lean_ctor_set(x_76, 19, x_49);
lean_ctor_set(x_76, 20, x_50);
lean_ctor_set(x_76, 21, x_51);
lean_ctor_set(x_76, 22, x_52);
lean_ctor_set(x_76, 23, x_53);
lean_ctor_set(x_76, 24, x_54);
lean_ctor_set(x_76, 25, x_55);
lean_ctor_set(x_76, 26, x_56);
lean_ctor_set(x_76, 27, x_57);
lean_ctor_set(x_76, 28, x_58);
lean_ctor_set(x_76, 29, x_59);
lean_ctor_set(x_76, 30, x_60);
lean_ctor_set(x_76, 31, x_61);
lean_ctor_set(x_76, 32, x_62);
lean_ctor_set(x_76, 33, x_63);
lean_ctor_set(x_76, 34, x_64);
lean_ctor_set(x_76, 35, x_65);
lean_ctor_set(x_76, 36, x_67);
lean_ctor_set(x_76, 37, x_68);
lean_ctor_set(x_76, 38, x_69);
lean_ctor_set(x_76, 39, x_70);
lean_ctor_set(x_76, 40, x_71);
lean_ctor_set(x_76, 41, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*42, x_66);
x_77 = lean_array_fset(x_74, x_1, x_76);
lean_ctor_set(x_3, 0, x_77);
return x_3;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
x_78 = lean_array_fget(x_4, x_1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 11);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 12);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 13);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 14);
lean_inc(x_93);
x_94 = lean_ctor_get(x_78, 15);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 16);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 17);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_78, 18);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_78, 19);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 20);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 21);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 22);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_78, 23);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_78, 24);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_78, 25);
lean_inc(x_104);
x_105 = lean_ctor_get(x_78, 26);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 27);
lean_inc(x_106);
x_107 = lean_ctor_get(x_78, 28);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_78, 29);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_78, 30);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_78, 31);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_78, 32);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_78, 33);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_78, 34);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_78, 35);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_78, sizeof(void*)*42);
x_116 = lean_ctor_get(x_78, 36);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 37);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_78, 38);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_78, 39);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 40);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_78, 41);
lean_inc_ref(x_121);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 lean_ctor_release(x_78, 9);
 lean_ctor_release(x_78, 10);
 lean_ctor_release(x_78, 11);
 lean_ctor_release(x_78, 12);
 lean_ctor_release(x_78, 13);
 lean_ctor_release(x_78, 14);
 lean_ctor_release(x_78, 15);
 lean_ctor_release(x_78, 16);
 lean_ctor_release(x_78, 17);
 lean_ctor_release(x_78, 18);
 lean_ctor_release(x_78, 19);
 lean_ctor_release(x_78, 20);
 lean_ctor_release(x_78, 21);
 lean_ctor_release(x_78, 22);
 lean_ctor_release(x_78, 23);
 lean_ctor_release(x_78, 24);
 lean_ctor_release(x_78, 25);
 lean_ctor_release(x_78, 26);
 lean_ctor_release(x_78, 27);
 lean_ctor_release(x_78, 28);
 lean_ctor_release(x_78, 29);
 lean_ctor_release(x_78, 30);
 lean_ctor_release(x_78, 31);
 lean_ctor_release(x_78, 32);
 lean_ctor_release(x_78, 33);
 lean_ctor_release(x_78, 34);
 lean_ctor_release(x_78, 35);
 lean_ctor_release(x_78, 36);
 lean_ctor_release(x_78, 37);
 lean_ctor_release(x_78, 38);
 lean_ctor_release(x_78, 39);
 lean_ctor_release(x_78, 40);
 lean_ctor_release(x_78, 41);
 x_122 = x_78;
} else {
 lean_dec_ref(x_78);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
x_124 = lean_array_fset(x_4, x_1, x_123);
x_125 = l_Lean_PersistentArray_push___redArg(x_121, x_2);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 42, 1);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_79);
lean_ctor_set(x_126, 1, x_80);
lean_ctor_set(x_126, 2, x_81);
lean_ctor_set(x_126, 3, x_82);
lean_ctor_set(x_126, 4, x_83);
lean_ctor_set(x_126, 5, x_84);
lean_ctor_set(x_126, 6, x_85);
lean_ctor_set(x_126, 7, x_86);
lean_ctor_set(x_126, 8, x_87);
lean_ctor_set(x_126, 9, x_88);
lean_ctor_set(x_126, 10, x_89);
lean_ctor_set(x_126, 11, x_90);
lean_ctor_set(x_126, 12, x_91);
lean_ctor_set(x_126, 13, x_92);
lean_ctor_set(x_126, 14, x_93);
lean_ctor_set(x_126, 15, x_94);
lean_ctor_set(x_126, 16, x_95);
lean_ctor_set(x_126, 17, x_96);
lean_ctor_set(x_126, 18, x_97);
lean_ctor_set(x_126, 19, x_98);
lean_ctor_set(x_126, 20, x_99);
lean_ctor_set(x_126, 21, x_100);
lean_ctor_set(x_126, 22, x_101);
lean_ctor_set(x_126, 23, x_102);
lean_ctor_set(x_126, 24, x_103);
lean_ctor_set(x_126, 25, x_104);
lean_ctor_set(x_126, 26, x_105);
lean_ctor_set(x_126, 27, x_106);
lean_ctor_set(x_126, 28, x_107);
lean_ctor_set(x_126, 29, x_108);
lean_ctor_set(x_126, 30, x_109);
lean_ctor_set(x_126, 31, x_110);
lean_ctor_set(x_126, 32, x_111);
lean_ctor_set(x_126, 33, x_112);
lean_ctor_set(x_126, 34, x_113);
lean_ctor_set(x_126, 35, x_114);
lean_ctor_set(x_126, 36, x_116);
lean_ctor_set(x_126, 37, x_117);
lean_ctor_set(x_126, 38, x_118);
lean_ctor_set(x_126, 39, x_119);
lean_ctor_set(x_126, 40, x_120);
lean_ctor_set(x_126, 41, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*42, x_115);
x_127 = lean_array_fset(x_124, x_1, x_126);
x_128 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_5);
lean_ctor_set(x_128, 2, x_6);
lean_ctor_set(x_128, 3, x_7);
lean_ctor_set(x_128, 4, x_8);
lean_ctor_set(x_128, 5, x_9);
lean_ctor_set(x_128, 6, x_10);
lean_ctor_set(x_128, 7, x_11);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_19);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_box(x_18);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(x_27, 0, x_3);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_19);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_7);
if (lean_obj_tag(x_32) == 0)
{
if (x_5 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_37, 0, x_6);
lean_closure_set(x_37, 1, x_1);
x_38 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_39 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_38, x_37, x_7);
lean_dec(x_7);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_inc(x_25);
lean_inc(x_31);
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_25);
x_41 = l_Lean_Grind_CommRing_Expr_toPoly(x_40);
if (x_4 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_35);
lean_dec(x_35);
x_42 = x_77;
goto block_76;
}
else
{
lean_dec(x_35);
x_42 = x_5;
goto block_76;
}
block_76:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_31);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_42);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_33);
lean_inc_ref(x_47);
x_48 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_47, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_49, x_18, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_53);
x_54 = l_Lean_Grind_Linarith_Expr_norm(x_53);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_42);
x_57 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_58 = lean_box(0);
lean_ctor_set(x_50, 0, x_58);
return x_50;
}
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_50, 0);
lean_inc(x_59);
lean_dec(x_50);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc(x_60);
x_61 = l_Lean_Grind_Linarith_Expr_norm(x_60);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_42);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_46);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_50);
if (x_67 == 0)
{
return x_50;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_50, 0);
lean_inc(x_68);
lean_dec(x_50);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_46);
lean_dec(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
return x_48;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_48, 0);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
return x_45;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_45, 0);
lean_inc(x_74);
lean_dec(x_45);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_34, 0);
lean_inc(x_79);
lean_dec(x_34);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_32, 0);
lean_inc(x_81);
lean_dec_ref(x_32);
lean_inc(x_31);
lean_inc(x_25);
x_82 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_82, 0, x_25);
lean_ctor_set(x_82, 1, x_31);
x_83 = l_Lean_Grind_CommRing_Expr_toPoly(x_82);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_25);
lean_ctor_set(x_84, 2, x_31);
x_85 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_4);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_86 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_85, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_81);
lean_inc_ref(x_88);
x_89 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_88, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_91 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_90, x_18, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
lean_inc(x_94);
x_95 = l_Lean_Grind_Linarith_Expr_norm(x_94);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_4);
x_98 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_97, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_98;
}
else
{
lean_object* x_99; 
lean_dec(x_93);
lean_dec(x_87);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_99 = lean_box(0);
lean_ctor_set(x_91, 0, x_99);
return x_91;
}
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
lean_dec(x_91);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_101);
x_102 = l_Lean_Grind_Linarith_Expr_norm(x_101);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_4);
x_105 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_104, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_100);
lean_dec(x_87);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_87);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_108 = !lean_is_exclusive(x_91);
if (x_108 == 0)
{
return x_91;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_91, 0);
lean_inc(x_109);
lean_dec(x_91);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_87);
lean_dec(x_81);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_111 = !lean_is_exclusive(x_89);
if (x_111 == 0)
{
return x_89;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_89, 0);
lean_inc(x_112);
lean_dec(x_89);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_81);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_114 = !lean_is_exclusive(x_86);
if (x_114 == 0)
{
return x_86;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_86, 0);
lean_inc(x_115);
lean_dec(x_86);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_117 = !lean_is_exclusive(x_32);
if (x_117 == 0)
{
return x_32;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_32, 0);
lean_inc(x_118);
lean_dec(x_32);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_120 = lean_box(0);
lean_ctor_set(x_28, 0, x_120);
return x_28;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_28, 0);
lean_inc(x_121);
lean_dec(x_28);
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_7);
if (lean_obj_tag(x_123) == 0)
{
if (x_5 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_unbox(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_128 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_128, 0, x_6);
lean_closure_set(x_128, 1, x_1);
x_129 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_130 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_129, x_128, x_7);
lean_dec(x_7);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_inc(x_25);
lean_inc(x_122);
x_131 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_25);
x_132 = l_Lean_Grind_CommRing_Expr_toPoly(x_131);
if (x_4 == 0)
{
uint8_t x_161; 
x_161 = lean_unbox(x_126);
lean_dec(x_126);
x_133 = x_161;
goto block_160;
}
else
{
lean_dec(x_126);
x_133 = x_5;
goto block_160;
}
block_160:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_25);
lean_ctor_set(x_134, 2, x_122);
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_136 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_135, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_124);
lean_inc_ref(x_138);
x_139 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_138, x_124, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_141 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_140, x_18, x_124, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_obj_tag(x_142) == 1)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec_ref(x_142);
lean_inc(x_144);
x_145 = l_Lean_Grind_Linarith_Expr_norm(x_144);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_133);
x_148 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_147, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_142);
lean_dec(x_137);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_149 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_143;
}
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_137);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_152 = x_141;
} else {
 lean_dec_ref(x_141);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_137);
lean_dec(x_124);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_155 = x_139;
} else {
 lean_dec_ref(x_139);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_124);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_157 = lean_ctor_get(x_136, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_158 = x_136;
} else {
 lean_dec_ref(x_136);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_125, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_163 = x_125;
} else {
 lean_dec_ref(x_125);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
lean_dec_ref(x_123);
lean_inc(x_122);
lean_inc(x_25);
x_166 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_166, 0, x_25);
lean_ctor_set(x_166, 1, x_122);
x_167 = l_Lean_Grind_CommRing_Expr_toPoly(x_166);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_25);
lean_ctor_set(x_168, 2, x_122);
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_4);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_170 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_169, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_165);
lean_inc_ref(x_172);
x_173 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_172, x_165, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_175 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_174, x_18, x_165, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_obj_tag(x_176) == 1)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_177);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec_ref(x_176);
lean_inc(x_178);
x_179 = l_Lean_Grind_Linarith_Expr_norm(x_178);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_171);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_4);
x_182 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_181, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_183 = lean_box(0);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_171);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_185 = lean_ctor_get(x_175, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_186 = x_175;
} else {
 lean_dec_ref(x_175);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_188 = lean_ctor_get(x_173, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_189 = x_173;
} else {
 lean_dec_ref(x_173);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_165);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_191 = lean_ctor_get(x_170, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_192 = x_170;
} else {
 lean_dec_ref(x_170);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_122);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_123, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_195 = x_123;
} else {
 lean_dec_ref(x_123);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_121);
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_199 = !lean_is_exclusive(x_28);
if (x_199 == 0)
{
return x_28;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_28, 0);
lean_inc(x_200);
lean_dec(x_28);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_202 = lean_box(0);
lean_ctor_set(x_22, 0, x_202);
return x_22;
}
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_22, 0);
lean_inc(x_203);
lean_dec(x_22);
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_box(x_18);
x_206 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(x_206, 0, x_3);
lean_closure_set(x_206, 1, x_205);
lean_closure_set(x_206, 2, x_19);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_207 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_206, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_209);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec_ref(x_208);
x_211 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_7);
if (lean_obj_tag(x_211) == 0)
{
if (x_5 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = lean_unbox(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_204);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_216 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_216, 0, x_6);
lean_closure_set(x_216, 1, x_1);
x_217 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_218 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_217, x_216, x_7);
lean_dec(x_7);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_inc(x_204);
lean_inc(x_210);
x_219 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set(x_219, 1, x_204);
x_220 = l_Lean_Grind_CommRing_Expr_toPoly(x_219);
if (x_4 == 0)
{
uint8_t x_249; 
x_249 = lean_unbox(x_214);
lean_dec(x_214);
x_221 = x_249;
goto block_248;
}
else
{
lean_dec(x_214);
x_221 = x_5;
goto block_248;
}
block_248:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_1);
lean_ctor_set(x_222, 1, x_204);
lean_ctor_set(x_222, 2, x_210);
x_223 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*2, x_221);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_224 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_223, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_212);
lean_inc_ref(x_226);
x_227 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_226, x_212, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_229 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_228, x_18, x_212, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_obj_tag(x_230) == 1)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_231);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec_ref(x_230);
lean_inc(x_232);
x_233 = l_Lean_Grind_Linarith_Expr_norm(x_232);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_225);
lean_ctor_set(x_234, 1, x_232);
x_235 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set_uint8(x_235, sizeof(void*)*2, x_221);
x_236 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_235, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_230);
lean_dec(x_225);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_237 = lean_box(0);
if (lean_is_scalar(x_231)) {
 x_238 = lean_alloc_ctor(0, 1, 0);
} else {
 x_238 = x_231;
}
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_225);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_239 = lean_ctor_get(x_229, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_240 = x_229;
} else {
 lean_dec_ref(x_229);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_225);
lean_dec(x_212);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_242 = lean_ctor_get(x_227, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_243 = x_227;
} else {
 lean_dec_ref(x_227);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_212);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_245 = lean_ctor_get(x_224, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_246 = x_224;
} else {
 lean_dec_ref(x_224);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_204);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_213, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_251 = x_213;
} else {
 lean_dec_ref(x_213);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_253 = lean_ctor_get(x_211, 0);
lean_inc(x_253);
lean_dec_ref(x_211);
lean_inc(x_210);
lean_inc(x_204);
x_254 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_254, 0, x_204);
lean_ctor_set(x_254, 1, x_210);
x_255 = l_Lean_Grind_CommRing_Expr_toPoly(x_254);
x_256 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_256, 0, x_1);
lean_ctor_set(x_256, 1, x_204);
lean_ctor_set(x_256, 2, x_210);
x_257 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set_uint8(x_257, sizeof(void*)*2, x_4);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_258 = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(x_257, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_253);
lean_inc_ref(x_260);
x_261 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_260, x_253, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_263 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_262, x_18, x_253, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
if (lean_obj_tag(x_264) == 1)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_265);
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
lean_dec_ref(x_264);
lean_inc(x_266);
x_267 = l_Lean_Grind_Linarith_Expr_norm(x_266);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_259);
lean_ctor_set(x_268, 1, x_266);
x_269 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_4);
x_270 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_269, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_264);
lean_dec(x_259);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_271 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 1, 0);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_259);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_273 = lean_ctor_get(x_263, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_274 = x_263;
} else {
 lean_dec_ref(x_263);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_259);
lean_dec(x_253);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_276 = lean_ctor_get(x_261, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_277 = x_261;
} else {
 lean_dec_ref(x_261);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_253);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_279 = lean_ctor_get(x_258, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_280 = x_258;
} else {
 lean_dec_ref(x_258);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_210);
lean_dec(x_204);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_282 = lean_ctor_get(x_211, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_283 = x_211;
} else {
 lean_dec_ref(x_211);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_208);
lean_dec(x_204);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_285 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_209;
}
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_204);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_207, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_288 = x_207;
} else {
 lean_dec_ref(x_207);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_203);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_22);
if (x_292 == 0)
{
return x_22;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_22, 0);
lean_inc(x_293);
lean_dec(x_22);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_20, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_3, x_20, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_29) == 1)
{
lean_free_object(x_27);
if (x_5 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_34, 0, x_6);
lean_closure_set(x_34, 1, x_1);
x_35 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_36 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_35, x_34, x_7);
lean_dec(x_7);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_24);
lean_inc(x_30);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_24);
x_38 = l_Lean_Grind_Linarith_Expr_norm(x_37);
if (x_4 == 0)
{
uint8_t x_44; 
x_44 = lean_unbox(x_32);
lean_dec(x_32);
x_39 = x_44;
goto block_43;
}
else
{
lean_dec(x_32);
x_39 = x_5;
goto block_43;
}
block_43:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 2, x_30);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_39);
x_42 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_42;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec_ref(x_29);
lean_inc(x_48);
lean_inc(x_24);
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Grind_Linarith_Expr_norm(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_24);
lean_ctor_set(x_51, 2, x_48);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_4);
x_53 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_54 = lean_box(0);
lean_ctor_set(x_27, 0, x_54);
return x_27;
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
lean_dec(x_27);
if (lean_obj_tag(x_55) == 1)
{
if (x_5 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_60, 0, x_6);
lean_closure_set(x_60, 1, x_1);
x_61 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_62 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_61, x_60, x_7);
lean_dec(x_7);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_inc(x_24);
lean_inc(x_56);
x_63 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_24);
x_64 = l_Lean_Grind_Linarith_Expr_norm(x_63);
if (x_4 == 0)
{
uint8_t x_70; 
x_70 = lean_unbox(x_58);
lean_dec(x_58);
x_65 = x_70;
goto block_69;
}
else
{
lean_dec(x_58);
x_65 = x_5;
goto block_69;
}
block_69:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_24);
lean_ctor_set(x_66, 2, x_56);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_65);
x_68 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_67, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_68;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_56);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
lean_dec_ref(x_55);
lean_inc(x_74);
lean_inc(x_24);
x_75 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_75, 0, x_24);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Grind_Linarith_Expr_norm(x_75);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_24);
lean_ctor_set(x_77, 2, x_74);
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_4);
x_79 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_78, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_55);
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_27);
if (x_82 == 0)
{
return x_27;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_27, 0);
lean_inc(x_83);
lean_dec(x_27);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_25);
if (x_85 == 0)
{
return x_25;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_25, 0);
lean_inc(x_86);
lean_dec(x_25);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_88 = lean_box(0);
lean_ctor_set(x_21, 0, x_88);
return x_21;
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_21, 0);
lean_inc(x_89);
lean_dec(x_21);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_3, x_20, x_92, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_obj_tag(x_94) == 1)
{
lean_dec(x_95);
if (x_5 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_unbox(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq___lam__0___boxed), 3, 2);
lean_closure_set(x_100, 0, x_6);
lean_closure_set(x_100, 1, x_1);
x_101 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_102 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_101, x_100, x_7);
lean_dec(x_7);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_inc(x_90);
lean_inc(x_96);
x_103 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_90);
x_104 = l_Lean_Grind_Linarith_Expr_norm(x_103);
if (x_4 == 0)
{
uint8_t x_110; 
x_110 = lean_unbox(x_98);
lean_dec(x_98);
x_105 = x_110;
goto block_109;
}
else
{
lean_dec(x_98);
x_105 = x_5;
goto block_109;
}
block_109:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_106, 2, x_96);
x_107 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_105);
x_108 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_107, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_108;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_112 = x_97;
} else {
 lean_dec_ref(x_97);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
lean_dec_ref(x_94);
lean_inc(x_114);
lean_inc(x_90);
x_115 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Grind_Linarith_Expr_norm(x_115);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_90);
lean_ctor_set(x_117, 2, x_114);
x_118 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_4);
x_119 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_118, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_94);
lean_dec(x_90);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_120 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_95;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_93, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_123 = x_93;
} else {
 lean_dec_ref(x_93);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_91, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_126 = x_91;
} else {
 lean_dec_ref(x_91);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_89);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_21);
if (x_130 == 0)
{
return x_21;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_21, 0);
lean_inc(x_131);
lean_dec(x_21);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_18);
if (x_133 == 0)
{
return x_18;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_18, 0);
lean_inc(x_134);
lean_dec(x_18);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_20 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_3);
x_23 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_7);
lean_dec_ref(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_22, x_32, x_29, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
lean_dec_ref(x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
x_39 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_26, x_32, x_38, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 1)
{
lean_free_object(x_39);
if (x_5 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_36);
lean_inc(x_42);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_36);
lean_ctor_set(x_24, 0, x_42);
x_43 = l_Lean_Grind_Linarith_Expr_norm(x_24);
if (x_4 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_44 = x_49;
goto block_48;
}
else
{
x_44 = x_5;
goto block_48;
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_30);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_42);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
x_47 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_46, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_47;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec_ref(x_41);
lean_inc(x_50);
lean_inc(x_36);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_50);
lean_ctor_set(x_24, 0, x_36);
x_51 = l_Lean_Grind_Linarith_Expr_norm(x_24);
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_30);
lean_ctor_set(x_52, 2, x_36);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_4);
x_54 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_53, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_39, 0, x_55);
return x_39;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
lean_dec(x_39);
if (lean_obj_tag(x_56) == 1)
{
if (x_5 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_36);
lean_inc(x_57);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_36);
lean_ctor_set(x_24, 0, x_57);
x_58 = l_Lean_Grind_Linarith_Expr_norm(x_24);
if (x_4 == 0)
{
uint8_t x_64; 
x_64 = 1;
x_59 = x_64;
goto block_63;
}
else
{
x_59 = x_5;
goto block_63;
}
block_63:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_30);
lean_ctor_set(x_60, 2, x_36);
lean_ctor_set(x_60, 3, x_57);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_59);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_61, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_62;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec_ref(x_56);
lean_inc(x_65);
lean_inc(x_36);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_65);
lean_ctor_set(x_24, 0, x_36);
x_66 = l_Lean_Grind_Linarith_Expr_norm(x_24);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_30);
lean_ctor_set(x_67, 2, x_36);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_4);
x_69 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_68, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_39);
if (x_72 == 0)
{
return x_39;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_39, 0);
lean_inc(x_73);
lean_dec(x_39);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_37);
if (x_75 == 0)
{
return x_37;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_37, 0);
lean_inc(x_76);
lean_dec(x_37);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_78 = lean_box(0);
lean_ctor_set(x_33, 0, x_78);
return x_33;
}
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_33, 0);
lean_inc(x_79);
lean_dec(x_33);
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
lean_dec_ref(x_3);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
x_83 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_26, x_32, x_82, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_obj_tag(x_84) == 1)
{
lean_dec(x_85);
if (x_5 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec_ref(x_84);
lean_inc(x_80);
lean_inc(x_86);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_80);
lean_ctor_set(x_24, 0, x_86);
x_87 = l_Lean_Grind_Linarith_Expr_norm(x_24);
if (x_4 == 0)
{
uint8_t x_93; 
x_93 = 1;
x_88 = x_93;
goto block_92;
}
else
{
x_88 = x_5;
goto block_92;
}
block_92:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_30);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set(x_89, 3, x_86);
x_90 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_88);
x_91 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_90, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_91;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
lean_dec_ref(x_84);
lean_inc(x_94);
lean_inc(x_80);
lean_ctor_set_tag(x_24, 3);
lean_ctor_set(x_24, 1, x_94);
lean_ctor_set(x_24, 0, x_80);
x_95 = l_Lean_Grind_Linarith_Expr_norm(x_24);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_30);
lean_ctor_set(x_96, 2, x_80);
lean_ctor_set(x_96, 3, x_94);
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_4);
x_98 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_97, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_99 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_85;
}
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_80);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_83, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_102 = x_83;
} else {
 lean_dec_ref(x_83);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_80);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_81, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
return x_33;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_33, 0);
lean_inc(x_110);
lean_dec(x_33);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_28);
if (x_112 == 0)
{
return x_28;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_28, 0);
lean_inc(x_113);
lean_dec(x_28);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_24, 0);
lean_inc(x_115);
lean_dec(x_24);
x_116 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_7);
lean_dec_ref(x_2);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_ctor_get(x_19, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_19, 1);
lean_inc(x_119);
lean_dec(x_19);
x_120 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_119);
x_121 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_22, x_120, x_117, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_123);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
lean_dec_ref(x_3);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_119);
x_127 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_115, x_120, x_126, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_obj_tag(x_128) == 1)
{
lean_dec(x_129);
if (x_5 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec_ref(x_128);
lean_inc(x_124);
lean_inc(x_130);
x_131 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_124);
x_132 = l_Lean_Grind_Linarith_Expr_norm(x_131);
if (x_4 == 0)
{
uint8_t x_138; 
x_138 = 1;
x_133 = x_138;
goto block_137;
}
else
{
x_133 = x_5;
goto block_137;
}
block_137:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_118);
lean_ctor_set(x_134, 2, x_124);
lean_ctor_set(x_134, 3, x_130);
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
x_136 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_135, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_136;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
lean_dec_ref(x_128);
lean_inc(x_139);
lean_inc(x_124);
x_140 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_140, 0, x_124);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_Grind_Linarith_Expr_norm(x_140);
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_118);
lean_ctor_set(x_142, 2, x_124);
lean_ctor_set(x_142, 3, x_139);
x_143 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_4);
x_144 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_143, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_145 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_146 = lean_alloc_ctor(0, 1, 0);
} else {
 x_146 = x_129;
}
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_127, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_148 = x_127;
} else {
 lean_dec_ref(x_127);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_151 = x_125;
} else {
 lean_dec_ref(x_125);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_153 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_154 = lean_alloc_ctor(0, 1, 0);
} else {
 x_154 = x_123;
}
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_121, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_156 = x_121;
} else {
 lean_dec_ref(x_121);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_115);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_116, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_159 = x_116;
} else {
 lean_dec_ref(x_116);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_161 = !lean_is_exclusive(x_23);
if (x_161 == 0)
{
return x_23;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_23, 0);
lean_inc(x_162);
lean_dec(x_23);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_20);
if (x_164 == 0)
{
return x_20;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_20, 0);
lean_inc(x_165);
lean_dec(x_20);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_18);
if (x_167 == 0)
{
return x_18;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_18, 0);
lean_inc(x_168);
lean_dec(x_18);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_expr_eqv(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 21);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Expr_getAppNumArgs(x_1);
x_21 = lean_unsigned_to_nat(4u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_23 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_16;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_20, x_25);
lean_inc(x_26);
x_27 = l_Lean_Expr_getRevArg_x21(x_1, x_26);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_28 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_nat_sub(x_26, x_25);
lean_dec(x_26);
x_32 = l_Lean_Expr_getRevArg_x21(x_1, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_sub(x_20, x_33);
x_35 = lean_nat_sub(x_34, x_25);
lean_dec(x_34);
x_36 = l_Lean_Expr_getRevArg_x21(x_1, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_sub(x_20, x_37);
lean_dec(x_20);
x_39 = lean_nat_sub(x_38, x_25);
lean_dec(x_38);
x_40 = l_Lean_Expr_getRevArg_x21(x_1, x_39);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_30);
lean_dec_ref(x_27);
lean_dec(x_16);
x_63 = lean_ctor_get(x_29, 0);
lean_inc(x_63);
lean_dec_ref(x_29);
x_64 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_66, 20);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 21);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(x_67, x_32);
lean_dec(x_67);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(x_68, x_32);
lean_dec_ref(x_32);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_63);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_71 = lean_box(0);
lean_ctor_set(x_64, 0, x_71);
return x_64;
}
else
{
lean_free_object(x_64);
x_41 = x_22;
x_42 = x_63;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_72; 
lean_dec(x_68);
lean_free_object(x_64);
lean_dec_ref(x_32);
x_72 = 0;
x_41 = x_72;
x_42 = x_63;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = lean_box(0);
goto block_62;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
lean_dec(x_64);
x_74 = lean_ctor_get(x_73, 20);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 21);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(x_74, x_32);
lean_dec(x_74);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_isInstOf(x_75, x_32);
lean_dec_ref(x_32);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_63);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
x_41 = x_22;
x_42 = x_63;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_80; 
lean_dec(x_75);
lean_dec_ref(x_32);
x_80 = 0;
x_41 = x_80;
x_42 = x_63;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = lean_box(0);
goto block_62;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_63);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_64);
if (x_81 == 0)
{
return x_64;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_64, 0);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_29);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_obj_tag(x_85) == 1)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_152; uint8_t x_159; uint8_t x_161; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_95 = lean_ctor_get(x_90, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 6);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 7);
lean_inc(x_97);
x_98 = lean_ctor_get(x_90, 8);
lean_inc(x_98);
x_99 = lean_ctor_get(x_90, 9);
lean_inc(x_99);
x_100 = lean_ctor_get(x_90, 10);
lean_inc(x_100);
lean_dec(x_90);
if (lean_obj_tag(x_95) == 0)
{
if (x_22 == 0)
{
x_161 = x_22;
goto block_162;
}
else
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_94;
}
}
else
{
uint8_t x_163; 
x_163 = 0;
x_161 = x_163;
goto block_162;
}
block_94:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
block_119:
{
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_100);
lean_dec(x_86);
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(x_1, x_36, x_40, x_102, x_2, x_106, x_105, x_104, x_101, x_108, x_109, x_111, x_113, x_107, x_112, x_103);
return x_115;
}
else
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_1);
x_116 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_86;
}
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec_ref(x_100);
lean_dec(x_86);
x_118 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateNatModuleIneq(x_1, x_36, x_40, x_102, x_2, x_106, x_105, x_104, x_101, x_108, x_109, x_111, x_113, x_107, x_112, x_103);
return x_118;
}
}
}
block_134:
{
if (x_2 == 0)
{
x_101 = x_120;
x_102 = x_121;
x_103 = x_122;
x_104 = x_123;
x_105 = x_124;
x_106 = x_125;
x_107 = x_126;
x_108 = x_127;
x_109 = x_128;
x_110 = lean_box(0);
x_111 = x_130;
x_112 = x_131;
x_113 = x_132;
x_114 = x_22;
goto block_119;
}
else
{
x_101 = x_120;
x_102 = x_121;
x_103 = x_122;
x_104 = x_123;
x_105 = x_124;
x_106 = x_125;
x_107 = x_126;
x_108 = x_127;
x_109 = x_128;
x_110 = lean_box(0);
x_111 = x_130;
x_112 = x_131;
x_113 = x_132;
x_114 = x_133;
goto block_119;
}
}
block_151:
{
if (x_136 == 0)
{
lean_dec(x_97);
lean_dec(x_30);
x_120 = x_140;
x_121 = x_136;
x_122 = x_147;
x_123 = x_139;
x_124 = x_138;
x_125 = x_137;
x_126 = x_145;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
x_130 = x_143;
x_131 = x_146;
x_132 = x_144;
x_133 = x_136;
goto block_134;
}
else
{
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_100);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_1);
x_149 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_30;
}
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
else
{
lean_dec_ref(x_97);
lean_dec(x_30);
x_120 = x_140;
x_121 = x_136;
x_122 = x_147;
x_123 = x_139;
x_124 = x_138;
x_125 = x_137;
x_126 = x_145;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
x_130 = x_143;
x_131 = x_146;
x_132 = x_144;
x_133 = x_135;
goto block_134;
}
}
}
block_158:
{
lean_object* x_153; uint8_t x_154; 
if (lean_is_scalar(x_88)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_88;
}
lean_ctor_set(x_153, 0, x_32);
x_154 = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(x_153, x_95);
lean_dec(x_95);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(x_153, x_96);
lean_dec(x_96);
lean_dec_ref(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_156 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_16;
}
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
else
{
lean_dec(x_16);
x_135 = x_152;
x_136 = x_22;
x_137 = x_87;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
x_146 = x_11;
x_147 = x_12;
x_148 = lean_box(0);
goto block_151;
}
}
else
{
lean_dec_ref(x_153);
lean_dec(x_96);
lean_dec(x_16);
x_135 = x_152;
x_136 = x_152;
x_137 = x_87;
x_138 = x_3;
x_139 = x_4;
x_140 = x_5;
x_141 = x_6;
x_142 = x_7;
x_143 = x_8;
x_144 = x_9;
x_145 = x_10;
x_146 = x_11;
x_147 = x_12;
x_148 = lean_box(0);
goto block_151;
}
}
block_160:
{
if (lean_obj_tag(x_99) == 0)
{
if (x_22 == 0)
{
lean_dec(x_91);
x_152 = x_22;
goto block_158;
}
else
{
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_94;
}
}
else
{
lean_dec_ref(x_99);
lean_dec(x_91);
x_152 = x_159;
goto block_158;
}
}
block_162:
{
if (lean_obj_tag(x_98) == 0)
{
if (x_22 == 0)
{
x_159 = x_22;
goto block_160;
}
else
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_94;
}
}
else
{
lean_dec_ref(x_98);
x_159 = x_161;
goto block_160;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_89);
if (x_164 == 0)
{
return x_89;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_89, 0);
lean_inc(x_165);
lean_dec(x_89);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_85);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_167 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_168 = lean_alloc_ctor(0, 1, 0);
} else {
 x_168 = x_86;
}
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_84);
if (x_169 == 0)
{
return x_84;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_84, 0);
lean_inc(x_170);
lean_dec(x_84);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
block_62:
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateIntModuleIneq(x_1, x_36, x_40, x_41, x_2, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr_0__Lean_Meta_Grind_Arith_Linear_propagateCommRingIneq(x_1, x_36, x_40, x_41, x_2, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_172 = !lean_is_exclusive(x_28);
if (x_172 == 0)
{
return x_28;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_28, 0);
lean_inc(x_173);
lean_dec(x_28);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_175 = !lean_is_exclusive(x_14);
if (x_175 == 0)
{
return x_14;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_14, 0);
lean_inc(x_176);
lean_dec(x_14);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
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
l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___lam__0___closed__0);
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__2___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__4___closed__1);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert_spec__1_spec__1_spec__3_spec__8___closed__0);
l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
