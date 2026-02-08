// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Lookahead
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Split import Lean.Meta.Tactic.Grind.EMatchAction
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations;
lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0;
lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_assertAll___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value;
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_instantiate___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value;
lean_object* l_Lean_Meta_Grind_Solvers_mkAction();
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "of_lookahead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 178, 46, 74, 114, 9, 243, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 159, 125, 127, 17, 128, 107, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value),LEAN_SCALAR_PTR_LITERAL(132, 37, 244, 19, 72, 39, 101, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(10000u);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_box(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___boxed), 15, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0;
x_16 = l_Lean_Meta_Grind_Action_orElse(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Action_orElse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(10000u);
x_16 = l_Lean_Meta_Grind_Action_loop___redArg(x_15, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0));
x_16 = l_Lean_Meta_Grind_Action_andThen(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Action_andThen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Solvers_mkAction();
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1));
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed), 15, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed), 14, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed), 14, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed), 15, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
lean_inc_ref(x_1);
x_21 = l_Lean_Meta_Grind_Action_run(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_21;
}
else
{
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_1);
return x_21;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_32);
lean_dec_ref(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_1);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_10, 5);
lean_inc(x_47);
lean_dec_ref(x_10);
x_48 = lean_io_error_to_string(x_46);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_13, 0, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_ctor_get(x_10, 5);
lean_inc(x_53);
lean_dec_ref(x_10);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_2);
x_10 = lean_st_ref_set(x_1, x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
x_17 = lean_st_ref_set(x_1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_st_ref_get(x_9);
x_14 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec(x_14);
lean_inc(x_9);
x_17 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_ctor_set_tag(x_17, 1);
x_20 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(x_9, x_15, x_16, x_17);
lean_dec_ref(x_17);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(x_9, x_15, x_16, x_25);
lean_dec_ref(x_25);
lean_dec(x_9);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_27 = x_26;
} else {
 lean_dec_ref(x_26);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(x_9, x_15, x_16, x_30);
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; 
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_getTag(x_1, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_2);
x_19 = l_Lean_mkNot(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
x_20 = l_Lean_mkArrow(x_19, x_18, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_10);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_21, x_16, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_3, 8);
lean_dec(x_27);
x_28 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0;
lean_ctor_set(x_3, 8, x_28);
x_29 = l_Lean_Expr_mvarId_x21(x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_11);
x_31 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(x_30, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_free_object(x_31);
x_34 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(x_23, x_11);
lean_dec(x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec_ref(x_33);
lean_dec(x_23);
lean_dec(x_11);
x_41 = lean_box(0);
lean_ctor_set(x_31, 0, x_41);
return x_31;
}
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(x_23, x_11);
lean_dec(x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_42);
lean_dec(x_23);
lean_dec(x_11);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
x_55 = lean_ctor_get(x_3, 2);
x_56 = lean_ctor_get(x_3, 3);
x_57 = lean_ctor_get(x_3, 4);
x_58 = lean_ctor_get(x_3, 5);
x_59 = lean_ctor_get(x_3, 6);
x_60 = lean_ctor_get(x_3, 7);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*18);
x_62 = lean_ctor_get(x_3, 9);
x_63 = lean_ctor_get(x_3, 10);
x_64 = lean_ctor_get(x_3, 11);
x_65 = lean_ctor_get(x_3, 12);
x_66 = lean_ctor_get(x_3, 13);
x_67 = lean_ctor_get(x_3, 14);
x_68 = lean_ctor_get(x_3, 15);
x_69 = lean_ctor_get(x_3, 16);
x_70 = lean_ctor_get(x_3, 17);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_71 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0;
x_72 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_54);
lean_ctor_set(x_72, 2, x_55);
lean_ctor_set(x_72, 3, x_56);
lean_ctor_set(x_72, 4, x_57);
lean_ctor_set(x_72, 5, x_58);
lean_ctor_set(x_72, 6, x_59);
lean_ctor_set(x_72, 7, x_60);
lean_ctor_set(x_72, 8, x_71);
lean_ctor_set(x_72, 9, x_62);
lean_ctor_set(x_72, 10, x_63);
lean_ctor_set(x_72, 11, x_64);
lean_ctor_set(x_72, 12, x_65);
lean_ctor_set(x_72, 13, x_66);
lean_ctor_set(x_72, 14, x_67);
lean_ctor_set(x_72, 15, x_68);
lean_ctor_set(x_72, 16, x_69);
lean_ctor_set(x_72, 17, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*18, x_61);
x_73 = l_Lean_Expr_mvarId_x21(x_23);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_11);
x_75 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(x_74, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_78 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(x_23, x_11);
lean_dec(x_11);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_79);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 1, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_76);
lean_dec(x_23);
lean_dec(x_11);
x_83 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_23);
lean_dec(x_11);
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_88 = !lean_is_exclusive(x_24);
if (x_88 == 0)
{
return x_24;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_24, 0);
lean_inc(x_89);
lean_dec(x_24);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_91 = !lean_is_exclusive(x_22);
if (x_91 == 0)
{
return x_22;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_22, 0);
lean_inc(x_92);
lean_dec(x_22);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_94 = !lean_is_exclusive(x_20);
if (x_94 == 0)
{
return x_20;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
lean_dec(x_20);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_97 = !lean_is_exclusive(x_17);
if (x_97 == 0)
{
return x_17;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_17, 0);
lean_inc(x_98);
lean_dec(x_17);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_100 = !lean_is_exclusive(x_15);
if (x_100 == 0)
{
return x_15;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_15, 0);
lean_inc(x_101);
lean_dec(x_15);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(x_2, x_3, x_4, x_5, x_6);
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
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2;
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
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2;
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
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2;
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
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_43; 
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_4, 2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
x_95 = 1;
lean_ctor_set_uint8(x_44, sizeof(void*)*11 + 16, x_95);
x_96 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_94, x_10);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_ctor_set_uint8(x_4, sizeof(void*)*7, x_95);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
x_46 = x_2;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_99; 
x_99 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_99);
lean_inc_ref(x_1);
x_100 = l_Lean_MessageData_ofExpr(x_1);
x_101 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_94, x_100, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_101) == 0)
{
lean_dec_ref(x_101);
x_46 = x_2;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = lean_box(0);
goto block_93;
}
else
{
uint8_t x_102; 
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
return x_99;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
block_93:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_st_ref_get(x_46);
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc_ref(x_1);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_1);
lean_closure_set(x_60, 2, x_58);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_61 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(x_60, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_free_object(x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
x_66 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_65, x_54);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
x_13 = x_64;
x_14 = x_46;
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_inc_ref(x_1);
x_69 = l_Lean_MessageData_ofExpr(x_1);
x_70 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_65, x_69, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_13 = x_64;
x_14 = x_46;
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = lean_box(0);
goto block_42;
}
else
{
uint8_t x_71; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; lean_object* x_75; 
lean_dec(x_63);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_74 = 0;
x_75 = lean_box(x_74);
lean_ctor_set(x_61, 0, x_75);
return x_61;
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
lean_dec(x_61);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
x_79 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_78, x_54);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
x_13 = x_77;
x_14 = x_46;
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_inc_ref(x_1);
x_82 = l_Lean_MessageData_ofExpr(x_1);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_78, x_82, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_13 = x_77;
x_14 = x_46;
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_61);
if (x_90 == 0)
{
return x_61;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_61, 0);
lean_inc(x_91);
lean_dec(x_61);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_108 = lean_ctor_get_uint8(x_44, sizeof(void*)*11);
x_109 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 1);
x_110 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 2);
x_111 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 3);
x_112 = lean_ctor_get(x_44, 0);
x_113 = lean_ctor_get(x_44, 1);
x_114 = lean_ctor_get(x_44, 2);
x_115 = lean_ctor_get(x_44, 3);
x_116 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 4);
x_117 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 5);
x_118 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 6);
x_119 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 7);
x_120 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 8);
x_121 = lean_ctor_get(x_44, 4);
x_122 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 9);
x_123 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 10);
x_124 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 11);
x_125 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 12);
x_126 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 13);
x_127 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 14);
x_128 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 15);
x_129 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 17);
x_130 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 18);
x_131 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 19);
x_132 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 20);
x_133 = lean_ctor_get(x_44, 5);
x_134 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 21);
x_135 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 22);
x_136 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 23);
x_137 = lean_ctor_get(x_44, 6);
x_138 = lean_ctor_get(x_44, 7);
x_139 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 24);
x_140 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 25);
x_141 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 26);
x_142 = lean_ctor_get(x_44, 8);
x_143 = lean_ctor_get(x_44, 9);
x_144 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 27);
x_145 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 28);
x_146 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 29);
x_147 = lean_ctor_get_uint8(x_44, sizeof(void*)*11 + 30);
x_148 = lean_ctor_get(x_44, 10);
lean_inc(x_148);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_133);
lean_inc(x_121);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_44);
x_184 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
x_185 = 1;
x_186 = lean_alloc_ctor(0, 11, 31);
lean_ctor_set(x_186, 0, x_112);
lean_ctor_set(x_186, 1, x_113);
lean_ctor_set(x_186, 2, x_114);
lean_ctor_set(x_186, 3, x_115);
lean_ctor_set(x_186, 4, x_121);
lean_ctor_set(x_186, 5, x_133);
lean_ctor_set(x_186, 6, x_137);
lean_ctor_set(x_186, 7, x_138);
lean_ctor_set(x_186, 8, x_142);
lean_ctor_set(x_186, 9, x_143);
lean_ctor_set(x_186, 10, x_148);
lean_ctor_set_uint8(x_186, sizeof(void*)*11, x_108);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 1, x_109);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 2, x_110);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 3, x_111);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 4, x_116);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 5, x_117);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 6, x_118);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 7, x_119);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 8, x_120);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 9, x_122);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 10, x_123);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 11, x_124);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 12, x_125);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 13, x_126);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 14, x_127);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 15, x_128);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 16, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 17, x_129);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 18, x_130);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 19, x_131);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 20, x_132);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 21, x_134);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 22, x_135);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 23, x_136);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 24, x_139);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 25, x_140);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 26, x_141);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 27, x_144);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 28, x_145);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 29, x_146);
lean_ctor_set_uint8(x_186, sizeof(void*)*11 + 30, x_147);
x_187 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_184, x_10);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
lean_ctor_set(x_4, 2, x_186);
lean_ctor_set_uint8(x_4, sizeof(void*)*7, x_185);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
x_149 = x_2;
x_150 = x_3;
x_151 = x_4;
x_152 = x_5;
x_153 = x_6;
x_154 = x_7;
x_155 = x_8;
x_156 = x_9;
x_157 = x_10;
x_158 = x_11;
x_159 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_190; 
x_190 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_190);
lean_inc_ref(x_1);
x_191 = l_Lean_MessageData_ofExpr(x_1);
x_192 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_184, x_191, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_192) == 0)
{
lean_dec_ref(x_192);
x_149 = x_2;
x_150 = x_3;
x_151 = x_4;
x_152 = x_5;
x_153 = x_6;
x_154 = x_7;
x_155 = x_8;
x_156 = x_9;
x_157 = x_10;
x_158 = x_11;
x_159 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_196 = lean_ctor_get(x_190, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_197 = x_190;
} else {
 lean_dec_ref(x_190);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
block_183:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_st_ref_get(x_149);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc_ref(x_1);
x_163 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(x_163, 0, x_162);
lean_closure_set(x_163, 1, x_1);
lean_closure_set(x_163, 2, x_161);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_153);
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_164 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(x_163, x_149, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_obj_tag(x_165) == 1)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_dec(x_166);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
x_169 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_168, x_157);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
x_13 = x_167;
x_14 = x_149;
x_15 = x_150;
x_16 = x_151;
x_17 = x_152;
x_18 = x_153;
x_19 = x_154;
x_20 = x_155;
x_21 = x_156;
x_22 = x_157;
x_23 = x_158;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_inc_ref(x_1);
x_172 = l_Lean_MessageData_ofExpr(x_1);
x_173 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_168, x_172, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_173);
x_13 = x_167;
x_14 = x_149;
x_15 = x_150;
x_16 = x_151;
x_17 = x_152;
x_18 = x_153;
x_19 = x_154;
x_20 = x_155;
x_21 = x_156;
x_22 = x_157;
x_23 = x_158;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_167);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
}
else
{
uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_165);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_1);
x_177 = 0;
x_178 = lean_box(x_177);
if (lean_is_scalar(x_166)) {
 x_179 = lean_alloc_ctor(0, 1, 0);
} else {
 x_179 = x_166;
}
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_164, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_181 = x_164;
} else {
 lean_dec_ref(x_164);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_199 = lean_ctor_get(x_4, 2);
x_200 = lean_ctor_get(x_4, 0);
x_201 = lean_ctor_get(x_4, 1);
x_202 = lean_ctor_get(x_4, 3);
x_203 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_204 = lean_ctor_get(x_4, 4);
x_205 = lean_ctor_get(x_4, 5);
x_206 = lean_ctor_get(x_4, 6);
x_207 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_202);
lean_inc(x_199);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_4);
x_208 = lean_ctor_get_uint8(x_199, sizeof(void*)*11);
x_209 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 1);
x_210 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 2);
x_211 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 3);
x_212 = lean_ctor_get(x_199, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_199, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_199, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_199, 3);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 4);
x_217 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 5);
x_218 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 6);
x_219 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 7);
x_220 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 8);
x_221 = lean_ctor_get(x_199, 4);
lean_inc(x_221);
x_222 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 9);
x_223 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 10);
x_224 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 11);
x_225 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 12);
x_226 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 13);
x_227 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 14);
x_228 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 15);
x_229 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 17);
x_230 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 18);
x_231 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 19);
x_232 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 20);
x_233 = lean_ctor_get(x_199, 5);
lean_inc(x_233);
x_234 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 21);
x_235 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 22);
x_236 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 23);
x_237 = lean_ctor_get(x_199, 6);
lean_inc(x_237);
x_238 = lean_ctor_get(x_199, 7);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 24);
x_240 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 25);
x_241 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 26);
x_242 = lean_ctor_get(x_199, 8);
lean_inc(x_242);
x_243 = lean_ctor_get(x_199, 9);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 27);
x_245 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 28);
x_246 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 29);
x_247 = lean_ctor_get_uint8(x_199, sizeof(void*)*11 + 30);
x_248 = lean_ctor_get(x_199, 10);
lean_inc(x_248);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 lean_ctor_release(x_199, 6);
 lean_ctor_release(x_199, 7);
 lean_ctor_release(x_199, 8);
 lean_ctor_release(x_199, 9);
 lean_ctor_release(x_199, 10);
 x_249 = x_199;
} else {
 lean_dec_ref(x_199);
 x_249 = lean_box(0);
}
x_285 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
x_286 = 1;
if (lean_is_scalar(x_249)) {
 x_287 = lean_alloc_ctor(0, 11, 31);
} else {
 x_287 = x_249;
}
lean_ctor_set(x_287, 0, x_212);
lean_ctor_set(x_287, 1, x_213);
lean_ctor_set(x_287, 2, x_214);
lean_ctor_set(x_287, 3, x_215);
lean_ctor_set(x_287, 4, x_221);
lean_ctor_set(x_287, 5, x_233);
lean_ctor_set(x_287, 6, x_237);
lean_ctor_set(x_287, 7, x_238);
lean_ctor_set(x_287, 8, x_242);
lean_ctor_set(x_287, 9, x_243);
lean_ctor_set(x_287, 10, x_248);
lean_ctor_set_uint8(x_287, sizeof(void*)*11, x_208);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 1, x_209);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 2, x_210);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 3, x_211);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 4, x_216);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 5, x_217);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 6, x_218);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 7, x_219);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 8, x_220);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 9, x_222);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 10, x_223);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 11, x_224);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 12, x_225);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 13, x_226);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 14, x_227);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 15, x_228);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 16, x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 17, x_229);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 18, x_230);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 19, x_231);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 20, x_232);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 21, x_234);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 22, x_235);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 23, x_236);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 24, x_239);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 25, x_240);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 26, x_241);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 27, x_244);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 28, x_245);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 29, x_246);
lean_ctor_set_uint8(x_287, sizeof(void*)*11 + 30, x_247);
x_288 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_285, x_10);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_290, 0, x_200);
lean_ctor_set(x_290, 1, x_201);
lean_ctor_set(x_290, 2, x_287);
lean_ctor_set(x_290, 3, x_202);
lean_ctor_set(x_290, 4, x_204);
lean_ctor_set(x_290, 5, x_205);
lean_ctor_set(x_290, 6, x_206);
lean_ctor_set_uint8(x_290, sizeof(void*)*7, x_286);
lean_ctor_set_uint8(x_290, sizeof(void*)*7 + 1, x_203);
lean_ctor_set_uint8(x_290, sizeof(void*)*7 + 2, x_207);
x_291 = lean_unbox(x_289);
lean_dec(x_289);
if (x_291 == 0)
{
x_250 = x_2;
x_251 = x_3;
x_252 = x_290;
x_253 = x_5;
x_254 = x_6;
x_255 = x_7;
x_256 = x_8;
x_257 = x_9;
x_258 = x_10;
x_259 = x_11;
x_260 = lean_box(0);
goto block_284;
}
else
{
lean_object* x_292; 
x_292 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_290, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec_ref(x_292);
lean_inc_ref(x_1);
x_293 = l_Lean_MessageData_ofExpr(x_1);
x_294 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_285, x_293, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_294) == 0)
{
lean_dec_ref(x_294);
x_250 = x_2;
x_251 = x_3;
x_252 = x_290;
x_253 = x_5;
x_254 = x_6;
x_255 = x_7;
x_256 = x_8;
x_257 = x_9;
x_258 = x_10;
x_259 = x_11;
x_260 = lean_box(0);
goto block_284;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_290);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec_ref(x_290);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_292, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_299 = x_292;
} else {
 lean_dec_ref(x_292);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_298);
return x_300;
}
}
block_284:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_st_ref_get(x_250);
x_262 = lean_ctor_get(x_261, 0);
lean_inc_ref(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_inc_ref(x_1);
x_264 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(x_264, 0, x_263);
lean_closure_set(x_264, 1, x_1);
lean_closure_set(x_264, 2, x_262);
lean_inc(x_259);
lean_inc_ref(x_258);
lean_inc(x_257);
lean_inc_ref(x_256);
lean_inc(x_255);
lean_inc_ref(x_254);
lean_inc(x_253);
lean_inc_ref(x_252);
lean_inc(x_251);
lean_inc(x_250);
x_265 = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(x_264, x_250, x_251, x_252, x_253, x_254, x_255, x_256, x_257, x_258, x_259);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_obj_tag(x_266) == 1)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_267);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
lean_dec_ref(x_266);
x_269 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
x_270 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(x_269, x_258);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
x_13 = x_268;
x_14 = x_250;
x_15 = x_251;
x_16 = x_252;
x_17 = x_253;
x_18 = x_254;
x_19 = x_255;
x_20 = x_256;
x_21 = x_257;
x_22 = x_258;
x_23 = x_259;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_inc_ref(x_1);
x_273 = l_Lean_MessageData_ofExpr(x_1);
x_274 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_269, x_273, x_256, x_257, x_258, x_259);
if (lean_obj_tag(x_274) == 0)
{
lean_dec_ref(x_274);
x_13 = x_268;
x_14 = x_250;
x_15 = x_251;
x_16 = x_252;
x_17 = x_253;
x_18 = x_254;
x_19 = x_255;
x_20 = x_256;
x_21 = x_257;
x_22 = x_258;
x_23 = x_259;
x_24 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_268);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec_ref(x_1);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
}
else
{
uint8_t x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_266);
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec_ref(x_1);
x_278 = 0;
x_279 = lean_box(x_278);
if (lean_is_scalar(x_267)) {
 x_280 = lean_alloc_ctor(0, 1, 0);
} else {
 x_280 = x_267;
}
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_259);
lean_dec_ref(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_265, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_282 = x_265;
} else {
 lean_dec_ref(x_265);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
return x_283;
}
}
}
block_42:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4;
lean_inc_ref(x_1);
x_26 = l_Lean_mkAppB(x_25, x_1, x_13);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_27 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_26, x_14, x_16, x_18, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = lean_grind_process_new_facts(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
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
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_19);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_29 = l_Lean_Meta_Grind_checkSplitStatus(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_box(0);
switch (lean_obj_tag(x_30)) {
case 0:
{
lean_object* x_32; 
lean_dec(x_28);
lean_free_object(x_2);
lean_dec(x_17);
x_32 = lean_box(x_1);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_3, 0, x_31);
x_2 = x_18;
goto _start;
}
case 1:
{
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_3, 0, x_31);
x_2 = x_18;
goto _start;
}
default: 
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec_ref(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_3, 0, x_31);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_28);
lean_free_object(x_2);
lean_dec(x_17);
x_41 = lean_box(x_1);
lean_ctor_set(x_21, 1, x_41);
lean_ctor_set(x_3, 0, x_31);
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_3, 0, x_31);
x_2 = x_18;
goto _start;
}
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_52 = l_Lean_Meta_Grind_checkSplitStatus(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_box(0);
switch (lean_obj_tag(x_53)) {
case 0:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_free_object(x_2);
lean_dec(x_17);
x_55 = lean_box(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_3, 1, x_56);
lean_ctor_set(x_3, 0, x_54);
x_2 = x_18;
goto _start;
}
case 1:
{
lean_object* x_58; 
lean_ctor_set(x_2, 1, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_3, 1, x_58);
lean_ctor_set(x_3, 0, x_54);
x_2 = x_18;
goto _start;
}
default: 
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_53, sizeof(void*)*1 + 1);
lean_dec_ref(x_53);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_ctor_set(x_2, 1, x_50);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_51);
lean_ctor_set(x_3, 1, x_65);
lean_ctor_set(x_3, 0, x_54);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
lean_free_object(x_2);
lean_dec(x_17);
x_67 = lean_box(x_1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_3, 1, x_68);
lean_ctor_set(x_3, 0, x_54);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
lean_dec(x_50);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_ctor_set(x_2, 1, x_50);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_51);
lean_ctor_set(x_3, 1, x_73);
lean_ctor_set(x_3, 0, x_54);
x_2 = x_18;
goto _start;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_51);
lean_dec(x_50);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_76 = x_52;
} else {
 lean_dec_ref(x_52);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(x_1);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_3, 0, x_80);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_21, 0);
x_82 = lean_ctor_get(x_21, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_21);
x_83 = lean_box(x_1);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_3, 1, x_85);
lean_ctor_set(x_3, 0, x_84);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_19, 0);
lean_inc(x_86);
lean_dec(x_19);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_21, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_21, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_90 = x_21;
} else {
 lean_dec_ref(x_21);
 x_90 = lean_box(0);
}
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_91 = l_Lean_Meta_Grind_checkSplitStatus(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_box(0);
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_89);
lean_free_object(x_2);
lean_dec(x_17);
x_94 = lean_box(x_1);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_3, 1, x_95);
lean_ctor_set(x_3, 0, x_93);
x_2 = x_18;
goto _start;
}
case 1:
{
lean_object* x_97; 
lean_ctor_set(x_2, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_90;
}
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_3, 1, x_97);
lean_ctor_set(x_3, 0, x_93);
x_2 = x_18;
goto _start;
}
default: 
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_92, sizeof(void*)*1 + 1);
lean_dec_ref(x_92);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_101 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_ctor_set(x_2, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_90;
}
lean_ctor_set(x_104, 0, x_2);
lean_ctor_set(x_104, 1, x_89);
lean_ctor_set(x_3, 1, x_104);
lean_ctor_set(x_3, 0, x_93);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_89);
lean_free_object(x_2);
lean_dec(x_17);
x_106 = lean_box(x_1);
if (lean_is_scalar(x_90)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_90;
}
lean_ctor_set(x_107, 0, x_88);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_3, 1, x_107);
lean_ctor_set(x_3, 0, x_93);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_ctor_set(x_2, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_90;
}
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_89);
lean_ctor_set(x_3, 1, x_112);
lean_ctor_set(x_3, 0, x_93);
x_2 = x_18;
goto _start;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_3);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_115 = x_91;
} else {
 lean_dec_ref(x_91);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_117 = lean_ctor_get(x_21, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_21, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_119 = x_21;
} else {
 lean_dec_ref(x_21);
 x_119 = lean_box(0);
}
x_120 = lean_box(x_1);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_3, 1, x_122);
lean_ctor_set(x_3, 0, x_121);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_3);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
lean_dec(x_3);
x_125 = lean_ctor_get(x_19, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_126 = x_19;
} else {
 lean_dec_ref(x_19);
 x_126 = lean_box(0);
}
x_127 = lean_unbox(x_125);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_126);
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_131 = l_Lean_Meta_Grind_checkSplitStatus(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_box(0);
switch (lean_obj_tag(x_132)) {
case 0:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_129);
lean_free_object(x_2);
lean_dec(x_17);
x_134 = lean_box(x_1);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_2 = x_18;
x_3 = x_136;
goto _start;
}
case 1:
{
lean_object* x_138; lean_object* x_139; 
lean_ctor_set(x_2, 1, x_128);
if (lean_is_scalar(x_130)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_130;
}
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_129);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
x_2 = x_18;
x_3 = x_139;
goto _start;
}
default: 
{
uint8_t x_141; 
x_141 = lean_ctor_get_uint8(x_132, sizeof(void*)*1 + 1);
lean_dec_ref(x_132);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_143 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_142, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_ctor_set(x_2, 1, x_128);
if (lean_is_scalar(x_130)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_130;
}
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_129);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_146);
x_2 = x_18;
x_3 = x_147;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_129);
lean_free_object(x_2);
lean_dec(x_17);
x_149 = lean_box(x_1);
if (lean_is_scalar(x_130)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_130;
}
lean_ctor_set(x_150, 0, x_128);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_150);
x_2 = x_18;
x_3 = x_151;
goto _start;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_154 = x_143;
} else {
 lean_dec_ref(x_143);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_ctor_set(x_2, 1, x_128);
if (lean_is_scalar(x_130)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_130;
}
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_129);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_133);
lean_ctor_set(x_157, 1, x_156);
x_2 = x_18;
x_3 = x_157;
goto _start;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_159 = lean_ctor_get(x_131, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_160 = x_131;
} else {
 lean_dec_ref(x_131);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
x_162 = lean_ctor_get(x_124, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_124, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_164 = x_124;
} else {
 lean_dec_ref(x_124);
 x_164 = lean_box(0);
}
x_165 = lean_box(x_1);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_163);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
if (lean_is_scalar(x_126)) {
 x_169 = lean_alloc_ctor(0, 1, 0);
} else {
 x_169 = x_126;
}
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
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
lean_dec_ref(x_3);
x_170 = !lean_is_exclusive(x_19);
if (x_170 == 0)
{
return x_19;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_19, 0);
lean_inc(x_171);
lean_dec(x_19);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_2, 0);
x_174 = lean_ctor_get(x_2, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_2);
x_175 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_177 = x_3;
} else {
 lean_dec_ref(x_3);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_179 = x_175;
} else {
 lean_dec_ref(x_175);
 x_179 = lean_box(0);
}
x_180 = lean_unbox(x_178);
lean_dec(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_179);
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_173);
x_184 = l_Lean_Meta_Grind_checkSplitStatus(x_173, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_box(0);
switch (lean_obj_tag(x_185)) {
case 0:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_182);
lean_dec(x_173);
x_187 = lean_box(x_1);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_177)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_177;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_2 = x_174;
x_3 = x_189;
goto _start;
}
case 1:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_173);
lean_ctor_set(x_191, 1, x_181);
if (lean_is_scalar(x_183)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_183;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_177;
}
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_192);
x_2 = x_174;
x_3 = x_193;
goto _start;
}
default: 
{
uint8_t x_195; 
x_195 = lean_ctor_get_uint8(x_185, sizeof(void*)*1 + 1);
lean_dec_ref(x_185);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_173);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_197 = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(x_196, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_173);
lean_ctor_set(x_200, 1, x_181);
if (lean_is_scalar(x_183)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_183;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_177;
}
lean_ctor_set(x_202, 0, x_186);
lean_ctor_set(x_202, 1, x_201);
x_2 = x_174;
x_3 = x_202;
goto _start;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_182);
lean_dec(x_173);
x_204 = lean_box(x_1);
if (lean_is_scalar(x_183)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_183;
}
lean_ctor_set(x_205, 0, x_181);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_177)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_177;
}
lean_ctor_set(x_206, 0, x_186);
lean_ctor_set(x_206, 1, x_205);
x_2 = x_174;
x_3 = x_206;
goto _start;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_174);
lean_dec(x_173);
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
x_208 = lean_ctor_get(x_197, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_209 = x_197;
} else {
 lean_dec_ref(x_197);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_173);
lean_ctor_set(x_211, 1, x_181);
if (lean_is_scalar(x_183)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_183;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_177;
}
lean_ctor_set(x_213, 0, x_186);
lean_ctor_set(x_213, 1, x_212);
x_2 = x_174;
x_3 = x_213;
goto _start;
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_174);
lean_dec(x_173);
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
x_215 = lean_ctor_get(x_184, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_216 = x_184;
} else {
 lean_dec_ref(x_184);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_174);
lean_dec(x_173);
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
x_218 = lean_ctor_get(x_176, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_176, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_220 = x_176;
} else {
 lean_dec_ref(x_176);
 x_220 = lean_box(0);
}
x_221 = lean_box(x_1);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_220;
}
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_219);
if (lean_is_scalar(x_177)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_177;
}
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
if (lean_is_scalar(x_179)) {
 x_225 = lean_alloc_ctor(0, 1, 0);
} else {
 x_225 = x_179;
}
lean_ctor_set(x_225, 0, x_224);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_174);
lean_dec(x_173);
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
lean_dec_ref(x_3);
x_226 = lean_ctor_get(x_175, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_227 = x_175;
} else {
 lean_dec_ref(x_175);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
return x_228;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*11 + 13);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_get(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 15);
lean_inc_ref(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_21, 5);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_List_isEmpty___redArg(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_12);
x_24 = lean_st_ref_get(x_1);
x_25 = lean_st_ref_take(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_26, 15);
lean_inc_ref(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 15);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_27, 5);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_27, 5, x_34);
x_35 = lean_st_ref_set(x_1, x_25);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_37, 15);
lean_inc_ref(x_39);
lean_dec_ref(x_37);
x_40 = lean_ctor_get(x_39, 5);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_box(0);
x_42 = lean_box(x_23);
lean_ctor_set(x_24, 1, x_42);
lean_ctor_set(x_24, 0, x_34);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_41);
lean_inc(x_1);
x_43 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_40, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_1);
x_50 = lean_box(x_23);
lean_ctor_set(x_43, 0, x_50);
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_st_ref_take(x_1);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_53, 15);
lean_inc_ref(x_54);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_53, 15);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_54, 5);
x_61 = l_List_reverse___redArg(x_51);
x_62 = l_List_appendTR___redArg(x_60, x_61);
lean_ctor_set(x_54, 5, x_62);
x_63 = lean_st_ref_set(x_1, x_52);
lean_dec(x_1);
x_64 = lean_box(x_15);
lean_ctor_set(x_43, 0, x_64);
return x_43;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
x_67 = lean_ctor_get(x_54, 2);
x_68 = lean_ctor_get(x_54, 3);
x_69 = lean_ctor_get(x_54, 4);
x_70 = lean_ctor_get(x_54, 5);
x_71 = lean_ctor_get(x_54, 6);
x_72 = lean_ctor_get(x_54, 7);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_73 = l_List_reverse___redArg(x_51);
x_74 = l_List_appendTR___redArg(x_70, x_73);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_69);
lean_ctor_set(x_75, 5, x_74);
lean_ctor_set(x_75, 6, x_71);
lean_ctor_set(x_75, 7, x_72);
lean_ctor_set(x_53, 15, x_75);
x_76 = lean_st_ref_set(x_1, x_52);
lean_dec(x_1);
x_77 = lean_box(x_15);
lean_ctor_set(x_43, 0, x_77);
return x_43;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
x_80 = lean_ctor_get(x_53, 2);
x_81 = lean_ctor_get(x_53, 3);
x_82 = lean_ctor_get(x_53, 4);
x_83 = lean_ctor_get(x_53, 5);
x_84 = lean_ctor_get(x_53, 6);
x_85 = lean_ctor_get(x_53, 7);
x_86 = lean_ctor_get(x_53, 8);
x_87 = lean_ctor_get_uint8(x_53, sizeof(void*)*18);
x_88 = lean_ctor_get(x_53, 9);
x_89 = lean_ctor_get(x_53, 10);
x_90 = lean_ctor_get(x_53, 11);
x_91 = lean_ctor_get(x_53, 12);
x_92 = lean_ctor_get(x_53, 13);
x_93 = lean_ctor_get(x_53, 14);
x_94 = lean_ctor_get(x_53, 16);
x_95 = lean_ctor_get(x_53, 17);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
x_96 = lean_ctor_get(x_54, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_54, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_54, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_54, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_54, 6);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_54, 7);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 x_104 = x_54;
} else {
 lean_dec_ref(x_54);
 x_104 = lean_box(0);
}
x_105 = l_List_reverse___redArg(x_51);
x_106 = l_List_appendTR___redArg(x_101, x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 8, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_96);
lean_ctor_set(x_107, 1, x_97);
lean_ctor_set(x_107, 2, x_98);
lean_ctor_set(x_107, 3, x_99);
lean_ctor_set(x_107, 4, x_100);
lean_ctor_set(x_107, 5, x_106);
lean_ctor_set(x_107, 6, x_102);
lean_ctor_set(x_107, 7, x_103);
x_108 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_108, 0, x_78);
lean_ctor_set(x_108, 1, x_79);
lean_ctor_set(x_108, 2, x_80);
lean_ctor_set(x_108, 3, x_81);
lean_ctor_set(x_108, 4, x_82);
lean_ctor_set(x_108, 5, x_83);
lean_ctor_set(x_108, 6, x_84);
lean_ctor_set(x_108, 7, x_85);
lean_ctor_set(x_108, 8, x_86);
lean_ctor_set(x_108, 9, x_88);
lean_ctor_set(x_108, 10, x_89);
lean_ctor_set(x_108, 11, x_90);
lean_ctor_set(x_108, 12, x_91);
lean_ctor_set(x_108, 13, x_92);
lean_ctor_set(x_108, 14, x_93);
lean_ctor_set(x_108, 15, x_107);
lean_ctor_set(x_108, 16, x_94);
lean_ctor_set(x_108, 17, x_95);
lean_ctor_set_uint8(x_108, sizeof(void*)*18, x_87);
lean_ctor_set(x_52, 0, x_108);
x_109 = lean_st_ref_set(x_1, x_52);
lean_dec(x_1);
x_110 = lean_box(x_15);
lean_ctor_set(x_43, 0, x_110);
return x_43;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_111 = lean_ctor_get(x_52, 1);
lean_inc(x_111);
lean_dec(x_52);
x_112 = lean_ctor_get(x_53, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_53, 4);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_53, 5);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_53, 6);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_53, 7);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_53, 8);
lean_inc_ref(x_120);
x_121 = lean_ctor_get_uint8(x_53, sizeof(void*)*18);
x_122 = lean_ctor_get(x_53, 9);
lean_inc(x_122);
x_123 = lean_ctor_get(x_53, 10);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_53, 11);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_53, 12);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_53, 13);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_53, 14);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_53, 16);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_53, 17);
lean_inc_ref(x_129);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 lean_ctor_release(x_53, 7);
 lean_ctor_release(x_53, 8);
 lean_ctor_release(x_53, 9);
 lean_ctor_release(x_53, 10);
 lean_ctor_release(x_53, 11);
 lean_ctor_release(x_53, 12);
 lean_ctor_release(x_53, 13);
 lean_ctor_release(x_53, 14);
 lean_ctor_release(x_53, 15);
 lean_ctor_release(x_53, 16);
 lean_ctor_release(x_53, 17);
 x_130 = x_53;
} else {
 lean_dec_ref(x_53);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_54, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_54, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_54, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_54, 5);
lean_inc(x_136);
x_137 = lean_ctor_get(x_54, 6);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_54, 7);
lean_inc_ref(x_138);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 x_139 = x_54;
} else {
 lean_dec_ref(x_54);
 x_139 = lean_box(0);
}
x_140 = l_List_reverse___redArg(x_51);
x_141 = l_List_appendTR___redArg(x_136, x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 8, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_132);
lean_ctor_set(x_142, 2, x_133);
lean_ctor_set(x_142, 3, x_134);
lean_ctor_set(x_142, 4, x_135);
lean_ctor_set(x_142, 5, x_141);
lean_ctor_set(x_142, 6, x_137);
lean_ctor_set(x_142, 7, x_138);
if (lean_is_scalar(x_130)) {
 x_143 = lean_alloc_ctor(0, 18, 1);
} else {
 x_143 = x_130;
}
lean_ctor_set(x_143, 0, x_112);
lean_ctor_set(x_143, 1, x_113);
lean_ctor_set(x_143, 2, x_114);
lean_ctor_set(x_143, 3, x_115);
lean_ctor_set(x_143, 4, x_116);
lean_ctor_set(x_143, 5, x_117);
lean_ctor_set(x_143, 6, x_118);
lean_ctor_set(x_143, 7, x_119);
lean_ctor_set(x_143, 8, x_120);
lean_ctor_set(x_143, 9, x_122);
lean_ctor_set(x_143, 10, x_123);
lean_ctor_set(x_143, 11, x_124);
lean_ctor_set(x_143, 12, x_125);
lean_ctor_set(x_143, 13, x_126);
lean_ctor_set(x_143, 14, x_127);
lean_ctor_set(x_143, 15, x_142);
lean_ctor_set(x_143, 16, x_128);
lean_ctor_set(x_143, 17, x_129);
lean_ctor_set_uint8(x_143, sizeof(void*)*18, x_121);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_111);
x_145 = lean_st_ref_set(x_1, x_144);
lean_dec(x_1);
x_146 = lean_box(x_15);
lean_ctor_set(x_43, 0, x_146);
return x_43;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_46);
lean_dec(x_1);
x_147 = lean_ctor_get(x_47, 0);
lean_inc(x_147);
lean_dec_ref(x_47);
lean_ctor_set(x_43, 0, x_147);
return x_43;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_43, 0);
lean_inc(x_148);
lean_dec(x_43);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_149, 1);
x_152 = lean_unbox(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_149);
lean_dec(x_1);
x_153 = lean_box(x_23);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
lean_dec(x_149);
x_156 = lean_st_ref_take(x_1);
x_157 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_157, 15);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_157, 3);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_157, 4);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_157, 5);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_157, 6);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_157, 7);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_157, 8);
lean_inc_ref(x_169);
x_170 = lean_ctor_get_uint8(x_157, sizeof(void*)*18);
x_171 = lean_ctor_get(x_157, 9);
lean_inc(x_171);
x_172 = lean_ctor_get(x_157, 10);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_157, 11);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_157, 12);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_157, 13);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_157, 14);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_157, 16);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_157, 17);
lean_inc_ref(x_178);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 lean_ctor_release(x_157, 3);
 lean_ctor_release(x_157, 4);
 lean_ctor_release(x_157, 5);
 lean_ctor_release(x_157, 6);
 lean_ctor_release(x_157, 7);
 lean_ctor_release(x_157, 8);
 lean_ctor_release(x_157, 9);
 lean_ctor_release(x_157, 10);
 lean_ctor_release(x_157, 11);
 lean_ctor_release(x_157, 12);
 lean_ctor_release(x_157, 13);
 lean_ctor_release(x_157, 14);
 lean_ctor_release(x_157, 15);
 lean_ctor_release(x_157, 16);
 lean_ctor_release(x_157, 17);
 x_179 = x_157;
} else {
 lean_dec_ref(x_157);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_158, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_158, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_158, 2);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_158, 3);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_158, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_158, 5);
lean_inc(x_185);
x_186 = lean_ctor_get(x_158, 6);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_158, 7);
lean_inc_ref(x_187);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 lean_ctor_release(x_158, 5);
 lean_ctor_release(x_158, 6);
 lean_ctor_release(x_158, 7);
 x_188 = x_158;
} else {
 lean_dec_ref(x_158);
 x_188 = lean_box(0);
}
x_189 = l_List_reverse___redArg(x_155);
x_190 = l_List_appendTR___redArg(x_185, x_189);
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 8, 0);
} else {
 x_191 = x_188;
}
lean_ctor_set(x_191, 0, x_180);
lean_ctor_set(x_191, 1, x_181);
lean_ctor_set(x_191, 2, x_182);
lean_ctor_set(x_191, 3, x_183);
lean_ctor_set(x_191, 4, x_184);
lean_ctor_set(x_191, 5, x_190);
lean_ctor_set(x_191, 6, x_186);
lean_ctor_set(x_191, 7, x_187);
if (lean_is_scalar(x_179)) {
 x_192 = lean_alloc_ctor(0, 18, 1);
} else {
 x_192 = x_179;
}
lean_ctor_set(x_192, 0, x_161);
lean_ctor_set(x_192, 1, x_162);
lean_ctor_set(x_192, 2, x_163);
lean_ctor_set(x_192, 3, x_164);
lean_ctor_set(x_192, 4, x_165);
lean_ctor_set(x_192, 5, x_166);
lean_ctor_set(x_192, 6, x_167);
lean_ctor_set(x_192, 7, x_168);
lean_ctor_set(x_192, 8, x_169);
lean_ctor_set(x_192, 9, x_171);
lean_ctor_set(x_192, 10, x_172);
lean_ctor_set(x_192, 11, x_173);
lean_ctor_set(x_192, 12, x_174);
lean_ctor_set(x_192, 13, x_175);
lean_ctor_set(x_192, 14, x_176);
lean_ctor_set(x_192, 15, x_191);
lean_ctor_set(x_192, 16, x_177);
lean_ctor_set(x_192, 17, x_178);
lean_ctor_set_uint8(x_192, sizeof(void*)*18, x_170);
if (lean_is_scalar(x_160)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_160;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_159);
x_194 = lean_st_ref_set(x_1, x_193);
lean_dec(x_1);
x_195 = lean_box(x_15);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_149);
lean_dec(x_1);
x_197 = lean_ctor_get(x_150, 0);
lean_inc(x_197);
lean_dec_ref(x_150);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_43);
if (x_199 == 0)
{
return x_43;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_43, 0);
lean_inc(x_200);
lean_dec(x_43);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_24, 0);
lean_inc(x_202);
lean_dec(x_24);
x_203 = lean_ctor_get(x_202, 15);
lean_inc_ref(x_203);
lean_dec_ref(x_202);
x_204 = lean_ctor_get(x_203, 5);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_box(0);
x_206 = lean_box(x_23);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_34);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_17, 1, x_207);
lean_ctor_set(x_17, 0, x_205);
lean_inc(x_1);
x_208 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_204, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
lean_dec(x_209);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_211, 1);
x_214 = lean_unbox(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_211);
lean_dec(x_1);
x_215 = lean_box(x_23);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
lean_dec(x_211);
x_218 = lean_st_ref_take(x_1);
x_219 = lean_ctor_get(x_218, 0);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_219, 15);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_219, 2);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_219, 3);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_219, 4);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_219, 5);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_219, 6);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_219, 7);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_219, 8);
lean_inc_ref(x_231);
x_232 = lean_ctor_get_uint8(x_219, sizeof(void*)*18);
x_233 = lean_ctor_get(x_219, 9);
lean_inc(x_233);
x_234 = lean_ctor_get(x_219, 10);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_219, 11);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_219, 12);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_219, 13);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_219, 14);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_219, 16);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_219, 17);
lean_inc_ref(x_240);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 lean_ctor_release(x_219, 6);
 lean_ctor_release(x_219, 7);
 lean_ctor_release(x_219, 8);
 lean_ctor_release(x_219, 9);
 lean_ctor_release(x_219, 10);
 lean_ctor_release(x_219, 11);
 lean_ctor_release(x_219, 12);
 lean_ctor_release(x_219, 13);
 lean_ctor_release(x_219, 14);
 lean_ctor_release(x_219, 15);
 lean_ctor_release(x_219, 16);
 lean_ctor_release(x_219, 17);
 x_241 = x_219;
} else {
 lean_dec_ref(x_219);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_220, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_220, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_220, 2);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_220, 3);
lean_inc_ref(x_245);
x_246 = lean_ctor_get(x_220, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_220, 5);
lean_inc(x_247);
x_248 = lean_ctor_get(x_220, 6);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_220, 7);
lean_inc_ref(x_249);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 lean_ctor_release(x_220, 3);
 lean_ctor_release(x_220, 4);
 lean_ctor_release(x_220, 5);
 lean_ctor_release(x_220, 6);
 lean_ctor_release(x_220, 7);
 x_250 = x_220;
} else {
 lean_dec_ref(x_220);
 x_250 = lean_box(0);
}
x_251 = l_List_reverse___redArg(x_217);
x_252 = l_List_appendTR___redArg(x_247, x_251);
if (lean_is_scalar(x_250)) {
 x_253 = lean_alloc_ctor(0, 8, 0);
} else {
 x_253 = x_250;
}
lean_ctor_set(x_253, 0, x_242);
lean_ctor_set(x_253, 1, x_243);
lean_ctor_set(x_253, 2, x_244);
lean_ctor_set(x_253, 3, x_245);
lean_ctor_set(x_253, 4, x_246);
lean_ctor_set(x_253, 5, x_252);
lean_ctor_set(x_253, 6, x_248);
lean_ctor_set(x_253, 7, x_249);
if (lean_is_scalar(x_241)) {
 x_254 = lean_alloc_ctor(0, 18, 1);
} else {
 x_254 = x_241;
}
lean_ctor_set(x_254, 0, x_223);
lean_ctor_set(x_254, 1, x_224);
lean_ctor_set(x_254, 2, x_225);
lean_ctor_set(x_254, 3, x_226);
lean_ctor_set(x_254, 4, x_227);
lean_ctor_set(x_254, 5, x_228);
lean_ctor_set(x_254, 6, x_229);
lean_ctor_set(x_254, 7, x_230);
lean_ctor_set(x_254, 8, x_231);
lean_ctor_set(x_254, 9, x_233);
lean_ctor_set(x_254, 10, x_234);
lean_ctor_set(x_254, 11, x_235);
lean_ctor_set(x_254, 12, x_236);
lean_ctor_set(x_254, 13, x_237);
lean_ctor_set(x_254, 14, x_238);
lean_ctor_set(x_254, 15, x_253);
lean_ctor_set(x_254, 16, x_239);
lean_ctor_set(x_254, 17, x_240);
lean_ctor_set_uint8(x_254, sizeof(void*)*18, x_232);
if (lean_is_scalar(x_222)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_222;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_221);
x_256 = lean_st_ref_set(x_1, x_255);
lean_dec(x_1);
x_257 = lean_box(x_15);
if (lean_is_scalar(x_210)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_210;
}
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_211);
lean_dec(x_1);
x_259 = lean_ctor_get(x_212, 0);
lean_inc(x_259);
lean_dec_ref(x_212);
if (lean_is_scalar(x_210)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_210;
}
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_1);
x_261 = lean_ctor_get(x_208, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_262 = x_208;
} else {
 lean_dec_ref(x_208);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_264 = lean_ctor_get(x_27, 0);
x_265 = lean_ctor_get(x_27, 1);
x_266 = lean_ctor_get(x_27, 2);
x_267 = lean_ctor_get(x_27, 3);
x_268 = lean_ctor_get(x_27, 4);
x_269 = lean_ctor_get(x_27, 6);
x_270 = lean_ctor_get(x_27, 7);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_27);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_265);
lean_ctor_set(x_272, 2, x_266);
lean_ctor_set(x_272, 3, x_267);
lean_ctor_set(x_272, 4, x_268);
lean_ctor_set(x_272, 5, x_271);
lean_ctor_set(x_272, 6, x_269);
lean_ctor_set(x_272, 7, x_270);
lean_ctor_set(x_26, 15, x_272);
x_273 = lean_st_ref_set(x_1, x_25);
x_274 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_274);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_275 = x_24;
} else {
 lean_dec_ref(x_24);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_274, 15);
lean_inc_ref(x_276);
lean_dec_ref(x_274);
x_277 = lean_ctor_get(x_276, 5);
lean_inc(x_277);
lean_dec_ref(x_276);
x_278 = lean_box(0);
x_279 = lean_box(x_23);
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_271);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_17, 1, x_280);
lean_ctor_set(x_17, 0, x_278);
lean_inc(x_1);
x_281 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_277, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 0);
lean_inc(x_285);
lean_dec(x_282);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_284, 1);
x_287 = lean_unbox(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_284);
lean_dec(x_1);
x_288 = lean_box(x_23);
if (lean_is_scalar(x_283)) {
 x_289 = lean_alloc_ctor(0, 1, 0);
} else {
 x_289 = x_283;
}
lean_ctor_set(x_289, 0, x_288);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
lean_dec(x_284);
x_291 = lean_st_ref_take(x_1);
x_292 = lean_ctor_get(x_291, 0);
lean_inc_ref(x_292);
x_293 = lean_ctor_get(x_292, 15);
lean_inc_ref(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_295 = x_291;
} else {
 lean_dec_ref(x_291);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 1);
lean_inc_ref(x_297);
x_298 = lean_ctor_get(x_292, 2);
lean_inc_ref(x_298);
x_299 = lean_ctor_get(x_292, 3);
lean_inc_ref(x_299);
x_300 = lean_ctor_get(x_292, 4);
lean_inc_ref(x_300);
x_301 = lean_ctor_get(x_292, 5);
lean_inc_ref(x_301);
x_302 = lean_ctor_get(x_292, 6);
lean_inc_ref(x_302);
x_303 = lean_ctor_get(x_292, 7);
lean_inc_ref(x_303);
x_304 = lean_ctor_get(x_292, 8);
lean_inc_ref(x_304);
x_305 = lean_ctor_get_uint8(x_292, sizeof(void*)*18);
x_306 = lean_ctor_get(x_292, 9);
lean_inc(x_306);
x_307 = lean_ctor_get(x_292, 10);
lean_inc_ref(x_307);
x_308 = lean_ctor_get(x_292, 11);
lean_inc_ref(x_308);
x_309 = lean_ctor_get(x_292, 12);
lean_inc_ref(x_309);
x_310 = lean_ctor_get(x_292, 13);
lean_inc_ref(x_310);
x_311 = lean_ctor_get(x_292, 14);
lean_inc_ref(x_311);
x_312 = lean_ctor_get(x_292, 16);
lean_inc_ref(x_312);
x_313 = lean_ctor_get(x_292, 17);
lean_inc_ref(x_313);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 lean_ctor_release(x_292, 3);
 lean_ctor_release(x_292, 4);
 lean_ctor_release(x_292, 5);
 lean_ctor_release(x_292, 6);
 lean_ctor_release(x_292, 7);
 lean_ctor_release(x_292, 8);
 lean_ctor_release(x_292, 9);
 lean_ctor_release(x_292, 10);
 lean_ctor_release(x_292, 11);
 lean_ctor_release(x_292, 12);
 lean_ctor_release(x_292, 13);
 lean_ctor_release(x_292, 14);
 lean_ctor_release(x_292, 15);
 lean_ctor_release(x_292, 16);
 lean_ctor_release(x_292, 17);
 x_314 = x_292;
} else {
 lean_dec_ref(x_292);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_293, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_293, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_293, 2);
lean_inc_ref(x_317);
x_318 = lean_ctor_get(x_293, 3);
lean_inc_ref(x_318);
x_319 = lean_ctor_get(x_293, 4);
lean_inc(x_319);
x_320 = lean_ctor_get(x_293, 5);
lean_inc(x_320);
x_321 = lean_ctor_get(x_293, 6);
lean_inc_ref(x_321);
x_322 = lean_ctor_get(x_293, 7);
lean_inc_ref(x_322);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 lean_ctor_release(x_293, 4);
 lean_ctor_release(x_293, 5);
 lean_ctor_release(x_293, 6);
 lean_ctor_release(x_293, 7);
 x_323 = x_293;
} else {
 lean_dec_ref(x_293);
 x_323 = lean_box(0);
}
x_324 = l_List_reverse___redArg(x_290);
x_325 = l_List_appendTR___redArg(x_320, x_324);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(0, 8, 0);
} else {
 x_326 = x_323;
}
lean_ctor_set(x_326, 0, x_315);
lean_ctor_set(x_326, 1, x_316);
lean_ctor_set(x_326, 2, x_317);
lean_ctor_set(x_326, 3, x_318);
lean_ctor_set(x_326, 4, x_319);
lean_ctor_set(x_326, 5, x_325);
lean_ctor_set(x_326, 6, x_321);
lean_ctor_set(x_326, 7, x_322);
if (lean_is_scalar(x_314)) {
 x_327 = lean_alloc_ctor(0, 18, 1);
} else {
 x_327 = x_314;
}
lean_ctor_set(x_327, 0, x_296);
lean_ctor_set(x_327, 1, x_297);
lean_ctor_set(x_327, 2, x_298);
lean_ctor_set(x_327, 3, x_299);
lean_ctor_set(x_327, 4, x_300);
lean_ctor_set(x_327, 5, x_301);
lean_ctor_set(x_327, 6, x_302);
lean_ctor_set(x_327, 7, x_303);
lean_ctor_set(x_327, 8, x_304);
lean_ctor_set(x_327, 9, x_306);
lean_ctor_set(x_327, 10, x_307);
lean_ctor_set(x_327, 11, x_308);
lean_ctor_set(x_327, 12, x_309);
lean_ctor_set(x_327, 13, x_310);
lean_ctor_set(x_327, 14, x_311);
lean_ctor_set(x_327, 15, x_326);
lean_ctor_set(x_327, 16, x_312);
lean_ctor_set(x_327, 17, x_313);
lean_ctor_set_uint8(x_327, sizeof(void*)*18, x_305);
if (lean_is_scalar(x_295)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_295;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_294);
x_329 = lean_st_ref_set(x_1, x_328);
lean_dec(x_1);
x_330 = lean_box(x_15);
if (lean_is_scalar(x_283)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_283;
}
lean_ctor_set(x_331, 0, x_330);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_284);
lean_dec(x_1);
x_332 = lean_ctor_get(x_285, 0);
lean_inc(x_332);
lean_dec_ref(x_285);
if (lean_is_scalar(x_283)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_283;
}
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_1);
x_334 = lean_ctor_get(x_281, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_335 = x_281;
} else {
 lean_dec_ref(x_281);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 1, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_337 = lean_ctor_get(x_26, 0);
x_338 = lean_ctor_get(x_26, 1);
x_339 = lean_ctor_get(x_26, 2);
x_340 = lean_ctor_get(x_26, 3);
x_341 = lean_ctor_get(x_26, 4);
x_342 = lean_ctor_get(x_26, 5);
x_343 = lean_ctor_get(x_26, 6);
x_344 = lean_ctor_get(x_26, 7);
x_345 = lean_ctor_get(x_26, 8);
x_346 = lean_ctor_get_uint8(x_26, sizeof(void*)*18);
x_347 = lean_ctor_get(x_26, 9);
x_348 = lean_ctor_get(x_26, 10);
x_349 = lean_ctor_get(x_26, 11);
x_350 = lean_ctor_get(x_26, 12);
x_351 = lean_ctor_get(x_26, 13);
x_352 = lean_ctor_get(x_26, 14);
x_353 = lean_ctor_get(x_26, 16);
x_354 = lean_ctor_get(x_26, 17);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_26);
x_355 = lean_ctor_get(x_27, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_27, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_357);
x_358 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_358);
x_359 = lean_ctor_get(x_27, 4);
lean_inc(x_359);
x_360 = lean_ctor_get(x_27, 6);
lean_inc_ref(x_360);
x_361 = lean_ctor_get(x_27, 7);
lean_inc_ref(x_361);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 x_362 = x_27;
} else {
 lean_dec_ref(x_27);
 x_362 = lean_box(0);
}
x_363 = lean_box(0);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 8, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_355);
lean_ctor_set(x_364, 1, x_356);
lean_ctor_set(x_364, 2, x_357);
lean_ctor_set(x_364, 3, x_358);
lean_ctor_set(x_364, 4, x_359);
lean_ctor_set(x_364, 5, x_363);
lean_ctor_set(x_364, 6, x_360);
lean_ctor_set(x_364, 7, x_361);
x_365 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_365, 0, x_337);
lean_ctor_set(x_365, 1, x_338);
lean_ctor_set(x_365, 2, x_339);
lean_ctor_set(x_365, 3, x_340);
lean_ctor_set(x_365, 4, x_341);
lean_ctor_set(x_365, 5, x_342);
lean_ctor_set(x_365, 6, x_343);
lean_ctor_set(x_365, 7, x_344);
lean_ctor_set(x_365, 8, x_345);
lean_ctor_set(x_365, 9, x_347);
lean_ctor_set(x_365, 10, x_348);
lean_ctor_set(x_365, 11, x_349);
lean_ctor_set(x_365, 12, x_350);
lean_ctor_set(x_365, 13, x_351);
lean_ctor_set(x_365, 14, x_352);
lean_ctor_set(x_365, 15, x_364);
lean_ctor_set(x_365, 16, x_353);
lean_ctor_set(x_365, 17, x_354);
lean_ctor_set_uint8(x_365, sizeof(void*)*18, x_346);
lean_ctor_set(x_25, 0, x_365);
x_366 = lean_st_ref_set(x_1, x_25);
x_367 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_367);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_368 = x_24;
} else {
 lean_dec_ref(x_24);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_367, 15);
lean_inc_ref(x_369);
lean_dec_ref(x_367);
x_370 = lean_ctor_get(x_369, 5);
lean_inc(x_370);
lean_dec_ref(x_369);
x_371 = lean_box(0);
x_372 = lean_box(x_23);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_363);
lean_ctor_set(x_373, 1, x_372);
lean_ctor_set(x_17, 1, x_373);
lean_ctor_set(x_17, 0, x_371);
lean_inc(x_1);
x_374 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_370, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_376 = x_374;
} else {
 lean_dec_ref(x_374);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 0);
lean_inc(x_378);
lean_dec(x_375);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = lean_ctor_get(x_377, 1);
x_380 = lean_unbox(x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
lean_dec(x_1);
x_381 = lean_box(x_23);
if (lean_is_scalar(x_376)) {
 x_382 = lean_alloc_ctor(0, 1, 0);
} else {
 x_382 = x_376;
}
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_383 = lean_ctor_get(x_377, 0);
lean_inc(x_383);
lean_dec(x_377);
x_384 = lean_st_ref_take(x_1);
x_385 = lean_ctor_get(x_384, 0);
lean_inc_ref(x_385);
x_386 = lean_ctor_get(x_385, 15);
lean_inc_ref(x_386);
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_388 = x_384;
} else {
 lean_dec_ref(x_384);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 1);
lean_inc_ref(x_390);
x_391 = lean_ctor_get(x_385, 2);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_385, 3);
lean_inc_ref(x_392);
x_393 = lean_ctor_get(x_385, 4);
lean_inc_ref(x_393);
x_394 = lean_ctor_get(x_385, 5);
lean_inc_ref(x_394);
x_395 = lean_ctor_get(x_385, 6);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_385, 7);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_385, 8);
lean_inc_ref(x_397);
x_398 = lean_ctor_get_uint8(x_385, sizeof(void*)*18);
x_399 = lean_ctor_get(x_385, 9);
lean_inc(x_399);
x_400 = lean_ctor_get(x_385, 10);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_385, 11);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_385, 12);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_385, 13);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_385, 14);
lean_inc_ref(x_404);
x_405 = lean_ctor_get(x_385, 16);
lean_inc_ref(x_405);
x_406 = lean_ctor_get(x_385, 17);
lean_inc_ref(x_406);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 lean_ctor_release(x_385, 2);
 lean_ctor_release(x_385, 3);
 lean_ctor_release(x_385, 4);
 lean_ctor_release(x_385, 5);
 lean_ctor_release(x_385, 6);
 lean_ctor_release(x_385, 7);
 lean_ctor_release(x_385, 8);
 lean_ctor_release(x_385, 9);
 lean_ctor_release(x_385, 10);
 lean_ctor_release(x_385, 11);
 lean_ctor_release(x_385, 12);
 lean_ctor_release(x_385, 13);
 lean_ctor_release(x_385, 14);
 lean_ctor_release(x_385, 15);
 lean_ctor_release(x_385, 16);
 lean_ctor_release(x_385, 17);
 x_407 = x_385;
} else {
 lean_dec_ref(x_385);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_386, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_386, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_386, 2);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_386, 3);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_386, 4);
lean_inc(x_412);
x_413 = lean_ctor_get(x_386, 5);
lean_inc(x_413);
x_414 = lean_ctor_get(x_386, 6);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_386, 7);
lean_inc_ref(x_415);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 lean_ctor_release(x_386, 2);
 lean_ctor_release(x_386, 3);
 lean_ctor_release(x_386, 4);
 lean_ctor_release(x_386, 5);
 lean_ctor_release(x_386, 6);
 lean_ctor_release(x_386, 7);
 x_416 = x_386;
} else {
 lean_dec_ref(x_386);
 x_416 = lean_box(0);
}
x_417 = l_List_reverse___redArg(x_383);
x_418 = l_List_appendTR___redArg(x_413, x_417);
if (lean_is_scalar(x_416)) {
 x_419 = lean_alloc_ctor(0, 8, 0);
} else {
 x_419 = x_416;
}
lean_ctor_set(x_419, 0, x_408);
lean_ctor_set(x_419, 1, x_409);
lean_ctor_set(x_419, 2, x_410);
lean_ctor_set(x_419, 3, x_411);
lean_ctor_set(x_419, 4, x_412);
lean_ctor_set(x_419, 5, x_418);
lean_ctor_set(x_419, 6, x_414);
lean_ctor_set(x_419, 7, x_415);
if (lean_is_scalar(x_407)) {
 x_420 = lean_alloc_ctor(0, 18, 1);
} else {
 x_420 = x_407;
}
lean_ctor_set(x_420, 0, x_389);
lean_ctor_set(x_420, 1, x_390);
lean_ctor_set(x_420, 2, x_391);
lean_ctor_set(x_420, 3, x_392);
lean_ctor_set(x_420, 4, x_393);
lean_ctor_set(x_420, 5, x_394);
lean_ctor_set(x_420, 6, x_395);
lean_ctor_set(x_420, 7, x_396);
lean_ctor_set(x_420, 8, x_397);
lean_ctor_set(x_420, 9, x_399);
lean_ctor_set(x_420, 10, x_400);
lean_ctor_set(x_420, 11, x_401);
lean_ctor_set(x_420, 12, x_402);
lean_ctor_set(x_420, 13, x_403);
lean_ctor_set(x_420, 14, x_404);
lean_ctor_set(x_420, 15, x_419);
lean_ctor_set(x_420, 16, x_405);
lean_ctor_set(x_420, 17, x_406);
lean_ctor_set_uint8(x_420, sizeof(void*)*18, x_398);
if (lean_is_scalar(x_388)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_388;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_387);
x_422 = lean_st_ref_set(x_1, x_421);
lean_dec(x_1);
x_423 = lean_box(x_15);
if (lean_is_scalar(x_376)) {
 x_424 = lean_alloc_ctor(0, 1, 0);
} else {
 x_424 = x_376;
}
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; 
lean_dec(x_377);
lean_dec(x_1);
x_425 = lean_ctor_get(x_378, 0);
lean_inc(x_425);
lean_dec_ref(x_378);
if (lean_is_scalar(x_376)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_376;
}
lean_ctor_set(x_426, 0, x_425);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_1);
x_427 = lean_ctor_get(x_374, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_428 = x_374;
} else {
 lean_dec_ref(x_374);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_430 = lean_ctor_get(x_25, 1);
lean_inc(x_430);
lean_dec(x_25);
x_431 = lean_ctor_get(x_26, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_432);
x_433 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_433);
x_434 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_434);
x_435 = lean_ctor_get(x_26, 4);
lean_inc_ref(x_435);
x_436 = lean_ctor_get(x_26, 5);
lean_inc_ref(x_436);
x_437 = lean_ctor_get(x_26, 6);
lean_inc_ref(x_437);
x_438 = lean_ctor_get(x_26, 7);
lean_inc_ref(x_438);
x_439 = lean_ctor_get(x_26, 8);
lean_inc_ref(x_439);
x_440 = lean_ctor_get_uint8(x_26, sizeof(void*)*18);
x_441 = lean_ctor_get(x_26, 9);
lean_inc(x_441);
x_442 = lean_ctor_get(x_26, 10);
lean_inc_ref(x_442);
x_443 = lean_ctor_get(x_26, 11);
lean_inc_ref(x_443);
x_444 = lean_ctor_get(x_26, 12);
lean_inc_ref(x_444);
x_445 = lean_ctor_get(x_26, 13);
lean_inc_ref(x_445);
x_446 = lean_ctor_get(x_26, 14);
lean_inc_ref(x_446);
x_447 = lean_ctor_get(x_26, 16);
lean_inc_ref(x_447);
x_448 = lean_ctor_get(x_26, 17);
lean_inc_ref(x_448);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 lean_ctor_release(x_26, 8);
 lean_ctor_release(x_26, 9);
 lean_ctor_release(x_26, 10);
 lean_ctor_release(x_26, 11);
 lean_ctor_release(x_26, 12);
 lean_ctor_release(x_26, 13);
 lean_ctor_release(x_26, 14);
 lean_ctor_release(x_26, 15);
 lean_ctor_release(x_26, 16);
 lean_ctor_release(x_26, 17);
 x_449 = x_26;
} else {
 lean_dec_ref(x_26);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_27, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_27, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_452);
x_453 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_453);
x_454 = lean_ctor_get(x_27, 4);
lean_inc(x_454);
x_455 = lean_ctor_get(x_27, 6);
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_27, 7);
lean_inc_ref(x_456);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 x_457 = x_27;
} else {
 lean_dec_ref(x_27);
 x_457 = lean_box(0);
}
x_458 = lean_box(0);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(0, 8, 0);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_450);
lean_ctor_set(x_459, 1, x_451);
lean_ctor_set(x_459, 2, x_452);
lean_ctor_set(x_459, 3, x_453);
lean_ctor_set(x_459, 4, x_454);
lean_ctor_set(x_459, 5, x_458);
lean_ctor_set(x_459, 6, x_455);
lean_ctor_set(x_459, 7, x_456);
if (lean_is_scalar(x_449)) {
 x_460 = lean_alloc_ctor(0, 18, 1);
} else {
 x_460 = x_449;
}
lean_ctor_set(x_460, 0, x_431);
lean_ctor_set(x_460, 1, x_432);
lean_ctor_set(x_460, 2, x_433);
lean_ctor_set(x_460, 3, x_434);
lean_ctor_set(x_460, 4, x_435);
lean_ctor_set(x_460, 5, x_436);
lean_ctor_set(x_460, 6, x_437);
lean_ctor_set(x_460, 7, x_438);
lean_ctor_set(x_460, 8, x_439);
lean_ctor_set(x_460, 9, x_441);
lean_ctor_set(x_460, 10, x_442);
lean_ctor_set(x_460, 11, x_443);
lean_ctor_set(x_460, 12, x_444);
lean_ctor_set(x_460, 13, x_445);
lean_ctor_set(x_460, 14, x_446);
lean_ctor_set(x_460, 15, x_459);
lean_ctor_set(x_460, 16, x_447);
lean_ctor_set(x_460, 17, x_448);
lean_ctor_set_uint8(x_460, sizeof(void*)*18, x_440);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_430);
x_462 = lean_st_ref_set(x_1, x_461);
x_463 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_463);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_464 = x_24;
} else {
 lean_dec_ref(x_24);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_463, 15);
lean_inc_ref(x_465);
lean_dec_ref(x_463);
x_466 = lean_ctor_get(x_465, 5);
lean_inc(x_466);
lean_dec_ref(x_465);
x_467 = lean_box(0);
x_468 = lean_box(x_23);
if (lean_is_scalar(x_464)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_464;
}
lean_ctor_set(x_469, 0, x_458);
lean_ctor_set(x_469, 1, x_468);
lean_ctor_set(x_17, 1, x_469);
lean_ctor_set(x_17, 0, x_467);
lean_inc(x_1);
x_470 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_466, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
lean_dec(x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_ctor_get(x_473, 1);
x_476 = lean_unbox(x_475);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
lean_dec(x_473);
lean_dec(x_1);
x_477 = lean_box(x_23);
if (lean_is_scalar(x_472)) {
 x_478 = lean_alloc_ctor(0, 1, 0);
} else {
 x_478 = x_472;
}
lean_ctor_set(x_478, 0, x_477);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_479 = lean_ctor_get(x_473, 0);
lean_inc(x_479);
lean_dec(x_473);
x_480 = lean_st_ref_take(x_1);
x_481 = lean_ctor_get(x_480, 0);
lean_inc_ref(x_481);
x_482 = lean_ctor_get(x_481, 15);
lean_inc_ref(x_482);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_484 = x_480;
} else {
 lean_dec_ref(x_480);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_481, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_481, 1);
lean_inc_ref(x_486);
x_487 = lean_ctor_get(x_481, 2);
lean_inc_ref(x_487);
x_488 = lean_ctor_get(x_481, 3);
lean_inc_ref(x_488);
x_489 = lean_ctor_get(x_481, 4);
lean_inc_ref(x_489);
x_490 = lean_ctor_get(x_481, 5);
lean_inc_ref(x_490);
x_491 = lean_ctor_get(x_481, 6);
lean_inc_ref(x_491);
x_492 = lean_ctor_get(x_481, 7);
lean_inc_ref(x_492);
x_493 = lean_ctor_get(x_481, 8);
lean_inc_ref(x_493);
x_494 = lean_ctor_get_uint8(x_481, sizeof(void*)*18);
x_495 = lean_ctor_get(x_481, 9);
lean_inc(x_495);
x_496 = lean_ctor_get(x_481, 10);
lean_inc_ref(x_496);
x_497 = lean_ctor_get(x_481, 11);
lean_inc_ref(x_497);
x_498 = lean_ctor_get(x_481, 12);
lean_inc_ref(x_498);
x_499 = lean_ctor_get(x_481, 13);
lean_inc_ref(x_499);
x_500 = lean_ctor_get(x_481, 14);
lean_inc_ref(x_500);
x_501 = lean_ctor_get(x_481, 16);
lean_inc_ref(x_501);
x_502 = lean_ctor_get(x_481, 17);
lean_inc_ref(x_502);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 lean_ctor_release(x_481, 2);
 lean_ctor_release(x_481, 3);
 lean_ctor_release(x_481, 4);
 lean_ctor_release(x_481, 5);
 lean_ctor_release(x_481, 6);
 lean_ctor_release(x_481, 7);
 lean_ctor_release(x_481, 8);
 lean_ctor_release(x_481, 9);
 lean_ctor_release(x_481, 10);
 lean_ctor_release(x_481, 11);
 lean_ctor_release(x_481, 12);
 lean_ctor_release(x_481, 13);
 lean_ctor_release(x_481, 14);
 lean_ctor_release(x_481, 15);
 lean_ctor_release(x_481, 16);
 lean_ctor_release(x_481, 17);
 x_503 = x_481;
} else {
 lean_dec_ref(x_481);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_482, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_482, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_482, 2);
lean_inc_ref(x_506);
x_507 = lean_ctor_get(x_482, 3);
lean_inc_ref(x_507);
x_508 = lean_ctor_get(x_482, 4);
lean_inc(x_508);
x_509 = lean_ctor_get(x_482, 5);
lean_inc(x_509);
x_510 = lean_ctor_get(x_482, 6);
lean_inc_ref(x_510);
x_511 = lean_ctor_get(x_482, 7);
lean_inc_ref(x_511);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 lean_ctor_release(x_482, 2);
 lean_ctor_release(x_482, 3);
 lean_ctor_release(x_482, 4);
 lean_ctor_release(x_482, 5);
 lean_ctor_release(x_482, 6);
 lean_ctor_release(x_482, 7);
 x_512 = x_482;
} else {
 lean_dec_ref(x_482);
 x_512 = lean_box(0);
}
x_513 = l_List_reverse___redArg(x_479);
x_514 = l_List_appendTR___redArg(x_509, x_513);
if (lean_is_scalar(x_512)) {
 x_515 = lean_alloc_ctor(0, 8, 0);
} else {
 x_515 = x_512;
}
lean_ctor_set(x_515, 0, x_504);
lean_ctor_set(x_515, 1, x_505);
lean_ctor_set(x_515, 2, x_506);
lean_ctor_set(x_515, 3, x_507);
lean_ctor_set(x_515, 4, x_508);
lean_ctor_set(x_515, 5, x_514);
lean_ctor_set(x_515, 6, x_510);
lean_ctor_set(x_515, 7, x_511);
if (lean_is_scalar(x_503)) {
 x_516 = lean_alloc_ctor(0, 18, 1);
} else {
 x_516 = x_503;
}
lean_ctor_set(x_516, 0, x_485);
lean_ctor_set(x_516, 1, x_486);
lean_ctor_set(x_516, 2, x_487);
lean_ctor_set(x_516, 3, x_488);
lean_ctor_set(x_516, 4, x_489);
lean_ctor_set(x_516, 5, x_490);
lean_ctor_set(x_516, 6, x_491);
lean_ctor_set(x_516, 7, x_492);
lean_ctor_set(x_516, 8, x_493);
lean_ctor_set(x_516, 9, x_495);
lean_ctor_set(x_516, 10, x_496);
lean_ctor_set(x_516, 11, x_497);
lean_ctor_set(x_516, 12, x_498);
lean_ctor_set(x_516, 13, x_499);
lean_ctor_set(x_516, 14, x_500);
lean_ctor_set(x_516, 15, x_515);
lean_ctor_set(x_516, 16, x_501);
lean_ctor_set(x_516, 17, x_502);
lean_ctor_set_uint8(x_516, sizeof(void*)*18, x_494);
if (lean_is_scalar(x_484)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_484;
}
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_483);
x_518 = lean_st_ref_set(x_1, x_517);
lean_dec(x_1);
x_519 = lean_box(x_15);
if (lean_is_scalar(x_472)) {
 x_520 = lean_alloc_ctor(0, 1, 0);
} else {
 x_520 = x_472;
}
lean_ctor_set(x_520, 0, x_519);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_473);
lean_dec(x_1);
x_521 = lean_ctor_get(x_474, 0);
lean_inc(x_521);
lean_dec_ref(x_474);
if (lean_is_scalar(x_472)) {
 x_522 = lean_alloc_ctor(0, 1, 0);
} else {
 x_522 = x_472;
}
lean_ctor_set(x_522, 0, x_521);
return x_522;
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_1);
x_523 = lean_ctor_get(x_470, 0);
lean_inc(x_523);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_524 = x_470;
} else {
 lean_dec_ref(x_470);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_523);
return x_525;
}
}
}
else
{
uint8_t x_526; lean_object* x_527; 
lean_free_object(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_526 = 0;
x_527 = lean_box(x_526);
lean_ctor_set(x_12, 0, x_527);
return x_12;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
x_528 = lean_ctor_get(x_17, 0);
lean_inc(x_528);
lean_dec(x_17);
x_529 = lean_ctor_get(x_528, 15);
lean_inc_ref(x_529);
lean_dec_ref(x_528);
x_530 = lean_ctor_get(x_529, 5);
lean_inc(x_530);
lean_dec_ref(x_529);
x_531 = l_List_isEmpty___redArg(x_530);
lean_dec(x_530);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_free_object(x_12);
x_532 = lean_st_ref_get(x_1);
x_533 = lean_st_ref_take(x_1);
x_534 = lean_ctor_get(x_533, 0);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_534, 15);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_537 = x_533;
} else {
 lean_dec_ref(x_533);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_534, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_534, 1);
lean_inc_ref(x_539);
x_540 = lean_ctor_get(x_534, 2);
lean_inc_ref(x_540);
x_541 = lean_ctor_get(x_534, 3);
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_534, 4);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_534, 5);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_534, 6);
lean_inc_ref(x_544);
x_545 = lean_ctor_get(x_534, 7);
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_534, 8);
lean_inc_ref(x_546);
x_547 = lean_ctor_get_uint8(x_534, sizeof(void*)*18);
x_548 = lean_ctor_get(x_534, 9);
lean_inc(x_548);
x_549 = lean_ctor_get(x_534, 10);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_534, 11);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_534, 12);
lean_inc_ref(x_551);
x_552 = lean_ctor_get(x_534, 13);
lean_inc_ref(x_552);
x_553 = lean_ctor_get(x_534, 14);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_534, 16);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_534, 17);
lean_inc_ref(x_555);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 lean_ctor_release(x_534, 2);
 lean_ctor_release(x_534, 3);
 lean_ctor_release(x_534, 4);
 lean_ctor_release(x_534, 5);
 lean_ctor_release(x_534, 6);
 lean_ctor_release(x_534, 7);
 lean_ctor_release(x_534, 8);
 lean_ctor_release(x_534, 9);
 lean_ctor_release(x_534, 10);
 lean_ctor_release(x_534, 11);
 lean_ctor_release(x_534, 12);
 lean_ctor_release(x_534, 13);
 lean_ctor_release(x_534, 14);
 lean_ctor_release(x_534, 15);
 lean_ctor_release(x_534, 16);
 lean_ctor_release(x_534, 17);
 x_556 = x_534;
} else {
 lean_dec_ref(x_534);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_535, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_535, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_535, 2);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_535, 3);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_535, 4);
lean_inc(x_561);
x_562 = lean_ctor_get(x_535, 6);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_535, 7);
lean_inc_ref(x_563);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 lean_ctor_release(x_535, 2);
 lean_ctor_release(x_535, 3);
 lean_ctor_release(x_535, 4);
 lean_ctor_release(x_535, 5);
 lean_ctor_release(x_535, 6);
 lean_ctor_release(x_535, 7);
 x_564 = x_535;
} else {
 lean_dec_ref(x_535);
 x_564 = lean_box(0);
}
x_565 = lean_box(0);
if (lean_is_scalar(x_564)) {
 x_566 = lean_alloc_ctor(0, 8, 0);
} else {
 x_566 = x_564;
}
lean_ctor_set(x_566, 0, x_557);
lean_ctor_set(x_566, 1, x_558);
lean_ctor_set(x_566, 2, x_559);
lean_ctor_set(x_566, 3, x_560);
lean_ctor_set(x_566, 4, x_561);
lean_ctor_set(x_566, 5, x_565);
lean_ctor_set(x_566, 6, x_562);
lean_ctor_set(x_566, 7, x_563);
if (lean_is_scalar(x_556)) {
 x_567 = lean_alloc_ctor(0, 18, 1);
} else {
 x_567 = x_556;
}
lean_ctor_set(x_567, 0, x_538);
lean_ctor_set(x_567, 1, x_539);
lean_ctor_set(x_567, 2, x_540);
lean_ctor_set(x_567, 3, x_541);
lean_ctor_set(x_567, 4, x_542);
lean_ctor_set(x_567, 5, x_543);
lean_ctor_set(x_567, 6, x_544);
lean_ctor_set(x_567, 7, x_545);
lean_ctor_set(x_567, 8, x_546);
lean_ctor_set(x_567, 9, x_548);
lean_ctor_set(x_567, 10, x_549);
lean_ctor_set(x_567, 11, x_550);
lean_ctor_set(x_567, 12, x_551);
lean_ctor_set(x_567, 13, x_552);
lean_ctor_set(x_567, 14, x_553);
lean_ctor_set(x_567, 15, x_566);
lean_ctor_set(x_567, 16, x_554);
lean_ctor_set(x_567, 17, x_555);
lean_ctor_set_uint8(x_567, sizeof(void*)*18, x_547);
if (lean_is_scalar(x_537)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_537;
}
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_536);
x_569 = lean_st_ref_set(x_1, x_568);
x_570 = lean_ctor_get(x_532, 0);
lean_inc_ref(x_570);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_571 = x_532;
} else {
 lean_dec_ref(x_532);
 x_571 = lean_box(0);
}
x_572 = lean_ctor_get(x_570, 15);
lean_inc_ref(x_572);
lean_dec_ref(x_570);
x_573 = lean_ctor_get(x_572, 5);
lean_inc(x_573);
lean_dec_ref(x_572);
x_574 = lean_box(0);
x_575 = lean_box(x_531);
if (lean_is_scalar(x_571)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_571;
}
lean_ctor_set(x_576, 0, x_565);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_576);
lean_inc(x_1);
x_578 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_15, x_573, x_577, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_580 = x_578;
} else {
 lean_dec_ref(x_578);
 x_580 = lean_box(0);
}
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_579, 0);
lean_inc(x_582);
lean_dec(x_579);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; uint8_t x_584; 
x_583 = lean_ctor_get(x_581, 1);
x_584 = lean_unbox(x_583);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_581);
lean_dec(x_1);
x_585 = lean_box(x_531);
if (lean_is_scalar(x_580)) {
 x_586 = lean_alloc_ctor(0, 1, 0);
} else {
 x_586 = x_580;
}
lean_ctor_set(x_586, 0, x_585);
return x_586;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_587 = lean_ctor_get(x_581, 0);
lean_inc(x_587);
lean_dec(x_581);
x_588 = lean_st_ref_take(x_1);
x_589 = lean_ctor_get(x_588, 0);
lean_inc_ref(x_589);
x_590 = lean_ctor_get(x_589, 15);
lean_inc_ref(x_590);
x_591 = lean_ctor_get(x_588, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_592 = x_588;
} else {
 lean_dec_ref(x_588);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_589, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_589, 1);
lean_inc_ref(x_594);
x_595 = lean_ctor_get(x_589, 2);
lean_inc_ref(x_595);
x_596 = lean_ctor_get(x_589, 3);
lean_inc_ref(x_596);
x_597 = lean_ctor_get(x_589, 4);
lean_inc_ref(x_597);
x_598 = lean_ctor_get(x_589, 5);
lean_inc_ref(x_598);
x_599 = lean_ctor_get(x_589, 6);
lean_inc_ref(x_599);
x_600 = lean_ctor_get(x_589, 7);
lean_inc_ref(x_600);
x_601 = lean_ctor_get(x_589, 8);
lean_inc_ref(x_601);
x_602 = lean_ctor_get_uint8(x_589, sizeof(void*)*18);
x_603 = lean_ctor_get(x_589, 9);
lean_inc(x_603);
x_604 = lean_ctor_get(x_589, 10);
lean_inc_ref(x_604);
x_605 = lean_ctor_get(x_589, 11);
lean_inc_ref(x_605);
x_606 = lean_ctor_get(x_589, 12);
lean_inc_ref(x_606);
x_607 = lean_ctor_get(x_589, 13);
lean_inc_ref(x_607);
x_608 = lean_ctor_get(x_589, 14);
lean_inc_ref(x_608);
x_609 = lean_ctor_get(x_589, 16);
lean_inc_ref(x_609);
x_610 = lean_ctor_get(x_589, 17);
lean_inc_ref(x_610);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 lean_ctor_release(x_589, 2);
 lean_ctor_release(x_589, 3);
 lean_ctor_release(x_589, 4);
 lean_ctor_release(x_589, 5);
 lean_ctor_release(x_589, 6);
 lean_ctor_release(x_589, 7);
 lean_ctor_release(x_589, 8);
 lean_ctor_release(x_589, 9);
 lean_ctor_release(x_589, 10);
 lean_ctor_release(x_589, 11);
 lean_ctor_release(x_589, 12);
 lean_ctor_release(x_589, 13);
 lean_ctor_release(x_589, 14);
 lean_ctor_release(x_589, 15);
 lean_ctor_release(x_589, 16);
 lean_ctor_release(x_589, 17);
 x_611 = x_589;
} else {
 lean_dec_ref(x_589);
 x_611 = lean_box(0);
}
x_612 = lean_ctor_get(x_590, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_590, 1);
lean_inc(x_613);
x_614 = lean_ctor_get(x_590, 2);
lean_inc_ref(x_614);
x_615 = lean_ctor_get(x_590, 3);
lean_inc_ref(x_615);
x_616 = lean_ctor_get(x_590, 4);
lean_inc(x_616);
x_617 = lean_ctor_get(x_590, 5);
lean_inc(x_617);
x_618 = lean_ctor_get(x_590, 6);
lean_inc_ref(x_618);
x_619 = lean_ctor_get(x_590, 7);
lean_inc_ref(x_619);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 lean_ctor_release(x_590, 2);
 lean_ctor_release(x_590, 3);
 lean_ctor_release(x_590, 4);
 lean_ctor_release(x_590, 5);
 lean_ctor_release(x_590, 6);
 lean_ctor_release(x_590, 7);
 x_620 = x_590;
} else {
 lean_dec_ref(x_590);
 x_620 = lean_box(0);
}
x_621 = l_List_reverse___redArg(x_587);
x_622 = l_List_appendTR___redArg(x_617, x_621);
if (lean_is_scalar(x_620)) {
 x_623 = lean_alloc_ctor(0, 8, 0);
} else {
 x_623 = x_620;
}
lean_ctor_set(x_623, 0, x_612);
lean_ctor_set(x_623, 1, x_613);
lean_ctor_set(x_623, 2, x_614);
lean_ctor_set(x_623, 3, x_615);
lean_ctor_set(x_623, 4, x_616);
lean_ctor_set(x_623, 5, x_622);
lean_ctor_set(x_623, 6, x_618);
lean_ctor_set(x_623, 7, x_619);
if (lean_is_scalar(x_611)) {
 x_624 = lean_alloc_ctor(0, 18, 1);
} else {
 x_624 = x_611;
}
lean_ctor_set(x_624, 0, x_593);
lean_ctor_set(x_624, 1, x_594);
lean_ctor_set(x_624, 2, x_595);
lean_ctor_set(x_624, 3, x_596);
lean_ctor_set(x_624, 4, x_597);
lean_ctor_set(x_624, 5, x_598);
lean_ctor_set(x_624, 6, x_599);
lean_ctor_set(x_624, 7, x_600);
lean_ctor_set(x_624, 8, x_601);
lean_ctor_set(x_624, 9, x_603);
lean_ctor_set(x_624, 10, x_604);
lean_ctor_set(x_624, 11, x_605);
lean_ctor_set(x_624, 12, x_606);
lean_ctor_set(x_624, 13, x_607);
lean_ctor_set(x_624, 14, x_608);
lean_ctor_set(x_624, 15, x_623);
lean_ctor_set(x_624, 16, x_609);
lean_ctor_set(x_624, 17, x_610);
lean_ctor_set_uint8(x_624, sizeof(void*)*18, x_602);
if (lean_is_scalar(x_592)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_592;
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_591);
x_626 = lean_st_ref_set(x_1, x_625);
lean_dec(x_1);
x_627 = lean_box(x_15);
if (lean_is_scalar(x_580)) {
 x_628 = lean_alloc_ctor(0, 1, 0);
} else {
 x_628 = x_580;
}
lean_ctor_set(x_628, 0, x_627);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; 
lean_dec(x_581);
lean_dec(x_1);
x_629 = lean_ctor_get(x_582, 0);
lean_inc(x_629);
lean_dec_ref(x_582);
if (lean_is_scalar(x_580)) {
 x_630 = lean_alloc_ctor(0, 1, 0);
} else {
 x_630 = x_580;
}
lean_ctor_set(x_630, 0, x_629);
return x_630;
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_1);
x_631 = lean_ctor_get(x_578, 0);
lean_inc(x_631);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_632 = x_578;
} else {
 lean_dec_ref(x_578);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 1, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_631);
return x_633;
}
}
else
{
uint8_t x_634; lean_object* x_635; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_634 = 0;
x_635 = lean_box(x_634);
lean_ctor_set(x_12, 0, x_635);
return x_12;
}
}
}
}
else
{
lean_object* x_636; uint8_t x_637; 
x_636 = lean_ctor_get(x_12, 0);
lean_inc(x_636);
lean_dec(x_12);
x_637 = lean_ctor_get_uint8(x_636, sizeof(void*)*11 + 13);
lean_dec(x_636);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_638 = lean_box(x_637);
x_639 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_639, 0, x_638);
return x_639;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; 
x_640 = lean_st_ref_get(x_1);
x_641 = lean_ctor_get(x_640, 0);
lean_inc_ref(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
x_643 = lean_ctor_get(x_641, 15);
lean_inc_ref(x_643);
lean_dec_ref(x_641);
x_644 = lean_ctor_get(x_643, 5);
lean_inc(x_644);
lean_dec_ref(x_643);
x_645 = l_List_isEmpty___redArg(x_644);
lean_dec(x_644);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_646 = lean_st_ref_get(x_1);
x_647 = lean_st_ref_take(x_1);
x_648 = lean_ctor_get(x_647, 0);
lean_inc_ref(x_648);
x_649 = lean_ctor_get(x_648, 15);
lean_inc_ref(x_649);
x_650 = lean_ctor_get(x_647, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_651 = x_647;
} else {
 lean_dec_ref(x_647);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_648, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_648, 1);
lean_inc_ref(x_653);
x_654 = lean_ctor_get(x_648, 2);
lean_inc_ref(x_654);
x_655 = lean_ctor_get(x_648, 3);
lean_inc_ref(x_655);
x_656 = lean_ctor_get(x_648, 4);
lean_inc_ref(x_656);
x_657 = lean_ctor_get(x_648, 5);
lean_inc_ref(x_657);
x_658 = lean_ctor_get(x_648, 6);
lean_inc_ref(x_658);
x_659 = lean_ctor_get(x_648, 7);
lean_inc_ref(x_659);
x_660 = lean_ctor_get(x_648, 8);
lean_inc_ref(x_660);
x_661 = lean_ctor_get_uint8(x_648, sizeof(void*)*18);
x_662 = lean_ctor_get(x_648, 9);
lean_inc(x_662);
x_663 = lean_ctor_get(x_648, 10);
lean_inc_ref(x_663);
x_664 = lean_ctor_get(x_648, 11);
lean_inc_ref(x_664);
x_665 = lean_ctor_get(x_648, 12);
lean_inc_ref(x_665);
x_666 = lean_ctor_get(x_648, 13);
lean_inc_ref(x_666);
x_667 = lean_ctor_get(x_648, 14);
lean_inc_ref(x_667);
x_668 = lean_ctor_get(x_648, 16);
lean_inc_ref(x_668);
x_669 = lean_ctor_get(x_648, 17);
lean_inc_ref(x_669);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 lean_ctor_release(x_648, 2);
 lean_ctor_release(x_648, 3);
 lean_ctor_release(x_648, 4);
 lean_ctor_release(x_648, 5);
 lean_ctor_release(x_648, 6);
 lean_ctor_release(x_648, 7);
 lean_ctor_release(x_648, 8);
 lean_ctor_release(x_648, 9);
 lean_ctor_release(x_648, 10);
 lean_ctor_release(x_648, 11);
 lean_ctor_release(x_648, 12);
 lean_ctor_release(x_648, 13);
 lean_ctor_release(x_648, 14);
 lean_ctor_release(x_648, 15);
 lean_ctor_release(x_648, 16);
 lean_ctor_release(x_648, 17);
 x_670 = x_648;
} else {
 lean_dec_ref(x_648);
 x_670 = lean_box(0);
}
x_671 = lean_ctor_get(x_649, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_649, 1);
lean_inc(x_672);
x_673 = lean_ctor_get(x_649, 2);
lean_inc_ref(x_673);
x_674 = lean_ctor_get(x_649, 3);
lean_inc_ref(x_674);
x_675 = lean_ctor_get(x_649, 4);
lean_inc(x_675);
x_676 = lean_ctor_get(x_649, 6);
lean_inc_ref(x_676);
x_677 = lean_ctor_get(x_649, 7);
lean_inc_ref(x_677);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 lean_ctor_release(x_649, 2);
 lean_ctor_release(x_649, 3);
 lean_ctor_release(x_649, 4);
 lean_ctor_release(x_649, 5);
 lean_ctor_release(x_649, 6);
 lean_ctor_release(x_649, 7);
 x_678 = x_649;
} else {
 lean_dec_ref(x_649);
 x_678 = lean_box(0);
}
x_679 = lean_box(0);
if (lean_is_scalar(x_678)) {
 x_680 = lean_alloc_ctor(0, 8, 0);
} else {
 x_680 = x_678;
}
lean_ctor_set(x_680, 0, x_671);
lean_ctor_set(x_680, 1, x_672);
lean_ctor_set(x_680, 2, x_673);
lean_ctor_set(x_680, 3, x_674);
lean_ctor_set(x_680, 4, x_675);
lean_ctor_set(x_680, 5, x_679);
lean_ctor_set(x_680, 6, x_676);
lean_ctor_set(x_680, 7, x_677);
if (lean_is_scalar(x_670)) {
 x_681 = lean_alloc_ctor(0, 18, 1);
} else {
 x_681 = x_670;
}
lean_ctor_set(x_681, 0, x_652);
lean_ctor_set(x_681, 1, x_653);
lean_ctor_set(x_681, 2, x_654);
lean_ctor_set(x_681, 3, x_655);
lean_ctor_set(x_681, 4, x_656);
lean_ctor_set(x_681, 5, x_657);
lean_ctor_set(x_681, 6, x_658);
lean_ctor_set(x_681, 7, x_659);
lean_ctor_set(x_681, 8, x_660);
lean_ctor_set(x_681, 9, x_662);
lean_ctor_set(x_681, 10, x_663);
lean_ctor_set(x_681, 11, x_664);
lean_ctor_set(x_681, 12, x_665);
lean_ctor_set(x_681, 13, x_666);
lean_ctor_set(x_681, 14, x_667);
lean_ctor_set(x_681, 15, x_680);
lean_ctor_set(x_681, 16, x_668);
lean_ctor_set(x_681, 17, x_669);
lean_ctor_set_uint8(x_681, sizeof(void*)*18, x_661);
if (lean_is_scalar(x_651)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_651;
}
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_650);
x_683 = lean_st_ref_set(x_1, x_682);
x_684 = lean_ctor_get(x_646, 0);
lean_inc_ref(x_684);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_685 = x_646;
} else {
 lean_dec_ref(x_646);
 x_685 = lean_box(0);
}
x_686 = lean_ctor_get(x_684, 15);
lean_inc_ref(x_686);
lean_dec_ref(x_684);
x_687 = lean_ctor_get(x_686, 5);
lean_inc(x_687);
lean_dec_ref(x_686);
x_688 = lean_box(0);
x_689 = lean_box(x_645);
if (lean_is_scalar(x_685)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_685;
}
lean_ctor_set(x_690, 0, x_679);
lean_ctor_set(x_690, 1, x_689);
if (lean_is_scalar(x_642)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_642;
}
lean_ctor_set(x_691, 0, x_688);
lean_ctor_set(x_691, 1, x_690);
lean_inc(x_1);
x_692 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_637, x_687, x_691, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 x_694 = x_692;
} else {
 lean_dec_ref(x_692);
 x_694 = lean_box(0);
}
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_693, 0);
lean_inc(x_696);
lean_dec(x_693);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; uint8_t x_698; 
x_697 = lean_ctor_get(x_695, 1);
x_698 = lean_unbox(x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
lean_dec(x_695);
lean_dec(x_1);
x_699 = lean_box(x_645);
if (lean_is_scalar(x_694)) {
 x_700 = lean_alloc_ctor(0, 1, 0);
} else {
 x_700 = x_694;
}
lean_ctor_set(x_700, 0, x_699);
return x_700;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_701 = lean_ctor_get(x_695, 0);
lean_inc(x_701);
lean_dec(x_695);
x_702 = lean_st_ref_take(x_1);
x_703 = lean_ctor_get(x_702, 0);
lean_inc_ref(x_703);
x_704 = lean_ctor_get(x_703, 15);
lean_inc_ref(x_704);
x_705 = lean_ctor_get(x_702, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_706 = x_702;
} else {
 lean_dec_ref(x_702);
 x_706 = lean_box(0);
}
x_707 = lean_ctor_get(x_703, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_703, 1);
lean_inc_ref(x_708);
x_709 = lean_ctor_get(x_703, 2);
lean_inc_ref(x_709);
x_710 = lean_ctor_get(x_703, 3);
lean_inc_ref(x_710);
x_711 = lean_ctor_get(x_703, 4);
lean_inc_ref(x_711);
x_712 = lean_ctor_get(x_703, 5);
lean_inc_ref(x_712);
x_713 = lean_ctor_get(x_703, 6);
lean_inc_ref(x_713);
x_714 = lean_ctor_get(x_703, 7);
lean_inc_ref(x_714);
x_715 = lean_ctor_get(x_703, 8);
lean_inc_ref(x_715);
x_716 = lean_ctor_get_uint8(x_703, sizeof(void*)*18);
x_717 = lean_ctor_get(x_703, 9);
lean_inc(x_717);
x_718 = lean_ctor_get(x_703, 10);
lean_inc_ref(x_718);
x_719 = lean_ctor_get(x_703, 11);
lean_inc_ref(x_719);
x_720 = lean_ctor_get(x_703, 12);
lean_inc_ref(x_720);
x_721 = lean_ctor_get(x_703, 13);
lean_inc_ref(x_721);
x_722 = lean_ctor_get(x_703, 14);
lean_inc_ref(x_722);
x_723 = lean_ctor_get(x_703, 16);
lean_inc_ref(x_723);
x_724 = lean_ctor_get(x_703, 17);
lean_inc_ref(x_724);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 lean_ctor_release(x_703, 2);
 lean_ctor_release(x_703, 3);
 lean_ctor_release(x_703, 4);
 lean_ctor_release(x_703, 5);
 lean_ctor_release(x_703, 6);
 lean_ctor_release(x_703, 7);
 lean_ctor_release(x_703, 8);
 lean_ctor_release(x_703, 9);
 lean_ctor_release(x_703, 10);
 lean_ctor_release(x_703, 11);
 lean_ctor_release(x_703, 12);
 lean_ctor_release(x_703, 13);
 lean_ctor_release(x_703, 14);
 lean_ctor_release(x_703, 15);
 lean_ctor_release(x_703, 16);
 lean_ctor_release(x_703, 17);
 x_725 = x_703;
} else {
 lean_dec_ref(x_703);
 x_725 = lean_box(0);
}
x_726 = lean_ctor_get(x_704, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_704, 1);
lean_inc(x_727);
x_728 = lean_ctor_get(x_704, 2);
lean_inc_ref(x_728);
x_729 = lean_ctor_get(x_704, 3);
lean_inc_ref(x_729);
x_730 = lean_ctor_get(x_704, 4);
lean_inc(x_730);
x_731 = lean_ctor_get(x_704, 5);
lean_inc(x_731);
x_732 = lean_ctor_get(x_704, 6);
lean_inc_ref(x_732);
x_733 = lean_ctor_get(x_704, 7);
lean_inc_ref(x_733);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 lean_ctor_release(x_704, 2);
 lean_ctor_release(x_704, 3);
 lean_ctor_release(x_704, 4);
 lean_ctor_release(x_704, 5);
 lean_ctor_release(x_704, 6);
 lean_ctor_release(x_704, 7);
 x_734 = x_704;
} else {
 lean_dec_ref(x_704);
 x_734 = lean_box(0);
}
x_735 = l_List_reverse___redArg(x_701);
x_736 = l_List_appendTR___redArg(x_731, x_735);
if (lean_is_scalar(x_734)) {
 x_737 = lean_alloc_ctor(0, 8, 0);
} else {
 x_737 = x_734;
}
lean_ctor_set(x_737, 0, x_726);
lean_ctor_set(x_737, 1, x_727);
lean_ctor_set(x_737, 2, x_728);
lean_ctor_set(x_737, 3, x_729);
lean_ctor_set(x_737, 4, x_730);
lean_ctor_set(x_737, 5, x_736);
lean_ctor_set(x_737, 6, x_732);
lean_ctor_set(x_737, 7, x_733);
if (lean_is_scalar(x_725)) {
 x_738 = lean_alloc_ctor(0, 18, 1);
} else {
 x_738 = x_725;
}
lean_ctor_set(x_738, 0, x_707);
lean_ctor_set(x_738, 1, x_708);
lean_ctor_set(x_738, 2, x_709);
lean_ctor_set(x_738, 3, x_710);
lean_ctor_set(x_738, 4, x_711);
lean_ctor_set(x_738, 5, x_712);
lean_ctor_set(x_738, 6, x_713);
lean_ctor_set(x_738, 7, x_714);
lean_ctor_set(x_738, 8, x_715);
lean_ctor_set(x_738, 9, x_717);
lean_ctor_set(x_738, 10, x_718);
lean_ctor_set(x_738, 11, x_719);
lean_ctor_set(x_738, 12, x_720);
lean_ctor_set(x_738, 13, x_721);
lean_ctor_set(x_738, 14, x_722);
lean_ctor_set(x_738, 15, x_737);
lean_ctor_set(x_738, 16, x_723);
lean_ctor_set(x_738, 17, x_724);
lean_ctor_set_uint8(x_738, sizeof(void*)*18, x_716);
if (lean_is_scalar(x_706)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_706;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_705);
x_740 = lean_st_ref_set(x_1, x_739);
lean_dec(x_1);
x_741 = lean_box(x_637);
if (lean_is_scalar(x_694)) {
 x_742 = lean_alloc_ctor(0, 1, 0);
} else {
 x_742 = x_694;
}
lean_ctor_set(x_742, 0, x_741);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; 
lean_dec(x_695);
lean_dec(x_1);
x_743 = lean_ctor_get(x_696, 0);
lean_inc(x_743);
lean_dec_ref(x_696);
if (lean_is_scalar(x_694)) {
 x_744 = lean_alloc_ctor(0, 1, 0);
} else {
 x_744 = x_694;
}
lean_ctor_set(x_744, 0, x_743);
return x_744;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_1);
x_745 = lean_ctor_get(x_692, 0);
lean_inc(x_745);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 x_746 = x_692;
} else {
 lean_dec_ref(x_692);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 1, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_745);
return x_747;
}
}
else
{
uint8_t x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_642);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_748 = 0;
x_749 = lean_box(x_748);
x_750 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_750, 0, x_749);
return x_750;
}
}
}
}
else
{
uint8_t x_751; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_751 = !lean_is_exclusive(x_12);
if (x_751 == 0)
{
return x_12;
}
else
{
lean_object* x_752; lean_object* x_753; 
x_752 = lean_ctor_get(x_12, 0);
lean_inc(x_752);
lean_dec(x_12);
x_753 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_753, 0, x_752);
return x_753;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_lookahead(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_1);
x_18 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_18;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations = _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations);
l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
