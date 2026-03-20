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
lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mkAction();
lean_object* l_Lean_Meta_Grind_Action_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_splitNext___boxed, .m_arity = 15, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_assertAll___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_instantiate___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "of_lookahead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 178, 46, 74, 114, 9, 243, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(10000u);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(lean_object* v___f_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0));
v___x_21_ = l_Lean_Meta_Grind_Action_orElse(v___x_20_, v___f_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(lean_object* v___f_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(v___f_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(lean_object* v_a_37_, lean_object* v___f_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_Action_orElse(v_a_37_, v___f_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(lean_object* v_a_53_, lean_object* v___f_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(v_a_53_, v___f_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(lean_object* v___f_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(10000u);
v___x_84_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_83_, v___f_69_, v___y_70_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(lean_object* v___f_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(v___f_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___y_87_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(lean_object* v___f_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0));
v___x_116_ = l_Lean_Meta_Grind_Action_andThen(v___x_115_, v___f_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(lean_object* v___f_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(v___f_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(lean_object* v___x_132_, lean_object* v___f_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_Action_andThen(v___x_132_, v___f_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(lean_object* v___x_148_, lean_object* v___f_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(v___x_148_, v___f_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object* v_goal_167_, lean_object* v_generation_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Grind_Solvers_mkAction();
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
v___f_181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1));
v___f_182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed), 15, 2);
lean_closure_set(v___f_182_, 0, v_a_180_);
lean_closure_set(v___f_182_, 1, v___f_181_);
v___f_183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed), 14, 1);
lean_closure_set(v___f_183_, 0, v___f_182_);
v___f_184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed), 14, 1);
lean_closure_set(v___f_184_, 0, v___f_183_);
v___x_185_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_185_, 0, v_generation_168_);
v___f_186_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed), 15, 2);
lean_closure_set(v___f_186_, 0, v___x_185_);
lean_closure_set(v___f_186_, 1, v___f_184_);
lean_inc_ref(v_goal_167_);
v___x_187_ = l_Lean_Meta_Grind_Action_run(v_goal_167_, v___f_186_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_214_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_214_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_214_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_214_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
if (lean_obj_tag(v_a_188_) == 0)
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_dec_ref(v_a_188_);
lean_dec_ref(v_goal_167_);
v___x_192_ = lean_box(0);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v_gs_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_213_; 
v_gs_196_ = lean_ctor_get(v_a_188_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_188_);
if (v_isSharedCheck_213_ == 0)
{
v___x_198_ = v_a_188_;
v_isShared_199_ = v_isSharedCheck_213_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_gs_196_);
lean_dec(v_a_188_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_213_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
if (lean_obj_tag(v_gs_196_) == 1)
{
lean_object* v_head_200_; lean_object* v___x_202_; 
lean_dec_ref(v_goal_167_);
v_head_200_ = lean_ctor_get(v_gs_196_, 0);
lean_inc(v_head_200_);
lean_dec_ref(v_gs_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_head_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_head_200_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_202_);
v___x_204_ = v___x_190_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v_gs_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_goal_167_);
v___x_208_ = v___x_198_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_goal_167_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_208_);
v___x_210_ = v___x_190_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_goal_167_);
v_a_215_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_187_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_187_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_177_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec(v_generation_168_);
lean_dec_ref(v_goal_167_);
v_a_223_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_235_ == 0)
{
v___x_225_ = v___x_179_;
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_179_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_ref_227_ = lean_ctor_get(v_a_176_, 5);
lean_inc(v_ref_227_);
lean_dec_ref(v_a_176_);
v___x_228_ = lean_io_error_to_string(v_a_223_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_ref_227_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_231_);
v___x_233_ = v___x_225_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(lean_object* v_goal_236_, lean_object* v_generation_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v_goal_236_, v_generation_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(lean_object* v_e_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = l_Lean_Expr_hasMVar(v_e_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_e_249_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v_mctx_255_; lean_object* v___x_256_; lean_object* v_fst_257_; lean_object* v_snd_258_; lean_object* v___x_259_; lean_object* v_cache_260_; lean_object* v_zetaDeltaFVarIds_261_; lean_object* v_postponed_262_; lean_object* v_diag_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_272_; 
v___x_254_ = lean_st_ref_get(v___y_250_);
v_mctx_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_mctx_255_);
lean_dec(v___x_254_);
v___x_256_ = l_Lean_instantiateMVarsCore(v_mctx_255_, v_e_249_);
v_fst_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_fst_257_);
v_snd_258_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_snd_258_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_st_ref_take(v___y_250_);
v_cache_260_ = lean_ctor_get(v___x_259_, 1);
v_zetaDeltaFVarIds_261_ = lean_ctor_get(v___x_259_, 2);
v_postponed_262_ = lean_ctor_get(v___x_259_, 3);
v_diag_263_ = lean_ctor_get(v___x_259_, 4);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_273_);
v___x_265_ = v___x_259_;
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_diag_263_);
lean_inc(v_postponed_262_);
lean_inc(v_zetaDeltaFVarIds_261_);
lean_inc(v_cache_260_);
lean_dec(v___x_259_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v_snd_258_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_snd_258_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_cache_260_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_zetaDeltaFVarIds_261_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_postponed_262_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_diag_263_);
v___x_268_ = v_reuseFailAlloc_271_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_st_ref_set(v___y_250_, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_fst_257_);
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg___boxed(lean_object* v_e_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_274_, v___y_275_);
lean_dec(v___y_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(lean_object* v_e_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_278_, v___y_286_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___boxed(lean_object* v_e_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(v_e_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec(v___y_292_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(lean_object* v___y_304_, lean_object* v_mctx_305_, lean_object* v_cache_306_, lean_object* v_a_x3f_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_zetaDeltaFVarIds_310_; lean_object* v_postponed_311_; lean_object* v_diag_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
v___x_309_ = lean_st_ref_take(v___y_304_);
v_zetaDeltaFVarIds_310_ = lean_ctor_get(v___x_309_, 2);
v_postponed_311_ = lean_ctor_get(v___x_309_, 3);
v_diag_312_ = lean_ctor_get(v___x_309_, 4);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_323_ = lean_ctor_get(v___x_309_, 1);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v___x_309_, 0);
lean_dec(v_unused_324_);
v___x_314_ = v___x_309_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_diag_312_);
lean_inc(v_postponed_311_);
lean_inc(v_zetaDeltaFVarIds_310_);
lean_dec(v___x_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_cache_306_);
lean_ctor_set(v___x_314_, 0, v_mctx_305_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_mctx_305_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_cache_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_zetaDeltaFVarIds_310_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_postponed_311_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_diag_312_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_st_ref_set(v___y_304_, v___x_317_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0___boxed(lean_object* v___y_325_, lean_object* v_mctx_326_, lean_object* v_cache_327_, lean_object* v_a_x3f_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_325_, v_mctx_326_, v_cache_327_, v_a_x3f_328_);
lean_dec(v_a_x3f_328_);
lean_dec(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_mctx_345_; lean_object* v_cache_346_; lean_object* v___x_347_; 
v___x_343_ = lean_st_ref_get(v___y_339_);
v___x_344_ = lean_st_ref_get(v___y_339_);
v_mctx_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_mctx_345_);
lean_dec(v___x_343_);
v_cache_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc_ref(v_cache_346_);
lean_dec(v___x_344_);
lean_inc(v___y_339_);
v___x_347_ = lean_apply_11(v_x_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, lean_box(0));
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_364_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_364_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_364_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_364_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
lean_inc(v_a_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_363_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v___x_354_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_345_, v_cache_346_, v___x_353_);
lean_dec_ref(v___x_353_);
lean_dec(v___y_339_);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_362_);
v___x_356_ = v___x_354_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_dec(v___x_354_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v_a_348_);
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_348_);
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
else
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_347_);
v___x_366_ = lean_box(0);
v___x_367_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_345_, v_cache_346_, v___x_366_);
lean_dec(v___y_339_);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_375_);
v___x_369_ = v___x_367_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_dec(v___x_367_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 1);
lean_ctor_set(v___x_369_, 0, v_a_365_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_365_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___boxed(lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(lean_object* v_00_u03b1_389_, lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___boxed(lean_object* v_00_u03b1_403_, lean_object* v_x_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(v_00_u03b1_403_, v_x_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_options_423_; uint8_t v_hasTrace_424_; 
v_options_423_ = lean_ctor_get(v___y_421_, 2);
v_hasTrace_424_ = lean_ctor_get_uint8(v_options_423_, sizeof(void*)*1);
if (v_hasTrace_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_cls_420_);
v___x_425_ = lean_box(v_hasTrace_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v_inheritedTraceOptions_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_inheritedTraceOptions_427_ = lean_ctor_get(v___y_421_, 13);
v___x_428_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_429_ = l_Lean_Name_append(v___x_428_, v_cls_420_);
v___x_430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_427_, v_options_423_, v___x_429_);
lean_dec(v___x_429_);
v___x_431_ = lean_box(v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_433_, v___y_434_);
lean_dec_ref(v___y_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_437_, v___y_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object* v_mvarId_465_, lean_object* v_e_466_, lean_object* v_toGoalState_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MVarId_getTag(v_mvarId_465_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___x_481_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_472_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
lean_inc_ref(v_e_466_);
v___x_483_ = l_Lean_mkNot(v_e_466_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
v___x_484_ = l_Lean_mkArrow(v___x_483_, v_a_482_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
lean_inc_ref(v___y_474_);
v___x_486_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_485_, v_a_480_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_466_, v___y_468_);
lean_dec_ref(v_e_466_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v_nextDeclIdx_490_; lean_object* v_canon_491_; lean_object* v_enodeMap_492_; lean_object* v_exprs_493_; lean_object* v_parents_494_; lean_object* v_congrTable_495_; lean_object* v_appMap_496_; lean_object* v_indicesFound_497_; uint8_t v_inconsistent_498_; lean_object* v_nextIdx_499_; lean_object* v_newRawFacts_500_; lean_object* v_facts_501_; lean_object* v_extThms_502_; lean_object* v_ematch_503_; lean_object* v_inj_504_; lean_object* v_split_505_; lean_object* v_clean_506_; lean_object* v_sstates_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_545_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v_nextDeclIdx_490_ = lean_ctor_get(v_toGoalState_467_, 0);
v_canon_491_ = lean_ctor_get(v_toGoalState_467_, 1);
v_enodeMap_492_ = lean_ctor_get(v_toGoalState_467_, 2);
v_exprs_493_ = lean_ctor_get(v_toGoalState_467_, 3);
v_parents_494_ = lean_ctor_get(v_toGoalState_467_, 4);
v_congrTable_495_ = lean_ctor_get(v_toGoalState_467_, 5);
v_appMap_496_ = lean_ctor_get(v_toGoalState_467_, 6);
v_indicesFound_497_ = lean_ctor_get(v_toGoalState_467_, 7);
v_inconsistent_498_ = lean_ctor_get_uint8(v_toGoalState_467_, sizeof(void*)*18);
v_nextIdx_499_ = lean_ctor_get(v_toGoalState_467_, 9);
v_newRawFacts_500_ = lean_ctor_get(v_toGoalState_467_, 10);
v_facts_501_ = lean_ctor_get(v_toGoalState_467_, 11);
v_extThms_502_ = lean_ctor_get(v_toGoalState_467_, 12);
v_ematch_503_ = lean_ctor_get(v_toGoalState_467_, 13);
v_inj_504_ = lean_ctor_get(v_toGoalState_467_, 14);
v_split_505_ = lean_ctor_get(v_toGoalState_467_, 15);
v_clean_506_ = lean_ctor_get(v_toGoalState_467_, 16);
v_sstates_507_ = lean_ctor_get(v_toGoalState_467_, 17);
v_isSharedCheck_545_ = !lean_is_exclusive(v_toGoalState_467_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_toGoalState_467_, 8);
lean_dec(v_unused_546_);
v___x_509_ = v_toGoalState_467_;
v_isShared_510_ = v_isSharedCheck_545_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_sstates_507_);
lean_inc(v_clean_506_);
lean_inc(v_split_505_);
lean_inc(v_inj_504_);
lean_inc(v_ematch_503_);
lean_inc(v_extThms_502_);
lean_inc(v_facts_501_);
lean_inc(v_newRawFacts_500_);
lean_inc(v_nextIdx_499_);
lean_inc(v_indicesFound_497_);
lean_inc(v_appMap_496_);
lean_inc(v_congrTable_495_);
lean_inc(v_parents_494_);
lean_inc(v_exprs_493_);
lean_inc(v_enodeMap_492_);
lean_inc(v_canon_491_);
lean_inc(v_nextDeclIdx_490_);
lean_dec(v_toGoalState_467_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_545_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0));
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 8, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_nextDeclIdx_490_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_canon_491_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_enodeMap_492_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_exprs_493_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_parents_494_);
lean_ctor_set(v_reuseFailAlloc_544_, 5, v_congrTable_495_);
lean_ctor_set(v_reuseFailAlloc_544_, 6, v_appMap_496_);
lean_ctor_set(v_reuseFailAlloc_544_, 7, v_indicesFound_497_);
lean_ctor_set(v_reuseFailAlloc_544_, 8, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_544_, 9, v_nextIdx_499_);
lean_ctor_set(v_reuseFailAlloc_544_, 10, v_newRawFacts_500_);
lean_ctor_set(v_reuseFailAlloc_544_, 11, v_facts_501_);
lean_ctor_set(v_reuseFailAlloc_544_, 12, v_extThms_502_);
lean_ctor_set(v_reuseFailAlloc_544_, 13, v_ematch_503_);
lean_ctor_set(v_reuseFailAlloc_544_, 14, v_inj_504_);
lean_ctor_set(v_reuseFailAlloc_544_, 15, v_split_505_);
lean_ctor_set(v_reuseFailAlloc_544_, 16, v_clean_506_);
lean_ctor_set(v_reuseFailAlloc_544_, 17, v_sstates_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_544_, sizeof(void*)*18, v_inconsistent_498_);
v___x_513_ = v_reuseFailAlloc_544_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = l_Lean_Expr_mvarId_x21(v_a_487_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
lean_inc(v___y_475_);
v___x_516_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_515_, v_a_489_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_535_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_535_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
if (lean_obj_tag(v_a_517_) == 0)
{
lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_519_);
v___x_521_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_487_, v___y_475_);
lean_dec(v___y_475_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_dec_ref(v_a_517_);
lean_dec(v_a_487_);
lean_dec(v___y_475_);
v___x_531_ = lean_box(0);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_531_);
v___x_533_ = v___x_519_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_a_487_);
lean_dec(v___y_475_);
v_a_536_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_516_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_516_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_487_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v_toGoalState_467_);
v_a_547_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_488_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_488_);
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
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v_toGoalState_467_);
lean_dec_ref(v_e_466_);
v_a_555_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_486_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_486_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_a_480_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v_toGoalState_467_);
lean_dec_ref(v_e_466_);
v_a_563_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_484_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_484_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_a_480_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v_toGoalState_467_);
lean_dec_ref(v_e_466_);
v_a_571_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_481_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_481_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v_toGoalState_467_);
lean_dec_ref(v_e_466_);
v_a_579_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_479_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_479_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* v_mvarId_587_, lean_object* v_e_588_, lean_object* v_toGoalState_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_587_, v_e_588_, v_toGoalState_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_590_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(lean_object* v_msgData_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; lean_object* v_env_609_; lean_object* v___x_610_; lean_object* v_mctx_611_; lean_object* v_lctx_612_; lean_object* v_options_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_608_ = lean_st_ref_get(v___y_606_);
v_env_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_609_);
lean_dec(v___x_608_);
v___x_610_ = lean_st_ref_get(v___y_604_);
v_mctx_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_mctx_611_);
lean_dec(v___x_610_);
v_lctx_612_ = lean_ctor_get(v___y_603_, 2);
v_options_613_ = lean_ctor_get(v___y_605_, 2);
lean_inc_ref(v_options_613_);
lean_inc_ref(v_lctx_612_);
v___x_614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_614_, 0, v_env_609_);
lean_ctor_set(v___x_614_, 1, v_mctx_611_);
lean_ctor_set(v___x_614_, 2, v_lctx_612_);
lean_ctor_set(v___x_614_, 3, v_options_613_);
v___x_615_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_msgData_602_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3___boxed(lean_object* v_msgData_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(v_msgData_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_624_; double v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_float_of_nat(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(lean_object* v_cls_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_ref_636_; lean_object* v___x_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_682_; 
v_ref_636_ = lean_ctor_get(v___y_633_, 5);
v___x_637_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3_spec__3(v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_682_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v_traceState_643_; lean_object* v_env_644_; lean_object* v_nextMacroScope_645_; lean_object* v_ngen_646_; lean_object* v_auxDeclNGen_647_; lean_object* v_cache_648_; lean_object* v_messages_649_; lean_object* v_infoState_650_; lean_object* v_snapshotTasks_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_681_; 
v___x_642_ = lean_st_ref_take(v___y_634_);
v_traceState_643_ = lean_ctor_get(v___x_642_, 4);
v_env_644_ = lean_ctor_get(v___x_642_, 0);
v_nextMacroScope_645_ = lean_ctor_get(v___x_642_, 1);
v_ngen_646_ = lean_ctor_get(v___x_642_, 2);
v_auxDeclNGen_647_ = lean_ctor_get(v___x_642_, 3);
v_cache_648_ = lean_ctor_get(v___x_642_, 5);
v_messages_649_ = lean_ctor_get(v___x_642_, 6);
v_infoState_650_ = lean_ctor_get(v___x_642_, 7);
v_snapshotTasks_651_ = lean_ctor_get(v___x_642_, 8);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_681_ == 0)
{
v___x_653_ = v___x_642_;
v_isShared_654_ = v_isSharedCheck_681_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snapshotTasks_651_);
lean_inc(v_infoState_650_);
lean_inc(v_messages_649_);
lean_inc(v_cache_648_);
lean_inc(v_traceState_643_);
lean_inc(v_auxDeclNGen_647_);
lean_inc(v_ngen_646_);
lean_inc(v_nextMacroScope_645_);
lean_inc(v_env_644_);
lean_dec(v___x_642_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_681_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint64_t v_tid_655_; lean_object* v_traces_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_680_; 
v_tid_655_ = lean_ctor_get_uint64(v_traceState_643_, sizeof(void*)*1);
v_traces_656_ = lean_ctor_get(v_traceState_643_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_traceState_643_);
if (v_isSharedCheck_680_ == 0)
{
v___x_658_ = v_traceState_643_;
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_traces_656_);
lean_dec(v_traceState_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; double v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__0);
v___x_662_ = 0;
v___x_663_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__1));
v___x_664_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_664_, 0, v_cls_629_);
lean_ctor_set(v___x_664_, 1, v___x_660_);
lean_ctor_set(v___x_664_, 2, v___x_663_);
lean_ctor_set_float(v___x_664_, sizeof(void*)*3, v___x_661_);
lean_ctor_set_float(v___x_664_, sizeof(void*)*3 + 8, v___x_661_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*3 + 16, v___x_662_);
v___x_665_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___closed__2));
v___x_666_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v_a_638_);
lean_ctor_set(v___x_666_, 2, v___x_665_);
lean_inc(v_ref_636_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_ref_636_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_PersistentArray_push___redArg(v_traces_656_, v___x_667_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_668_);
v___x_670_ = v___x_658_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_668_);
lean_ctor_set_uint64(v_reuseFailAlloc_679_, sizeof(void*)*1, v_tid_655_);
v___x_670_ = v_reuseFailAlloc_679_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_670_);
v___x_672_ = v___x_653_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_env_644_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_nextMacroScope_645_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_ngen_646_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_auxDeclNGen_647_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v_cache_648_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_messages_649_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_infoState_650_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_snapshotTasks_651_);
v___x_672_ = v_reuseFailAlloc_678_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_st_ref_set(v___y_634_, v___x_672_);
v___x_674_ = lean_box(0);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_674_);
v___x_676_ = v___x_640_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg___boxed(lean_object* v_cls_683_, lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(v_cls_683_, v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_box(0);
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_700_ = l_Lean_mkConst(v___x_699_, v___x_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v_config_767_; lean_object* v_simp_768_; lean_object* v_simpMethods_769_; lean_object* v_anchorRefs_x3f_770_; uint8_t v_reportMVarIssue_771_; lean_object* v_splitSource_772_; lean_object* v_symPrios_773_; lean_object* v_extensions_774_; uint8_t v_debug_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_904_; 
v_config_767_ = lean_ctor_get(v_a_716_, 2);
v_simp_768_ = lean_ctor_get(v_a_716_, 0);
v_simpMethods_769_ = lean_ctor_get(v_a_716_, 1);
v_anchorRefs_x3f_770_ = lean_ctor_get(v_a_716_, 3);
v_reportMVarIssue_771_ = lean_ctor_get_uint8(v_a_716_, sizeof(void*)*7 + 1);
v_splitSource_772_ = lean_ctor_get(v_a_716_, 4);
v_symPrios_773_ = lean_ctor_get(v_a_716_, 5);
v_extensions_774_ = lean_ctor_get(v_a_716_, 6);
v_debug_775_ = lean_ctor_get_uint8(v_a_716_, sizeof(void*)*7 + 2);
v_isSharedCheck_904_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_904_ == 0)
{
v___x_777_ = v_a_716_;
v_isShared_778_ = v_isSharedCheck_904_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_extensions_774_);
lean_inc(v_symPrios_773_);
lean_inc(v_splitSource_772_);
lean_inc(v_anchorRefs_x3f_770_);
lean_inc(v_config_767_);
lean_inc(v_simpMethods_769_);
lean_inc(v_simp_768_);
lean_dec(v_a_716_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_904_;
goto v_resetjp_776_;
}
v___jp_725_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_713_);
v___x_738_ = l_Lean_mkAppB(v___x_737_, v_e_713_, v___y_726_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
v___x_739_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_713_, v___x_738_, v___y_727_, v___y_729_, v___y_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_739_);
v___x_740_ = lean_grind_process_new_facts(v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_740_, 0);
lean_dec(v_unused_750_);
v___x_742_ = v___x_740_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_dec(v___x_740_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = 1;
v___x_745_ = lean_box(v___x_744_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_740_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_740_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec(v___y_727_);
v_a_759_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_739_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_739_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v_resetjp_776_:
{
uint8_t v_trace_779_; uint8_t v_markInstances_780_; uint8_t v_lax_781_; uint8_t v_suggestions_782_; uint8_t v_locals_783_; lean_object* v_splits_784_; lean_object* v_ematch_785_; lean_object* v_gen_786_; lean_object* v_instances_787_; uint8_t v_matchEqs_788_; uint8_t v_splitMatch_789_; uint8_t v_splitIte_790_; uint8_t v_splitIndPred_791_; uint8_t v_splitImp_792_; lean_object* v_canonHeartbeats_793_; uint8_t v_ext_794_; uint8_t v_extAll_795_; uint8_t v_etaStruct_796_; uint8_t v_funext_797_; uint8_t v_lookahead_798_; uint8_t v_verbose_799_; uint8_t v_clean_800_; uint8_t v_mbtc_801_; uint8_t v_zetaDelta_802_; uint8_t v_zeta_803_; uint8_t v_ring_804_; lean_object* v_ringSteps_805_; uint8_t v_linarith_806_; uint8_t v_lia_807_; uint8_t v_ac_808_; lean_object* v_acSteps_809_; lean_object* v_exp_810_; uint8_t v_abstractProof_811_; uint8_t v_inj_812_; uint8_t v_order_813_; lean_object* v_min_814_; lean_object* v_detailed_815_; uint8_t v_useSorry_816_; uint8_t v_revert_817_; uint8_t v_funCC_818_; uint8_t v_reducible_819_; lean_object* v_maxSuggestions_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_903_; 
v_trace_779_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11);
v_markInstances_780_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 1);
v_lax_781_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 2);
v_suggestions_782_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 3);
v_locals_783_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 4);
v_splits_784_ = lean_ctor_get(v_config_767_, 0);
v_ematch_785_ = lean_ctor_get(v_config_767_, 1);
v_gen_786_ = lean_ctor_get(v_config_767_, 2);
v_instances_787_ = lean_ctor_get(v_config_767_, 3);
v_matchEqs_788_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 5);
v_splitMatch_789_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 6);
v_splitIte_790_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 7);
v_splitIndPred_791_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 8);
v_splitImp_792_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 9);
v_canonHeartbeats_793_ = lean_ctor_get(v_config_767_, 4);
v_ext_794_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 10);
v_extAll_795_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 11);
v_etaStruct_796_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 12);
v_funext_797_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 13);
v_lookahead_798_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 14);
v_verbose_799_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 15);
v_clean_800_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 16);
v_mbtc_801_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 18);
v_zetaDelta_802_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 19);
v_zeta_803_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 20);
v_ring_804_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 21);
v_ringSteps_805_ = lean_ctor_get(v_config_767_, 5);
v_linarith_806_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 22);
v_lia_807_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 23);
v_ac_808_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 24);
v_acSteps_809_ = lean_ctor_get(v_config_767_, 6);
v_exp_810_ = lean_ctor_get(v_config_767_, 7);
v_abstractProof_811_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 25);
v_inj_812_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 26);
v_order_813_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 27);
v_min_814_ = lean_ctor_get(v_config_767_, 8);
v_detailed_815_ = lean_ctor_get(v_config_767_, 9);
v_useSorry_816_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 28);
v_revert_817_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 29);
v_funCC_818_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 30);
v_reducible_819_ = lean_ctor_get_uint8(v_config_767_, sizeof(void*)*11 + 31);
v_maxSuggestions_820_ = lean_ctor_get(v_config_767_, 10);
v_isSharedCheck_903_ = !lean_is_exclusive(v_config_767_);
if (v_isSharedCheck_903_ == 0)
{
v___x_822_ = v_config_767_;
v_isShared_823_ = v_isSharedCheck_903_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_maxSuggestions_820_);
lean_inc(v_detailed_815_);
lean_inc(v_min_814_);
lean_inc(v_exp_810_);
lean_inc(v_acSteps_809_);
lean_inc(v_ringSteps_805_);
lean_inc(v_canonHeartbeats_793_);
lean_inc(v_instances_787_);
lean_inc(v_gen_786_);
lean_inc(v_ematch_785_);
lean_inc(v_splits_784_);
lean_dec(v_config_767_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_903_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v_cls_873_; uint8_t v___x_874_; lean_object* v___x_876_; 
v_cls_873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_874_ = 1;
if (v_isShared_823_ == 0)
{
v___x_876_ = v___x_822_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 11, 32);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_splits_784_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_ematch_785_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_gen_786_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_instances_787_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_canonHeartbeats_793_);
lean_ctor_set(v_reuseFailAlloc_902_, 5, v_ringSteps_805_);
lean_ctor_set(v_reuseFailAlloc_902_, 6, v_acSteps_809_);
lean_ctor_set(v_reuseFailAlloc_902_, 7, v_exp_810_);
lean_ctor_set(v_reuseFailAlloc_902_, 8, v_min_814_);
lean_ctor_set(v_reuseFailAlloc_902_, 9, v_detailed_815_);
lean_ctor_set(v_reuseFailAlloc_902_, 10, v_maxSuggestions_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11, v_trace_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 1, v_markInstances_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 2, v_lax_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 3, v_suggestions_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 4, v_locals_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 5, v_matchEqs_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 6, v_splitMatch_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 7, v_splitIte_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 8, v_splitIndPred_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 9, v_splitImp_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 10, v_ext_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 11, v_extAll_795_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 12, v_etaStruct_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 13, v_funext_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 14, v_lookahead_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 15, v_verbose_799_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 16, v_clean_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 18, v_mbtc_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 19, v_zetaDelta_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 20, v_zeta_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 21, v_ring_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 22, v_linarith_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 23, v_lia_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 24, v_ac_808_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 25, v_abstractProof_811_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 26, v_inj_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 27, v_order_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 28, v_useSorry_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 29, v_revert_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 30, v_funCC_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*11 + 31, v_reducible_819_);
v___x_876_ = v_reuseFailAlloc_902_;
goto v_reusejp_875_;
}
v___jp_824_:
{
lean_object* v___x_835_; lean_object* v_toGoalState_836_; lean_object* v_mvarId_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v___x_835_ = lean_st_ref_get(v___y_825_);
v_toGoalState_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_toGoalState_836_);
v_mvarId_837_ = lean_ctor_get(v___x_835_, 1);
lean_inc(v_mvarId_837_);
lean_dec(v___x_835_);
lean_inc_ref(v_e_713_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_838_, 0, v_mvarId_837_);
lean_closure_set(v___f_838_, 1, v_e_713_);
lean_closure_set(v___f_838_, 2, v_toGoalState_836_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
v___x_839_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_838_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_864_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_864_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_864_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_864_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_a_840_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_a_847_; uint8_t v___x_848_; 
lean_del_object(v___x_842_);
v_val_844_ = lean_ctor_get(v_a_840_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v_a_840_);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_846_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_845_, v___y_833_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_848_ == 0)
{
v___y_726_ = v_val_844_;
v___y_727_ = v___y_825_;
v___y_728_ = v___y_826_;
v___y_729_ = v___y_827_;
v___y_730_ = v___y_828_;
v___y_731_ = v___y_829_;
v___y_732_ = v___y_830_;
v___y_733_ = v___y_831_;
v___y_734_ = v___y_832_;
v___y_735_ = v___y_833_;
v___y_736_ = v___y_834_;
goto v___jp_725_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_inc_ref(v_e_713_);
v___x_849_ = l_Lean_MessageData_ofExpr(v_e_713_);
v___x_850_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(v___x_845_, v___x_849_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_dec_ref(v___x_850_);
v___y_726_ = v_val_844_;
v___y_727_ = v___y_825_;
v___y_728_ = v___y_826_;
v___y_729_ = v___y_827_;
v___y_730_ = v___y_828_;
v___y_731_ = v___y_829_;
v___y_732_ = v___y_830_;
v___y_733_ = v___y_831_;
v___y_734_ = v___y_832_;
v___y_735_ = v___y_833_;
v___y_736_ = v___y_834_;
goto v___jp_725_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_val_844_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v_e_713_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
else
{
uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_a_840_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v_e_713_);
v___x_859_ = 0;
v___x_860_ = lean_box(v___x_859_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_860_);
v___x_862_ = v___x_842_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v_e_713_);
v_a_865_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_839_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_839_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_880_; 
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*11 + 17, v___x_874_);
v___x_877_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_873_, v_a_722_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 2, v___x_876_);
v___x_880_ = v___x_777_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_simp_768_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_simpMethods_769_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_anchorRefs_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_splitSource_772_);
lean_ctor_set(v_reuseFailAlloc_901_, 5, v_symPrios_773_);
lean_ctor_set(v_reuseFailAlloc_901_, 6, v_extensions_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*7 + 1, v_reportMVarIssue_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*7 + 2, v_debug_775_);
v___x_880_ = v_reuseFailAlloc_901_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
uint8_t v___x_881_; 
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*7, v___x_874_);
v___x_881_ = lean_unbox(v_a_878_);
lean_dec(v_a_878_);
if (v___x_881_ == 0)
{
v___y_825_ = v_a_714_;
v___y_826_ = v_a_715_;
v___y_827_ = v___x_880_;
v___y_828_ = v_a_717_;
v___y_829_ = v_a_718_;
v___y_830_ = v_a_719_;
v___y_831_ = v_a_720_;
v___y_832_ = v_a_721_;
v___y_833_ = v_a_722_;
v___y_834_ = v_a_723_;
goto v___jp_824_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_updateLastTag(v_a_714_, v_a_715_, v___x_880_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v___x_882_);
lean_inc_ref(v_e_713_);
v___x_883_ = l_Lean_MessageData_ofExpr(v_e_713_);
v___x_884_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(v_cls_873_, v___x_883_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_dec_ref(v___x_884_);
v___y_825_ = v_a_714_;
v___y_826_ = v_a_715_;
v___y_827_ = v___x_880_;
v___y_828_ = v_a_717_;
v___y_829_ = v_a_718_;
v___y_830_ = v_a_719_;
v___y_831_ = v_a_720_;
v___y_832_ = v_a_721_;
v___y_833_ = v_a_722_;
v___y_834_ = v_a_723_;
goto v___jp_824_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v___x_880_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_e_713_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_880_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_e_713_);
v_a_893_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_882_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_882_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(lean_object* v_cls_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___redArg(v_cls_918_, v_msg_919_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3___boxed(lean_object* v_cls_932_, lean_object* v_msg_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__3(v_cls_932_, v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_946_, lean_object* v_as_x27_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
if (lean_obj_tag(v_as_x27_947_) == 0)
{
lean_object* v___x_960_; 
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_948_);
return v___x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1080_; 
v_head_961_ = lean_ctor_get(v_as_x27_947_, 0);
v_tail_962_ = lean_ctor_get(v_as_x27_947_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_as_x27_947_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_964_ = v_as_x27_947_;
v_isShared_965_ = v_isSharedCheck_1080_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_head_961_);
lean_dec(v_as_x27_947_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1080_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_949_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1070_; 
v_snd_967_ = lean_ctor_get(v_b_948_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_b_948_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_b_948_, 0);
lean_dec(v_unused_1071_);
v___x_969_ = v_b_948_;
v_isShared_970_ = v_isSharedCheck_1070_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_dec(v_b_948_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1070_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1069_; 
v_a_971_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_973_ = v___x_966_;
v_isShared_974_ = v_isSharedCheck_1069_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_966_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1069_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
uint8_t v___x_975_; 
v___x_975_ = lean_unbox(v_a_971_);
lean_dec(v_a_971_);
if (v___x_975_ == 0)
{
lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1051_; 
lean_del_object(v___x_973_);
v_fst_976_ = lean_ctor_get(v_snd_967_, 0);
v_snd_977_ = lean_ctor_get(v_snd_967_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_snd_967_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_979_ = v_snd_967_;
v_isShared_980_ = v_isSharedCheck_1051_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_976_);
lean_dec(v_snd_967_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1051_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; 
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc(v___y_949_);
lean_inc(v_head_961_);
v___x_981_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_961_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = lean_box(0);
switch(lean_obj_tag(v_a_982_))
{
case 0:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_dec(v_snd_977_);
lean_del_object(v___x_964_);
lean_dec(v_head_961_);
v___x_984_ = lean_box(v___x_946_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_984_);
v___x_986_ = v___x_979_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_986_);
lean_ctor_set(v___x_969_, 0, v___x_983_);
v___x_988_ = v___x_969_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_986_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_988_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_993_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_fst_976_);
v___x_993_ = v___x_964_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_head_961_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_fst_976_);
v___x_993_ = v_reuseFailAlloc_1001_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_993_);
v___x_995_ = v___x_979_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_snd_977_);
v___x_995_ = v_reuseFailAlloc_1000_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_995_);
lean_ctor_set(v___x_969_, 0, v___x_983_);
v___x_997_ = v___x_969_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_997_;
goto _start;
}
}
}
}
default: 
{
uint8_t v_tryPostpone_1002_; 
v_tryPostpone_1002_ = lean_ctor_get_uint8(v_a_982_, sizeof(void*)*1 + 1);
lean_dec_ref(v_a_982_);
if (v_tryPostpone_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_961_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc(v___y_949_);
v___x_1004_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_1003_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; uint8_t v___x_1006_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_unbox(v_a_1005_);
lean_dec(v_a_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1008_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_fst_976_);
v___x_1008_ = v___x_964_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_head_961_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_fst_976_);
v___x_1008_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_1008_);
v___x_1010_ = v___x_979_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_977_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1010_);
lean_ctor_set(v___x_969_, 0, v___x_983_);
v___x_1012_ = v___x_969_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_1012_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v_snd_977_);
lean_del_object(v___x_964_);
lean_dec(v_head_961_);
v___x_1017_ = lean_box(v___x_946_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1017_);
v___x_1019_ = v___x_979_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1019_);
lean_ctor_set(v___x_969_, 0, v___x_983_);
v___x_1021_ = v___x_969_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_1021_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_del_object(v___x_979_);
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_del_object(v___x_969_);
lean_del_object(v___x_964_);
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
v_a_1025_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1004_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1004_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1034_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_fst_976_);
v___x_1034_ = v___x_964_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_head_961_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_fst_976_);
v___x_1034_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_1034_);
v___x_1036_ = v___x_979_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_snd_977_);
v___x_1036_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1036_);
lean_ctor_set(v___x_969_, 0, v___x_983_);
v___x_1038_ = v___x_969_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
v_as_x27_947_ = v_tail_962_;
v_b_948_ = v___x_1038_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_del_object(v___x_979_);
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_del_object(v___x_969_);
lean_del_object(v___x_964_);
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
v_a_1043_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_981_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_981_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1068_; 
lean_del_object(v___x_964_);
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
v_fst_1052_ = lean_ctor_get(v_snd_967_, 0);
v_snd_1053_ = lean_ctor_get(v_snd_967_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_snd_967_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1055_ = v_snd_967_;
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v_snd_967_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = lean_box(v___x_946_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
if (v_isShared_1056_ == 0)
{
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_fst_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_snd_1053_);
v___x_1060_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1060_);
lean_ctor_set(v___x_969_, 0, v___x_1058_);
v___x_1062_ = v___x_969_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1062_);
v___x_1064_ = v___x_973_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
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
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_del_object(v___x_964_);
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v_b_948_);
v_a_1072_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_966_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_966_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1081_, lean_object* v_as_x27_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_41497__boxed_1095_; lean_object* v_res_1096_; 
v___x_41497__boxed_1095_ = lean_unbox(v___x_1081_);
v_res_1096_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_41497__boxed_1095_, v_as_x27_1082_, v_b_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1099_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1292_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1292_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1292_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
uint8_t v_lookahead_1113_; 
v_lookahead_1113_ = lean_ctor_get_uint8(v_a_1109_, sizeof(void*)*11 + 14);
lean_dec(v_a_1109_);
if (v_lookahead_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
v___x_1114_ = lean_box(v_lookahead_1113_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
lean_object* v___x_1118_; lean_object* v_toGoalState_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1290_; 
v___x_1118_ = lean_st_ref_get(v_a_1097_);
v_toGoalState_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1118_, 1);
lean_dec(v_unused_1291_);
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1290_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_toGoalState_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1290_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_split_1123_; lean_object* v_lookaheads_1124_; uint8_t v___x_1125_; 
v_split_1123_ = lean_ctor_get(v_toGoalState_1119_, 15);
lean_inc_ref(v_split_1123_);
lean_dec_ref(v_toGoalState_1119_);
v_lookaheads_1124_ = lean_ctor_get(v_split_1123_, 5);
lean_inc(v_lookaheads_1124_);
lean_dec_ref(v_split_1123_);
v___x_1125_ = l_List_isEmpty___redArg(v_lookaheads_1124_);
lean_dec(v_lookaheads_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_toGoalState_1128_; lean_object* v_split_1129_; lean_object* v_mvarId_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1111_);
v___x_1126_ = lean_st_ref_get(v_a_1097_);
v___x_1127_ = lean_st_ref_take(v_a_1097_);
v_toGoalState_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_toGoalState_1128_);
v_split_1129_ = lean_ctor_get(v_toGoalState_1128_, 15);
lean_inc_ref(v_split_1129_);
v_mvarId_1130_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1127_, 0);
lean_dec(v_unused_1284_);
v___x_1132_ = v___x_1127_;
v_isShared_1133_ = v_isSharedCheck_1283_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_mvarId_1130_);
lean_dec(v___x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1283_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_nextDeclIdx_1134_; lean_object* v_canon_1135_; lean_object* v_enodeMap_1136_; lean_object* v_exprs_1137_; lean_object* v_parents_1138_; lean_object* v_congrTable_1139_; lean_object* v_appMap_1140_; lean_object* v_indicesFound_1141_; lean_object* v_newFacts_1142_; uint8_t v_inconsistent_1143_; lean_object* v_nextIdx_1144_; lean_object* v_newRawFacts_1145_; lean_object* v_facts_1146_; lean_object* v_extThms_1147_; lean_object* v_ematch_1148_; lean_object* v_inj_1149_; lean_object* v_clean_1150_; lean_object* v_sstates_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1281_; 
v_nextDeclIdx_1134_ = lean_ctor_get(v_toGoalState_1128_, 0);
v_canon_1135_ = lean_ctor_get(v_toGoalState_1128_, 1);
v_enodeMap_1136_ = lean_ctor_get(v_toGoalState_1128_, 2);
v_exprs_1137_ = lean_ctor_get(v_toGoalState_1128_, 3);
v_parents_1138_ = lean_ctor_get(v_toGoalState_1128_, 4);
v_congrTable_1139_ = lean_ctor_get(v_toGoalState_1128_, 5);
v_appMap_1140_ = lean_ctor_get(v_toGoalState_1128_, 6);
v_indicesFound_1141_ = lean_ctor_get(v_toGoalState_1128_, 7);
v_newFacts_1142_ = lean_ctor_get(v_toGoalState_1128_, 8);
v_inconsistent_1143_ = lean_ctor_get_uint8(v_toGoalState_1128_, sizeof(void*)*18);
v_nextIdx_1144_ = lean_ctor_get(v_toGoalState_1128_, 9);
v_newRawFacts_1145_ = lean_ctor_get(v_toGoalState_1128_, 10);
v_facts_1146_ = lean_ctor_get(v_toGoalState_1128_, 11);
v_extThms_1147_ = lean_ctor_get(v_toGoalState_1128_, 12);
v_ematch_1148_ = lean_ctor_get(v_toGoalState_1128_, 13);
v_inj_1149_ = lean_ctor_get(v_toGoalState_1128_, 14);
v_clean_1150_ = lean_ctor_get(v_toGoalState_1128_, 16);
v_sstates_1151_ = lean_ctor_get(v_toGoalState_1128_, 17);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_toGoalState_1128_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_toGoalState_1128_, 15);
lean_dec(v_unused_1282_);
v___x_1153_ = v_toGoalState_1128_;
v_isShared_1154_ = v_isSharedCheck_1281_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_sstates_1151_);
lean_inc(v_clean_1150_);
lean_inc(v_inj_1149_);
lean_inc(v_ematch_1148_);
lean_inc(v_extThms_1147_);
lean_inc(v_facts_1146_);
lean_inc(v_newRawFacts_1145_);
lean_inc(v_nextIdx_1144_);
lean_inc(v_newFacts_1142_);
lean_inc(v_indicesFound_1141_);
lean_inc(v_appMap_1140_);
lean_inc(v_congrTable_1139_);
lean_inc(v_parents_1138_);
lean_inc(v_exprs_1137_);
lean_inc(v_enodeMap_1136_);
lean_inc(v_canon_1135_);
lean_inc(v_nextDeclIdx_1134_);
lean_dec(v_toGoalState_1128_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1281_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_num_1155_; lean_object* v_candidates_1156_; lean_object* v_added_1157_; lean_object* v_resolved_1158_; lean_object* v_trace_1159_; lean_object* v_argPosMap_1160_; lean_object* v_argsAt_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1279_; 
v_num_1155_ = lean_ctor_get(v_split_1129_, 0);
v_candidates_1156_ = lean_ctor_get(v_split_1129_, 1);
v_added_1157_ = lean_ctor_get(v_split_1129_, 2);
v_resolved_1158_ = lean_ctor_get(v_split_1129_, 3);
v_trace_1159_ = lean_ctor_get(v_split_1129_, 4);
v_argPosMap_1160_ = lean_ctor_get(v_split_1129_, 6);
v_argsAt_1161_ = lean_ctor_get(v_split_1129_, 7);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_split_1129_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_split_1129_, 5);
lean_dec(v_unused_1280_);
v___x_1163_ = v_split_1129_;
v_isShared_1164_ = v_isSharedCheck_1279_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_argsAt_1161_);
lean_inc(v_argPosMap_1160_);
lean_inc(v_trace_1159_);
lean_inc(v_resolved_1158_);
lean_inc(v_added_1157_);
lean_inc(v_candidates_1156_);
lean_inc(v_num_1155_);
lean_dec(v_split_1129_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1279_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 5, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_num_1155_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_candidates_1156_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_added_1157_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_resolved_1158_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_trace_1159_);
lean_ctor_set(v_reuseFailAlloc_1278_, 5, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1278_, 6, v_argPosMap_1160_);
lean_ctor_set(v_reuseFailAlloc_1278_, 7, v_argsAt_1161_);
v___x_1167_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 15, v___x_1167_);
v___x_1169_ = v___x_1153_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_nextDeclIdx_1134_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_canon_1135_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_enodeMap_1136_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_exprs_1137_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_parents_1138_);
lean_ctor_set(v_reuseFailAlloc_1277_, 5, v_congrTable_1139_);
lean_ctor_set(v_reuseFailAlloc_1277_, 6, v_appMap_1140_);
lean_ctor_set(v_reuseFailAlloc_1277_, 7, v_indicesFound_1141_);
lean_ctor_set(v_reuseFailAlloc_1277_, 8, v_newFacts_1142_);
lean_ctor_set(v_reuseFailAlloc_1277_, 9, v_nextIdx_1144_);
lean_ctor_set(v_reuseFailAlloc_1277_, 10, v_newRawFacts_1145_);
lean_ctor_set(v_reuseFailAlloc_1277_, 11, v_facts_1146_);
lean_ctor_set(v_reuseFailAlloc_1277_, 12, v_extThms_1147_);
lean_ctor_set(v_reuseFailAlloc_1277_, 13, v_ematch_1148_);
lean_ctor_set(v_reuseFailAlloc_1277_, 14, v_inj_1149_);
lean_ctor_set(v_reuseFailAlloc_1277_, 15, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1277_, 16, v_clean_1150_);
lean_ctor_set(v_reuseFailAlloc_1277_, 17, v_sstates_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*18, v_inconsistent_1143_);
v___x_1169_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1169_);
v___x_1171_ = v___x_1132_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_mvarId_1130_);
v___x_1171_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v_toGoalState_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1274_; 
v___x_1172_ = lean_st_ref_set(v_a_1097_, v___x_1171_);
v_toGoalState_1173_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1126_, 1);
lean_dec(v_unused_1275_);
v___x_1175_ = v___x_1126_;
v_isShared_1176_ = v_isSharedCheck_1274_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_toGoalState_1173_);
lean_dec(v___x_1126_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1274_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_split_1177_; lean_object* v_lookaheads_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v_split_1177_ = lean_ctor_get(v_toGoalState_1173_, 15);
lean_inc_ref(v_split_1177_);
lean_dec_ref(v_toGoalState_1173_);
v_lookaheads_1178_ = lean_ctor_get(v_split_1177_, 5);
lean_inc(v_lookaheads_1178_);
lean_dec_ref(v_split_1177_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_box(v___x_1125_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1180_);
lean_ctor_set(v___x_1175_, 0, v___x_1165_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1182_);
lean_ctor_set(v___x_1121_, 0, v___x_1179_);
v___x_1184_ = v___x_1121_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
lean_inc(v_a_1097_);
v___x_1185_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1113_, v_lookaheads_1178_, v___x_1184_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1263_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1263_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1263_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_fst_1190_; 
v_fst_1190_ = lean_ctor_get(v_a_1186_, 0);
if (lean_obj_tag(v_fst_1190_) == 0)
{
lean_object* v_snd_1191_; lean_object* v_snd_1192_; uint8_t v___x_1193_; 
v_snd_1191_ = lean_ctor_get(v_a_1186_, 1);
lean_inc(v_snd_1191_);
lean_dec(v_a_1186_);
v_snd_1192_ = lean_ctor_get(v_snd_1191_, 1);
v___x_1193_ = lean_unbox(v_snd_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec(v_snd_1191_);
lean_dec(v_a_1097_);
v___x_1194_ = lean_box(v___x_1125_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1194_);
v___x_1196_ = v___x_1188_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v_fst_1198_; lean_object* v___x_1199_; lean_object* v_toGoalState_1200_; lean_object* v_split_1201_; lean_object* v_mvarId_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1257_; 
v_fst_1198_ = lean_ctor_get(v_snd_1191_, 0);
lean_inc(v_fst_1198_);
lean_dec(v_snd_1191_);
v___x_1199_ = lean_st_ref_take(v_a_1097_);
v_toGoalState_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_ref(v_toGoalState_1200_);
v_split_1201_ = lean_ctor_get(v_toGoalState_1200_, 15);
lean_inc_ref(v_split_1201_);
v_mvarId_1202_ = lean_ctor_get(v___x_1199_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1199_, 0);
lean_dec(v_unused_1258_);
v___x_1204_ = v___x_1199_;
v_isShared_1205_ = v_isSharedCheck_1257_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_mvarId_1202_);
lean_dec(v___x_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1257_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_nextDeclIdx_1206_; lean_object* v_canon_1207_; lean_object* v_enodeMap_1208_; lean_object* v_exprs_1209_; lean_object* v_parents_1210_; lean_object* v_congrTable_1211_; lean_object* v_appMap_1212_; lean_object* v_indicesFound_1213_; lean_object* v_newFacts_1214_; uint8_t v_inconsistent_1215_; lean_object* v_nextIdx_1216_; lean_object* v_newRawFacts_1217_; lean_object* v_facts_1218_; lean_object* v_extThms_1219_; lean_object* v_ematch_1220_; lean_object* v_inj_1221_; lean_object* v_clean_1222_; lean_object* v_sstates_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1255_; 
v_nextDeclIdx_1206_ = lean_ctor_get(v_toGoalState_1200_, 0);
v_canon_1207_ = lean_ctor_get(v_toGoalState_1200_, 1);
v_enodeMap_1208_ = lean_ctor_get(v_toGoalState_1200_, 2);
v_exprs_1209_ = lean_ctor_get(v_toGoalState_1200_, 3);
v_parents_1210_ = lean_ctor_get(v_toGoalState_1200_, 4);
v_congrTable_1211_ = lean_ctor_get(v_toGoalState_1200_, 5);
v_appMap_1212_ = lean_ctor_get(v_toGoalState_1200_, 6);
v_indicesFound_1213_ = lean_ctor_get(v_toGoalState_1200_, 7);
v_newFacts_1214_ = lean_ctor_get(v_toGoalState_1200_, 8);
v_inconsistent_1215_ = lean_ctor_get_uint8(v_toGoalState_1200_, sizeof(void*)*18);
v_nextIdx_1216_ = lean_ctor_get(v_toGoalState_1200_, 9);
v_newRawFacts_1217_ = lean_ctor_get(v_toGoalState_1200_, 10);
v_facts_1218_ = lean_ctor_get(v_toGoalState_1200_, 11);
v_extThms_1219_ = lean_ctor_get(v_toGoalState_1200_, 12);
v_ematch_1220_ = lean_ctor_get(v_toGoalState_1200_, 13);
v_inj_1221_ = lean_ctor_get(v_toGoalState_1200_, 14);
v_clean_1222_ = lean_ctor_get(v_toGoalState_1200_, 16);
v_sstates_1223_ = lean_ctor_get(v_toGoalState_1200_, 17);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_toGoalState_1200_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v_toGoalState_1200_, 15);
lean_dec(v_unused_1256_);
v___x_1225_ = v_toGoalState_1200_;
v_isShared_1226_ = v_isSharedCheck_1255_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_sstates_1223_);
lean_inc(v_clean_1222_);
lean_inc(v_inj_1221_);
lean_inc(v_ematch_1220_);
lean_inc(v_extThms_1219_);
lean_inc(v_facts_1218_);
lean_inc(v_newRawFacts_1217_);
lean_inc(v_nextIdx_1216_);
lean_inc(v_newFacts_1214_);
lean_inc(v_indicesFound_1213_);
lean_inc(v_appMap_1212_);
lean_inc(v_congrTable_1211_);
lean_inc(v_parents_1210_);
lean_inc(v_exprs_1209_);
lean_inc(v_enodeMap_1208_);
lean_inc(v_canon_1207_);
lean_inc(v_nextDeclIdx_1206_);
lean_dec(v_toGoalState_1200_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1255_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_num_1227_; lean_object* v_candidates_1228_; lean_object* v_added_1229_; lean_object* v_resolved_1230_; lean_object* v_trace_1231_; lean_object* v_lookaheads_1232_; lean_object* v_argPosMap_1233_; lean_object* v_argsAt_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1254_; 
v_num_1227_ = lean_ctor_get(v_split_1201_, 0);
v_candidates_1228_ = lean_ctor_get(v_split_1201_, 1);
v_added_1229_ = lean_ctor_get(v_split_1201_, 2);
v_resolved_1230_ = lean_ctor_get(v_split_1201_, 3);
v_trace_1231_ = lean_ctor_get(v_split_1201_, 4);
v_lookaheads_1232_ = lean_ctor_get(v_split_1201_, 5);
v_argPosMap_1233_ = lean_ctor_get(v_split_1201_, 6);
v_argsAt_1234_ = lean_ctor_get(v_split_1201_, 7);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_split_1201_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1236_ = v_split_1201_;
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_argsAt_1234_);
lean_inc(v_argPosMap_1233_);
lean_inc(v_lookaheads_1232_);
lean_inc(v_trace_1231_);
lean_inc(v_resolved_1230_);
lean_inc(v_added_1229_);
lean_inc(v_candidates_1228_);
lean_inc(v_num_1227_);
lean_dec(v_split_1201_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = l_List_reverse___redArg(v_fst_1198_);
v___x_1239_ = l_List_appendTR___redArg(v_lookaheads_1232_, v___x_1238_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 5, v___x_1239_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_num_1227_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_candidates_1228_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_added_1229_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_resolved_1230_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v_trace_1231_);
lean_ctor_set(v_reuseFailAlloc_1253_, 5, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1253_, 6, v_argPosMap_1233_);
lean_ctor_set(v_reuseFailAlloc_1253_, 7, v_argsAt_1234_);
v___x_1241_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 15, v___x_1241_);
v___x_1243_ = v___x_1225_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_nextDeclIdx_1206_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_canon_1207_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_enodeMap_1208_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_exprs_1209_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_parents_1210_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_congrTable_1211_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_appMap_1212_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_indicesFound_1213_);
lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_newFacts_1214_);
lean_ctor_set(v_reuseFailAlloc_1252_, 9, v_nextIdx_1216_);
lean_ctor_set(v_reuseFailAlloc_1252_, 10, v_newRawFacts_1217_);
lean_ctor_set(v_reuseFailAlloc_1252_, 11, v_facts_1218_);
lean_ctor_set(v_reuseFailAlloc_1252_, 12, v_extThms_1219_);
lean_ctor_set(v_reuseFailAlloc_1252_, 13, v_ematch_1220_);
lean_ctor_set(v_reuseFailAlloc_1252_, 14, v_inj_1221_);
lean_ctor_set(v_reuseFailAlloc_1252_, 15, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1252_, 16, v_clean_1222_);
lean_ctor_set(v_reuseFailAlloc_1252_, 17, v_sstates_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*18, v_inconsistent_1215_);
v___x_1243_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1243_);
v___x_1245_ = v___x_1204_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_mvarId_1202_);
v___x_1245_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_st_ref_set(v_a_1097_, v___x_1245_);
lean_dec(v_a_1097_);
v___x_1247_ = lean_box(v_lookahead_1113_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1247_);
v___x_1249_ = v___x_1188_;
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
}
}
}
}
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1261_; 
lean_inc_ref(v_fst_1190_);
lean_dec(v_a_1186_);
lean_dec(v_a_1097_);
v_val_1259_ = lean_ctor_get(v_fst_1190_, 0);
lean_inc(v_val_1259_);
lean_dec_ref(v_fst_1190_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_val_1259_);
v___x_1261_ = v___x_1188_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_val_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1097_);
v_a_1264_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1185_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1185_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
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
uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_del_object(v___x_1121_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
v___x_1285_ = 0;
v___x_1286_ = lean_box(v___x_1285_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1286_);
v___x_1288_ = v___x_1111_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
v_a_1293_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1108_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1108_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Grind_lookahead(v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1313_, lean_object* v_as_1314_, lean_object* v_as_x27_1315_, lean_object* v_b_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1313_, v_as_x27_1315_, v_b_1316_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1330_, lean_object* v_as_1331_, lean_object* v_as_x27_1332_, lean_object* v_b_1333_, lean_object* v_a_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v___x_42048__boxed_1346_; lean_object* v_res_1347_; 
v___x_42048__boxed_1346_ = lean_unbox(v___x_1330_);
v_res_1347_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_42048__boxed_1346_, v_as_1331_, v_as_x27_1332_, v_b_1333_, v_a_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v_as_1331_);
return v_res_1347_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations = _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
}
#ifdef __cplusplus
}
#endif
