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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mkAction();
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_to_do(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value),LEAN_SCALAR_PTR_LITERAL(132, 37, 244, 19, 72, 39, 101, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
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
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
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
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
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
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
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
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object* v_goal_167_, lean_object* v_generation_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_ref_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v_ref_179_ = lean_ctor_get(v_a_176_, 2);
v___f_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1));
v___x_181_ = l_Lean_Meta_Grind_Solvers_mkAction();
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___x_188_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___f_183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed), 15, 2);
lean_closure_set(v___f_183_, 0, v_a_182_);
lean_closure_set(v___f_183_, 1, v___f_180_);
v___f_184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed), 14, 1);
lean_closure_set(v___f_184_, 0, v___f_183_);
v___f_185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed), 14, 1);
lean_closure_set(v___f_185_, 0, v___f_184_);
v___x_186_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_186_, 0, v_generation_168_);
v___f_187_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed), 15, 2);
lean_closure_set(v___f_187_, 0, v___x_186_);
lean_closure_set(v___f_187_, 1, v___f_185_);
lean_inc_ref(v_goal_167_);
v___x_188_ = l_Lean_Meta_Grind_Action_run(v_goal_167_, v___f_187_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_215_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_215_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_215_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_215_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
if (lean_obj_tag(v_a_189_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_195_; 
lean_dec_ref_known(v_a_189_, 1);
lean_dec_ref(v_goal_167_);
v___x_193_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v_gs_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_214_; 
v_gs_197_ = lean_ctor_get(v_a_189_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_a_189_);
if (v_isSharedCheck_214_ == 0)
{
v___x_199_ = v_a_189_;
v_isShared_200_ = v_isSharedCheck_214_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_gs_197_);
lean_dec(v_a_189_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_214_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
if (lean_obj_tag(v_gs_197_) == 1)
{
lean_object* v_head_201_; lean_object* v___x_203_; 
lean_dec_ref(v_goal_167_);
v_head_201_ = lean_ctor_get(v_gs_197_, 0);
lean_inc(v_head_201_);
lean_dec_ref_known(v_gs_197_, 2);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v_head_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_head_201_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_203_);
v___x_205_ = v___x_191_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v_gs_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v_goal_167_);
v___x_209_ = v___x_199_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_goal_167_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_209_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_goal_167_);
v_a_216_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_188_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_188_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_generation_168_);
lean_dec_ref(v_goal_167_);
v_a_224_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_235_ == 0)
{
v___x_226_ = v___x_181_;
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_181_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_228_ = lean_io_error_to_string(v_a_224_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
lean_inc(v_ref_179_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_ref_179_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_231_);
v___x_233_ = v___x_226_;
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
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
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
v___x_269_ = lean_st_ref_put(v___y_250_, v___x_268_);
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
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_box(0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_cache_306_);
lean_ctor_set(v___x_314_, 0, v_mctx_305_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
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
v___x_318_ = v_reuseFailAlloc_321_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_st_ref_put(v___y_304_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_316_);
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
lean_object* v___x_343_; lean_object* v_mctx_344_; lean_object* v___x_345_; lean_object* v_cache_346_; lean_object* v___x_347_; 
v___x_343_ = lean_st_ref_get(v___y_339_);
v_mctx_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_mctx_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_339_);
v_cache_346_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_cache_346_);
lean_dec(v___x_345_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
lean_inc(v___y_339_);
lean_inc_ref(v___y_338_);
lean_inc(v___y_337_);
lean_inc_ref(v___y_336_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc(v___y_332_);
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
v___x_354_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_344_, v_cache_346_, v___x_353_);
lean_dec_ref(v___x_353_);
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
lean_dec_ref_known(v___x_347_, 1);
v___x_366_ = lean_box(0);
v___x_367_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_344_, v_cache_346_, v___x_366_);
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
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec(v___y_377_);
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
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec(v___y_405_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object* v_mvarId_419_, lean_object* v_e_420_, lean_object* v_toGoalState_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_MVarId_getTag(v_mvarId_419_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_426_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
lean_inc_ref(v_e_420_);
v___x_437_ = l_Lean_mkNot(v_e_420_);
v___x_438_ = l_Lean_mkArrow(v___x_437_, v_a_436_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_439_, v_a_434_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_nextDeclIdx_442_; lean_object* v_enodeMap_443_; lean_object* v_exprs_444_; lean_object* v_parents_445_; lean_object* v_congrTable_446_; lean_object* v_appMap_447_; lean_object* v_indicesFound_448_; lean_object* v_internalizing_449_; uint8_t v_inconsistent_450_; lean_object* v_nextIdx_451_; lean_object* v_newRawFacts_452_; lean_object* v_facts_453_; lean_object* v_extThms_454_; lean_object* v_ematch_455_; lean_object* v_inj_456_; lean_object* v_split_457_; lean_object* v_clean_458_; lean_object* v_sstates_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_507_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v_nextDeclIdx_442_ = lean_ctor_get(v_toGoalState_421_, 0);
v_enodeMap_443_ = lean_ctor_get(v_toGoalState_421_, 1);
v_exprs_444_ = lean_ctor_get(v_toGoalState_421_, 2);
v_parents_445_ = lean_ctor_get(v_toGoalState_421_, 3);
v_congrTable_446_ = lean_ctor_get(v_toGoalState_421_, 4);
v_appMap_447_ = lean_ctor_get(v_toGoalState_421_, 5);
v_indicesFound_448_ = lean_ctor_get(v_toGoalState_421_, 6);
v_internalizing_449_ = lean_ctor_get(v_toGoalState_421_, 8);
v_inconsistent_450_ = lean_ctor_get_uint8(v_toGoalState_421_, sizeof(void*)*18);
v_nextIdx_451_ = lean_ctor_get(v_toGoalState_421_, 9);
v_newRawFacts_452_ = lean_ctor_get(v_toGoalState_421_, 10);
v_facts_453_ = lean_ctor_get(v_toGoalState_421_, 11);
v_extThms_454_ = lean_ctor_get(v_toGoalState_421_, 12);
v_ematch_455_ = lean_ctor_get(v_toGoalState_421_, 13);
v_inj_456_ = lean_ctor_get(v_toGoalState_421_, 14);
v_split_457_ = lean_ctor_get(v_toGoalState_421_, 15);
v_clean_458_ = lean_ctor_get(v_toGoalState_421_, 16);
v_sstates_459_ = lean_ctor_get(v_toGoalState_421_, 17);
v_isSharedCheck_507_ = !lean_is_exclusive(v_toGoalState_421_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v_toGoalState_421_, 7);
lean_dec(v_unused_508_);
v___x_461_ = v_toGoalState_421_;
v_isShared_462_ = v_isSharedCheck_507_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_sstates_459_);
lean_inc(v_clean_458_);
lean_inc(v_split_457_);
lean_inc(v_inj_456_);
lean_inc(v_ematch_455_);
lean_inc(v_extThms_454_);
lean_inc(v_facts_453_);
lean_inc(v_newRawFacts_452_);
lean_inc(v_nextIdx_451_);
lean_inc(v_internalizing_449_);
lean_inc(v_indicesFound_448_);
lean_inc(v_appMap_447_);
lean_inc(v_congrTable_446_);
lean_inc(v_parents_445_);
lean_inc(v_exprs_444_);
lean_inc(v_enodeMap_443_);
lean_inc(v_nextDeclIdx_442_);
lean_dec(v_toGoalState_421_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_507_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0));
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 7, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_nextDeclIdx_442_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_enodeMap_443_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_exprs_444_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_parents_445_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_congrTable_446_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_appMap_447_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_indicesFound_448_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_internalizing_449_);
lean_ctor_set(v_reuseFailAlloc_506_, 9, v_nextIdx_451_);
lean_ctor_set(v_reuseFailAlloc_506_, 10, v_newRawFacts_452_);
lean_ctor_set(v_reuseFailAlloc_506_, 11, v_facts_453_);
lean_ctor_set(v_reuseFailAlloc_506_, 12, v_extThms_454_);
lean_ctor_set(v_reuseFailAlloc_506_, 13, v_ematch_455_);
lean_ctor_set(v_reuseFailAlloc_506_, 14, v_inj_456_);
lean_ctor_set(v_reuseFailAlloc_506_, 15, v_split_457_);
lean_ctor_set(v_reuseFailAlloc_506_, 16, v_clean_458_);
lean_ctor_set(v_reuseFailAlloc_506_, 17, v_sstates_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*18, v_inconsistent_450_);
v___x_465_ = v_reuseFailAlloc_506_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_Expr_mvarId_x21(v_a_441_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_420_, v___y_422_);
lean_dec_ref(v_e_420_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_467_, v_a_469_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_489_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_489_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
if (lean_obj_tag(v_a_471_) == 0)
{
lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
lean_del_object(v___x_473_);
v___x_475_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_441_, v___y_429_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_484_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_a_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec_ref_known(v_a_471_, 1);
lean_dec(v_a_441_);
v___x_485_ = lean_box(0);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_485_);
v___x_487_ = v___x_473_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_441_);
v_a_490_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_470_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_470_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref_known(v___x_467_, 2);
lean_dec(v_a_441_);
v_a_498_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_468_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_468_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_509_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_440_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_440_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_517_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_438_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_438_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_525_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_435_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_435_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_533_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_433_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_433_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* v_mvarId_541_, lean_object* v_e_542_, lean_object* v_toGoalState_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_541_, v_e_542_, v_toGoalState_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_env_563_; uint8_t v___x_564_; lean_object* v_env_565_; lean_object* v___x_566_; lean_object* v_toCold_567_; lean_object* v_mctx_568_; lean_object* v_lctx_569_; lean_object* v_options_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_562_ = lean_st_ref_get(v___y_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v___x_564_ = 0;
v_env_565_ = l_Lean_Environment_setRecordingDeps(v_env_563_, v___x_564_);
v___x_566_ = lean_st_ref_get(v___y_558_);
v_toCold_567_ = lean_ctor_get(v___y_559_, 0);
v_mctx_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_mctx_568_);
lean_dec(v___x_566_);
v_lctx_569_ = lean_ctor_get(v___y_557_, 2);
v_options_570_ = lean_ctor_get(v_toCold_567_, 2);
lean_inc_ref(v_options_570_);
lean_inc_ref(v_lctx_569_);
v___x_571_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_571_, 0, v_env_565_);
lean_ctor_set(v___x_571_, 1, v_mctx_568_);
lean_ctor_set(v___x_571_, 2, v_lctx_569_);
lean_ctor_set(v___x_571_, 3, v_options_570_);
v___x_572_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_msgData_556_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object* v_msgData_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_580_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_581_; double v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_float_of_nat(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_586_, lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_ref_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_640_; 
v_ref_593_ = lean_ctor_get(v___y_590_, 2);
v___x_594_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_640_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_640_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_640_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_traceState_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_cache_605_; lean_object* v_recordedDeps_606_; lean_object* v_messages_607_; lean_object* v_infoState_608_; lean_object* v_snapshotTasks_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_639_; 
v___x_599_ = lean_st_ref_take(v___y_591_);
v_traceState_600_ = lean_ctor_get(v___x_599_, 4);
v_env_601_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_599_, 1);
v_ngen_603_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_599_, 3);
v_cache_605_ = lean_ctor_get(v___x_599_, 5);
v_recordedDeps_606_ = lean_ctor_get(v___x_599_, 6);
v_messages_607_ = lean_ctor_get(v___x_599_, 7);
v_infoState_608_ = lean_ctor_get(v___x_599_, 8);
v_snapshotTasks_609_ = lean_ctor_get(v___x_599_, 9);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_639_ == 0)
{
v___x_611_ = v___x_599_;
v_isShared_612_ = v_isSharedCheck_639_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snapshotTasks_609_);
lean_inc(v_infoState_608_);
lean_inc(v_messages_607_);
lean_inc(v_recordedDeps_606_);
lean_inc(v_cache_605_);
lean_inc(v_traceState_600_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_599_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_639_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
uint64_t v_tid_613_; lean_object* v_traces_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_638_; 
v_tid_613_ = lean_ctor_get_uint64(v_traceState_600_, sizeof(void*)*1);
v_traces_614_ = lean_ctor_get(v_traceState_600_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_traceState_600_);
if (v_isSharedCheck_638_ == 0)
{
v___x_616_ = v_traceState_600_;
v_isShared_617_ = v_isSharedCheck_638_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_traces_614_);
lean_dec(v_traceState_600_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_638_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; double v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_box(0);
v___x_620_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
v___x_621_ = 0;
v___x_622_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_623_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_623_, 0, v_cls_586_);
lean_ctor_set(v___x_623_, 1, v___x_619_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
lean_ctor_set_float(v___x_623_, sizeof(void*)*3, v___x_620_);
lean_ctor_set_float(v___x_623_, sizeof(void*)*3 + 8, v___x_620_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*3 + 16, v___x_621_);
v___x_624_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2));
v___x_625_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v_a_595_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_inc(v_ref_593_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_ref_593_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_PersistentArray_push___redArg(v_traces_614_, v___x_626_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_627_);
v___x_629_ = v___x_616_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_627_);
lean_ctor_set_uint64(v_reuseFailAlloc_637_, sizeof(void*)*1, v_tid_613_);
v___x_629_ = v_reuseFailAlloc_637_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v___x_629_);
v___x_631_ = v___x_611_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_env_601_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_recordedDeps_606_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v_messages_607_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_infoState_608_);
lean_ctor_set(v_reuseFailAlloc_636_, 9, v_snapshotTasks_609_);
v___x_631_ = v_reuseFailAlloc_636_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_st_ref_put(v___y_591_, v___x_631_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_618_);
v___x_634_ = v___x_597_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_618_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_658_ = l_Lean_mkConst(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_671_ = l_Lean_Name_append(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14(void){
_start:
{
lean_object* v_cls_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_cls_677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_679_ = l_Lean_Name_append(v___x_678_, v_cls_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v_config_734_; lean_object* v_toCold_735_; lean_object* v_options_736_; lean_object* v_simp_737_; lean_object* v_simpMethods_738_; lean_object* v_symSimpMethods_739_; lean_object* v_symDSimpMethods_740_; lean_object* v_anchorRefs_x3f_741_; uint8_t v_reportMVarIssue_742_; lean_object* v_splitSource_743_; lean_object* v_ematchDiagSource_744_; lean_object* v_symPrios_745_; lean_object* v_extensions_746_; uint8_t v_debug_747_; uint8_t v_ematchDiag_748_; uint8_t v_trace_749_; uint8_t v_markInstances_750_; uint8_t v_lax_751_; uint8_t v_suggestions_752_; uint8_t v_locals_753_; lean_object* v_splits_754_; lean_object* v_ematch_755_; lean_object* v_gen_756_; lean_object* v_genLocal_757_; lean_object* v_instances_758_; uint8_t v_matchEqs_759_; uint8_t v_splitMatch_760_; uint8_t v_splitIte_761_; uint8_t v_splitIndPred_762_; uint8_t v_splitImp_763_; lean_object* v_canonHeartbeats_764_; uint8_t v_ext_765_; uint8_t v_extAll_766_; uint8_t v_etaStruct_767_; uint8_t v_funext_768_; uint8_t v_lookahead_769_; uint8_t v_verbose_770_; uint8_t v_clean_771_; uint8_t v_mbtc_772_; uint8_t v_zetaDelta_773_; uint8_t v_zeta_774_; uint8_t v_ring_775_; lean_object* v_ringSteps_776_; lean_object* v_ringMaxDegree_777_; uint8_t v_linarith_778_; uint8_t v_lia_779_; lean_object* v_liaSteps_780_; uint8_t v_hom_781_; uint8_t v_ac_782_; lean_object* v_acSteps_783_; lean_object* v_exp_784_; uint8_t v_abstractProof_785_; uint8_t v_inj_786_; uint8_t v_order_787_; lean_object* v_min_788_; lean_object* v_detailed_789_; uint8_t v_useSorry_790_; uint8_t v_revert_791_; uint8_t v_funCC_792_; uint8_t v_reducible_793_; lean_object* v_maxSuggestions_794_; lean_object* v_inheritedTraceOptions_795_; uint8_t v_hasTrace_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___x_852_; 
v_config_734_ = lean_ctor_get(v_a_683_, 4);
v_toCold_735_ = lean_ctor_get(v_a_689_, 0);
v_options_736_ = lean_ctor_get(v_toCold_735_, 2);
v_simp_737_ = lean_ctor_get(v_a_683_, 0);
v_simpMethods_738_ = lean_ctor_get(v_a_683_, 1);
v_symSimpMethods_739_ = lean_ctor_get(v_a_683_, 2);
v_symDSimpMethods_740_ = lean_ctor_get(v_a_683_, 3);
v_anchorRefs_x3f_741_ = lean_ctor_get(v_a_683_, 5);
v_reportMVarIssue_742_ = lean_ctor_get_uint8(v_a_683_, sizeof(void*)*10 + 1);
v_splitSource_743_ = lean_ctor_get(v_a_683_, 6);
v_ematchDiagSource_744_ = lean_ctor_get(v_a_683_, 7);
v_symPrios_745_ = lean_ctor_get(v_a_683_, 8);
v_extensions_746_ = lean_ctor_get(v_a_683_, 9);
v_debug_747_ = lean_ctor_get_uint8(v_a_683_, sizeof(void*)*10 + 2);
v_ematchDiag_748_ = lean_ctor_get_uint8(v_a_683_, sizeof(void*)*10 + 3);
v_trace_749_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14);
v_markInstances_750_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 1);
v_lax_751_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 2);
v_suggestions_752_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 3);
v_locals_753_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 4);
v_splits_754_ = lean_ctor_get(v_config_734_, 0);
v_ematch_755_ = lean_ctor_get(v_config_734_, 1);
v_gen_756_ = lean_ctor_get(v_config_734_, 2);
v_genLocal_757_ = lean_ctor_get(v_config_734_, 3);
v_instances_758_ = lean_ctor_get(v_config_734_, 4);
v_matchEqs_759_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 5);
v_splitMatch_760_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 6);
v_splitIte_761_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 7);
v_splitIndPred_762_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 8);
v_splitImp_763_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 9);
v_canonHeartbeats_764_ = lean_ctor_get(v_config_734_, 5);
v_ext_765_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 10);
v_extAll_766_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 11);
v_etaStruct_767_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 12);
v_funext_768_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 13);
v_lookahead_769_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 14);
v_verbose_770_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 15);
v_clean_771_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 16);
v_mbtc_772_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 18);
v_zetaDelta_773_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 19);
v_zeta_774_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 20);
v_ring_775_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 21);
v_ringSteps_776_ = lean_ctor_get(v_config_734_, 6);
v_ringMaxDegree_777_ = lean_ctor_get(v_config_734_, 7);
v_linarith_778_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 22);
v_lia_779_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 23);
v_liaSteps_780_ = lean_ctor_get(v_config_734_, 8);
v_hom_781_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 24);
v_ac_782_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 25);
v_acSteps_783_ = lean_ctor_get(v_config_734_, 9);
v_exp_784_ = lean_ctor_get(v_config_734_, 10);
v_abstractProof_785_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 26);
v_inj_786_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 27);
v_order_787_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 28);
v_min_788_ = lean_ctor_get(v_config_734_, 11);
v_detailed_789_ = lean_ctor_get(v_config_734_, 12);
v_useSorry_790_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 29);
v_revert_791_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 30);
v_funCC_792_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 31);
v_reducible_793_ = lean_ctor_get_uint8(v_config_734_, sizeof(void*)*14 + 32);
v_maxSuggestions_794_ = lean_ctor_get(v_config_734_, 13);
v_inheritedTraceOptions_795_ = lean_ctor_get(v_toCold_735_, 11);
v_hasTrace_796_ = lean_ctor_get_uint8(v_options_736_, sizeof(void*)*1);
v___x_797_ = 1;
lean_inc(v_maxSuggestions_794_);
lean_inc(v_detailed_789_);
lean_inc(v_min_788_);
lean_inc(v_exp_784_);
lean_inc(v_acSteps_783_);
lean_inc(v_liaSteps_780_);
lean_inc(v_ringMaxDegree_777_);
lean_inc(v_ringSteps_776_);
lean_inc(v_canonHeartbeats_764_);
lean_inc(v_instances_758_);
lean_inc(v_genLocal_757_);
lean_inc(v_gen_756_);
lean_inc(v_ematch_755_);
lean_inc(v_splits_754_);
v___x_798_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_798_, 0, v_splits_754_);
lean_ctor_set(v___x_798_, 1, v_ematch_755_);
lean_ctor_set(v___x_798_, 2, v_gen_756_);
lean_ctor_set(v___x_798_, 3, v_genLocal_757_);
lean_ctor_set(v___x_798_, 4, v_instances_758_);
lean_ctor_set(v___x_798_, 5, v_canonHeartbeats_764_);
lean_ctor_set(v___x_798_, 6, v_ringSteps_776_);
lean_ctor_set(v___x_798_, 7, v_ringMaxDegree_777_);
lean_ctor_set(v___x_798_, 8, v_liaSteps_780_);
lean_ctor_set(v___x_798_, 9, v_acSteps_783_);
lean_ctor_set(v___x_798_, 10, v_exp_784_);
lean_ctor_set(v___x_798_, 11, v_min_788_);
lean_ctor_set(v___x_798_, 12, v_detailed_789_);
lean_ctor_set(v___x_798_, 13, v_maxSuggestions_794_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14, v_trace_749_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 1, v_markInstances_750_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 2, v_lax_751_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 3, v_suggestions_752_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 4, v_locals_753_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 5, v_matchEqs_759_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 6, v_splitMatch_760_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 7, v_splitIte_761_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 8, v_splitIndPred_762_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 9, v_splitImp_763_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 10, v_ext_765_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 11, v_extAll_766_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 12, v_etaStruct_767_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 13, v_funext_768_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 14, v_lookahead_769_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 15, v_verbose_770_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 16, v_clean_771_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 17, v___x_797_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 18, v_mbtc_772_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 19, v_zetaDelta_773_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 20, v_zeta_774_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 21, v_ring_775_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 22, v_linarith_778_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 23, v_lia_779_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 24, v_hom_781_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 25, v_ac_782_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 26, v_abstractProof_785_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 27, v_inj_786_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 28, v_order_787_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 29, v_useSorry_790_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 30, v_revert_791_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 31, v_funCC_792_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*14 + 32, v_reducible_793_);
lean_inc_ref(v_extensions_746_);
lean_inc_ref(v_symPrios_745_);
lean_inc(v_ematchDiagSource_744_);
lean_inc(v_splitSource_743_);
lean_inc(v_anchorRefs_x3f_741_);
lean_inc_ref(v_symDSimpMethods_740_);
lean_inc_ref(v_symSimpMethods_739_);
lean_inc_ref(v_simpMethods_738_);
lean_inc_ref(v_simp_737_);
v___x_852_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_852_, 0, v_simp_737_);
lean_ctor_set(v___x_852_, 1, v_simpMethods_738_);
lean_ctor_set(v___x_852_, 2, v_symSimpMethods_739_);
lean_ctor_set(v___x_852_, 3, v_symDSimpMethods_740_);
lean_ctor_set(v___x_852_, 4, v___x_798_);
lean_ctor_set(v___x_852_, 5, v_anchorRefs_x3f_741_);
lean_ctor_set(v___x_852_, 6, v_splitSource_743_);
lean_ctor_set(v___x_852_, 7, v_ematchDiagSource_744_);
lean_ctor_set(v___x_852_, 8, v_symPrios_745_);
lean_ctor_set(v___x_852_, 9, v_extensions_746_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*10, v___x_797_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*10 + 1, v_reportMVarIssue_742_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*10 + 2, v_debug_747_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*10 + 3, v_ematchDiag_748_);
if (v_hasTrace_796_ == 0)
{
v___y_800_ = v_a_681_;
v___y_801_ = v_a_682_;
v___y_802_ = v___x_852_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
v___y_809_ = v_a_690_;
goto v___jp_799_;
}
else
{
lean_object* v_cls_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_cls_853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
v___x_855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_795_, v_options_736_, v___x_854_);
if (v___x_855_ == 0)
{
v___y_800_ = v_a_681_;
v___y_801_ = v_a_682_;
v___y_802_ = v___x_852_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
v___y_809_ = v_a_690_;
goto v___jp_799_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Grind_updateLastTag(v_a_681_, v_a_682_, v___x_852_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref_known(v___x_856_, 1);
lean_inc_ref(v_e_680_);
v___x_857_ = l_Lean_MessageData_ofExpr(v_e_680_);
v___x_858_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_853_, v___x_857_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_dec_ref_known(v___x_858_, 1);
v___y_800_ = v_a_681_;
v___y_801_ = v_a_682_;
v___y_802_ = v___x_852_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
v___y_809_ = v_a_690_;
goto v___jp_799_;
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref_known(v___x_852_, 10);
lean_dec_ref(v_e_680_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref_known(v___x_852_, 10);
lean_dec_ref(v_e_680_);
v_a_867_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_856_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_856_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
v___jp_692_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_680_);
v___x_705_ = l_Lean_mkAppB(v___x_704_, v_e_680_, v___y_693_);
v___x_706_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_680_, v___x_705_, v___y_694_, v___y_696_, v___y_698_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; 
lean_dec_ref_known(v___x_706_, 1);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc(v___y_695_);
lean_inc(v___y_694_);
v___x_707_ = lean_grind_process_to_do(v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_717_);
v___x_709_ = v___x_707_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_dec(v___x_707_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = 1;
v___x_712_ = lean_box(v___x_711_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_707_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_707_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v___y_696_);
v_a_726_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_706_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_706_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
v___jp_799_:
{
lean_object* v___x_810_; lean_object* v_toGoalState_811_; lean_object* v_mvarId_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
v___x_810_ = lean_st_ref_get(v___y_800_);
v_toGoalState_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_toGoalState_811_);
v_mvarId_812_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_mvarId_812_);
lean_dec(v___x_810_);
lean_inc_ref(v_e_680_);
v___f_813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_813_, 0, v_mvarId_812_);
lean_closure_set(v___f_813_, 1, v_e_680_);
lean_closure_set(v___f_813_, 2, v_toGoalState_811_);
v___x_814_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_813_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_843_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_843_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
if (lean_obj_tag(v_a_815_) == 1)
{
lean_object* v_toCold_819_; lean_object* v_options_820_; uint8_t v_hasTrace_821_; 
lean_del_object(v___x_817_);
v_toCold_819_ = lean_ctor_get(v___y_808_, 0);
v_options_820_ = lean_ctor_get(v_toCold_819_, 2);
v_hasTrace_821_ = lean_ctor_get_uint8(v_options_820_, sizeof(void*)*1);
if (v_hasTrace_821_ == 0)
{
lean_object* v_val_822_; 
v_val_822_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_a_815_, 1);
v___y_693_ = v_val_822_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
v___y_703_ = v___y_809_;
goto v___jp_692_;
}
else
{
lean_object* v_val_823_; lean_object* v_inheritedTraceOptions_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_val_823_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v_a_815_, 1);
v_inheritedTraceOptions_824_ = lean_ctor_get(v_toCold_819_, 11);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
v___x_827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_824_, v_options_820_, v___x_826_);
if (v___x_827_ == 0)
{
v___y_693_ = v_val_823_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
v___y_703_ = v___y_809_;
goto v___jp_692_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_inc_ref(v_e_680_);
v___x_828_ = l_Lean_MessageData_ofExpr(v_e_680_);
v___x_829_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_825_, v___x_828_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref_known(v___x_829_, 1);
v___y_693_ = v_val_823_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
v___y_703_ = v___y_809_;
goto v___jp_692_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_val_823_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_e_680_);
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
else
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
lean_dec(v_a_815_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_e_680_);
v___x_838_ = 0;
v___x_839_ = lean_box(v___x_838_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_839_);
v___x_841_ = v___x_817_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v___y_802_);
lean_dec_ref(v_e_680_);
v_a_844_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_814_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_814_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_888_, v_msg_889_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_902_, lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_902_, v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_916_, lean_object* v_as_x27_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
if (lean_obj_tag(v_as_x27_917_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_b_918_);
return v___x_930_;
}
else
{
lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_1033_; 
v_snd_931_ = lean_ctor_get(v_b_918_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_b_918_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_b_918_, 0);
lean_dec(v_unused_1034_);
v___x_933_ = v_b_918_;
v_isShared_934_ = v_isSharedCheck_1033_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_dec(v_b_918_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_1033_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_head_935_; lean_object* v_tail_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1032_; 
v_head_935_ = lean_ctor_get(v_as_x27_917_, 0);
v_tail_936_ = lean_ctor_get(v_as_x27_917_, 1);
v_fst_937_ = lean_ctor_get(v_snd_931_, 0);
v_snd_938_ = lean_ctor_get(v_snd_931_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_snd_931_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_940_ = v_snd_931_;
v_isShared_941_ = v_isSharedCheck_1032_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_inc(v_fst_937_);
lean_dec(v_snd_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1032_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_box(0);
v___x_943_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_919_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1023_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_1023_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1023_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_948_; 
v___x_948_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_del_object(v___x_946_);
lean_inc(v_head_935_);
v___x_949_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_935_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
switch(lean_obj_tag(v_a_950_))
{
case 0:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_snd_938_);
v___x_951_ = lean_box(v___x_916_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_951_);
v___x_953_ = v___x_940_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_953_);
lean_ctor_set(v___x_933_, 0, v___x_942_);
v___x_955_ = v___x_933_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v_as_x27_917_ = v_tail_936_;
v_b_918_ = v___x_955_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_inc(v_head_935_);
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v_head_935_);
lean_ctor_set(v___x_959_, 1, v_fst_937_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_959_);
v___x_961_ = v___x_940_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_snd_938_);
v___x_961_ = v_reuseFailAlloc_966_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_961_);
lean_ctor_set(v___x_933_, 0, v___x_942_);
v___x_963_ = v___x_933_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_as_x27_917_ = v_tail_936_;
v_b_918_ = v___x_963_;
goto _start;
}
}
}
default: 
{
uint8_t v_tryPostpone_967_; 
v_tryPostpone_967_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_950_, 1);
if (v_tryPostpone_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_935_);
v___x_969_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_968_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_inc(v_head_935_);
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v_head_935_);
lean_ctor_set(v___x_972_, 1, v_fst_937_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_972_);
v___x_974_ = v___x_940_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_snd_938_);
v___x_974_ = v_reuseFailAlloc_979_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_974_);
lean_ctor_set(v___x_933_, 0, v___x_942_);
v___x_976_ = v___x_933_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_978_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v_as_x27_917_ = v_tail_936_;
v_b_918_ = v___x_976_;
goto _start;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec(v_snd_938_);
v___x_980_ = lean_box(v___x_916_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_980_);
v___x_982_ = v___x_940_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_987_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_982_);
lean_ctor_set(v___x_933_, 0, v___x_942_);
v___x_984_ = v___x_933_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
v_as_x27_917_ = v_tail_936_;
v_b_918_ = v___x_984_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_940_);
lean_dec(v_snd_938_);
lean_dec(v_fst_937_);
lean_del_object(v___x_933_);
v_a_988_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_969_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_969_);
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
else
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_inc(v_head_935_);
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v_head_935_);
lean_ctor_set(v___x_996_, 1, v_fst_937_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_996_);
v___x_998_ = v___x_940_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_snd_938_);
v___x_998_ = v_reuseFailAlloc_1003_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_998_);
lean_ctor_set(v___x_933_, 0, v___x_942_);
v___x_1000_ = v___x_933_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_as_x27_917_ = v_tail_936_;
v_b_918_ = v___x_1000_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_940_);
lean_dec(v_snd_938_);
lean_dec(v_fst_937_);
lean_del_object(v___x_933_);
v_a_1004_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_949_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_949_);
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
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = lean_box(v___x_916_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
if (v_isShared_941_ == 0)
{
v___x_1015_ = v___x_940_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_938_);
v___x_1015_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_1015_);
lean_ctor_set(v___x_933_, 0, v___x_1013_);
v___x_1017_ = v___x_933_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_1017_);
v___x_1019_ = v___x_946_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_del_object(v___x_940_);
lean_dec(v_snd_938_);
lean_dec(v_fst_937_);
lean_del_object(v___x_933_);
v_a_1024_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_943_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_943_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1035_, lean_object* v_as_x27_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___x_33303__boxed_1049_; lean_object* v_res_1050_; 
v___x_33303__boxed_1049_ = lean_unbox(v___x_1035_);
v_res_1050_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_33303__boxed_1049_, v_as_x27_1036_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v_as_x27_1036_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1053_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1246_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1246_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1246_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v_lookahead_1067_; 
v_lookahead_1067_ = lean_ctor_get_uint8(v_a_1063_, sizeof(void*)*14 + 14);
lean_dec(v_a_1063_);
if (v_lookahead_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_box(v_lookahead_1067_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1068_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v_toGoalState_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1244_; 
v___x_1072_ = lean_st_ref_get(v_a_1051_);
v_toGoalState_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1072_, 1);
lean_dec(v_unused_1245_);
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1244_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_toGoalState_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1244_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_split_1077_; lean_object* v_lookaheads_1078_; uint8_t v___x_1079_; 
v_split_1077_ = lean_ctor_get(v_toGoalState_1073_, 15);
lean_inc_ref(v_split_1077_);
lean_dec_ref(v_toGoalState_1073_);
v_lookaheads_1078_ = lean_ctor_get(v_split_1077_, 5);
lean_inc(v_lookaheads_1078_);
lean_dec_ref(v_split_1077_);
v___x_1079_ = l_List_isEmpty___redArg(v_lookaheads_1078_);
lean_dec(v_lookaheads_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_toGoalState_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1237_; 
lean_del_object(v___x_1065_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_st_ref_get(v_a_1051_);
v_toGoalState_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1081_, 1);
lean_dec(v_unused_1238_);
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1237_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_toGoalState_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1237_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_split_1086_; lean_object* v_lookaheads_1087_; lean_object* v___x_1088_; lean_object* v_toGoalState_1089_; lean_object* v_split_1090_; lean_object* v_mvarId_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1235_; 
v_split_1086_ = lean_ctor_get(v_toGoalState_1082_, 15);
lean_inc_ref(v_split_1086_);
lean_dec_ref(v_toGoalState_1082_);
v_lookaheads_1087_ = lean_ctor_get(v_split_1086_, 5);
lean_inc(v_lookaheads_1087_);
lean_dec_ref(v_split_1086_);
v___x_1088_ = lean_st_ref_take(v_a_1051_);
v_toGoalState_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_toGoalState_1089_);
v_split_1090_ = lean_ctor_get(v_toGoalState_1089_, 15);
lean_inc_ref(v_split_1090_);
v_mvarId_1091_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1088_, 0);
lean_dec(v_unused_1236_);
v___x_1093_ = v___x_1088_;
v_isShared_1094_ = v_isSharedCheck_1235_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_mvarId_1091_);
lean_dec(v___x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1235_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_nextDeclIdx_1095_; lean_object* v_enodeMap_1096_; lean_object* v_exprs_1097_; lean_object* v_parents_1098_; lean_object* v_congrTable_1099_; lean_object* v_appMap_1100_; lean_object* v_indicesFound_1101_; lean_object* v_toProcess_1102_; lean_object* v_internalizing_1103_; uint8_t v_inconsistent_1104_; lean_object* v_nextIdx_1105_; lean_object* v_newRawFacts_1106_; lean_object* v_facts_1107_; lean_object* v_extThms_1108_; lean_object* v_ematch_1109_; lean_object* v_inj_1110_; lean_object* v_clean_1111_; lean_object* v_sstates_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1233_; 
v_nextDeclIdx_1095_ = lean_ctor_get(v_toGoalState_1089_, 0);
v_enodeMap_1096_ = lean_ctor_get(v_toGoalState_1089_, 1);
v_exprs_1097_ = lean_ctor_get(v_toGoalState_1089_, 2);
v_parents_1098_ = lean_ctor_get(v_toGoalState_1089_, 3);
v_congrTable_1099_ = lean_ctor_get(v_toGoalState_1089_, 4);
v_appMap_1100_ = lean_ctor_get(v_toGoalState_1089_, 5);
v_indicesFound_1101_ = lean_ctor_get(v_toGoalState_1089_, 6);
v_toProcess_1102_ = lean_ctor_get(v_toGoalState_1089_, 7);
v_internalizing_1103_ = lean_ctor_get(v_toGoalState_1089_, 8);
v_inconsistent_1104_ = lean_ctor_get_uint8(v_toGoalState_1089_, sizeof(void*)*18);
v_nextIdx_1105_ = lean_ctor_get(v_toGoalState_1089_, 9);
v_newRawFacts_1106_ = lean_ctor_get(v_toGoalState_1089_, 10);
v_facts_1107_ = lean_ctor_get(v_toGoalState_1089_, 11);
v_extThms_1108_ = lean_ctor_get(v_toGoalState_1089_, 12);
v_ematch_1109_ = lean_ctor_get(v_toGoalState_1089_, 13);
v_inj_1110_ = lean_ctor_get(v_toGoalState_1089_, 14);
v_clean_1111_ = lean_ctor_get(v_toGoalState_1089_, 16);
v_sstates_1112_ = lean_ctor_get(v_toGoalState_1089_, 17);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_toGoalState_1089_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_toGoalState_1089_, 15);
lean_dec(v_unused_1234_);
v___x_1114_ = v_toGoalState_1089_;
v_isShared_1115_ = v_isSharedCheck_1233_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_sstates_1112_);
lean_inc(v_clean_1111_);
lean_inc(v_inj_1110_);
lean_inc(v_ematch_1109_);
lean_inc(v_extThms_1108_);
lean_inc(v_facts_1107_);
lean_inc(v_newRawFacts_1106_);
lean_inc(v_nextIdx_1105_);
lean_inc(v_internalizing_1103_);
lean_inc(v_toProcess_1102_);
lean_inc(v_indicesFound_1101_);
lean_inc(v_appMap_1100_);
lean_inc(v_congrTable_1099_);
lean_inc(v_parents_1098_);
lean_inc(v_exprs_1097_);
lean_inc(v_enodeMap_1096_);
lean_inc(v_nextDeclIdx_1095_);
lean_dec(v_toGoalState_1089_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1233_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_num_1116_; lean_object* v_candidates_1117_; lean_object* v_added_1118_; lean_object* v_resolved_1119_; lean_object* v_trace_1120_; lean_object* v_argPosMap_1121_; lean_object* v_argsAt_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1231_; 
v_num_1116_ = lean_ctor_get(v_split_1090_, 0);
v_candidates_1117_ = lean_ctor_get(v_split_1090_, 1);
v_added_1118_ = lean_ctor_get(v_split_1090_, 2);
v_resolved_1119_ = lean_ctor_get(v_split_1090_, 3);
v_trace_1120_ = lean_ctor_get(v_split_1090_, 4);
v_argPosMap_1121_ = lean_ctor_get(v_split_1090_, 6);
v_argsAt_1122_ = lean_ctor_get(v_split_1090_, 7);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_split_1090_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_split_1090_, 5);
lean_dec(v_unused_1232_);
v___x_1124_ = v_split_1090_;
v_isShared_1125_ = v_isSharedCheck_1231_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_argsAt_1122_);
lean_inc(v_argPosMap_1121_);
lean_inc(v_trace_1120_);
lean_inc(v_resolved_1119_);
lean_inc(v_added_1118_);
lean_inc(v_candidates_1117_);
lean_inc(v_num_1116_);
lean_dec(v_split_1090_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1231_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 5, v___x_1080_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_num_1116_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_candidates_1117_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_added_1118_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_resolved_1119_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_trace_1120_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_argPosMap_1121_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_argsAt_1122_);
v___x_1127_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 15, v___x_1127_);
v___x_1129_ = v___x_1114_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_nextDeclIdx_1095_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_enodeMap_1096_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_exprs_1097_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_parents_1098_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_congrTable_1099_);
lean_ctor_set(v_reuseFailAlloc_1229_, 5, v_appMap_1100_);
lean_ctor_set(v_reuseFailAlloc_1229_, 6, v_indicesFound_1101_);
lean_ctor_set(v_reuseFailAlloc_1229_, 7, v_toProcess_1102_);
lean_ctor_set(v_reuseFailAlloc_1229_, 8, v_internalizing_1103_);
lean_ctor_set(v_reuseFailAlloc_1229_, 9, v_nextIdx_1105_);
lean_ctor_set(v_reuseFailAlloc_1229_, 10, v_newRawFacts_1106_);
lean_ctor_set(v_reuseFailAlloc_1229_, 11, v_facts_1107_);
lean_ctor_set(v_reuseFailAlloc_1229_, 12, v_extThms_1108_);
lean_ctor_set(v_reuseFailAlloc_1229_, 13, v_ematch_1109_);
lean_ctor_set(v_reuseFailAlloc_1229_, 14, v_inj_1110_);
lean_ctor_set(v_reuseFailAlloc_1229_, 15, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1229_, 16, v_clean_1111_);
lean_ctor_set(v_reuseFailAlloc_1229_, 17, v_sstates_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*18, v_inconsistent_1104_);
v___x_1129_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1129_);
v___x_1131_ = v___x_1093_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_mvarId_1091_);
v___x_1131_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1132_ = lean_st_ref_put(v_a_1051_, v___x_1131_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_box(v___x_1079_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1134_);
lean_ctor_set(v___x_1084_, 0, v___x_1080_);
v___x_1136_ = v___x_1084_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1136_);
lean_ctor_set(v___x_1075_, 0, v___x_1133_);
v___x_1138_ = v___x_1075_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1067_, v_lookaheads_1087_, v___x_1138_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_lookaheads_1087_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1217_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1217_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1217_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_fst_1144_; 
v_fst_1144_ = lean_ctor_get(v_a_1140_, 0);
if (lean_obj_tag(v_fst_1144_) == 0)
{
lean_object* v_snd_1145_; lean_object* v_snd_1146_; uint8_t v___x_1147_; 
v_snd_1145_ = lean_ctor_get(v_a_1140_, 1);
lean_inc(v_snd_1145_);
lean_dec(v_a_1140_);
v_snd_1146_ = lean_ctor_get(v_snd_1145_, 1);
v___x_1147_ = lean_unbox(v_snd_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec(v_snd_1145_);
v___x_1148_ = lean_box(v___x_1079_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1148_);
v___x_1150_ = v___x_1142_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v_fst_1152_; lean_object* v___x_1153_; lean_object* v_toGoalState_1154_; lean_object* v_split_1155_; lean_object* v_mvarId_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1211_; 
v_fst_1152_ = lean_ctor_get(v_snd_1145_, 0);
lean_inc(v_fst_1152_);
lean_dec(v_snd_1145_);
v___x_1153_ = lean_st_ref_take(v_a_1051_);
v_toGoalState_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_toGoalState_1154_);
v_split_1155_ = lean_ctor_get(v_toGoalState_1154_, 15);
lean_inc_ref(v_split_1155_);
v_mvarId_1156_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1212_);
v___x_1158_ = v___x_1153_;
v_isShared_1159_ = v_isSharedCheck_1211_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_mvarId_1156_);
lean_dec(v___x_1153_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1211_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_nextDeclIdx_1160_; lean_object* v_enodeMap_1161_; lean_object* v_exprs_1162_; lean_object* v_parents_1163_; lean_object* v_congrTable_1164_; lean_object* v_appMap_1165_; lean_object* v_indicesFound_1166_; lean_object* v_toProcess_1167_; lean_object* v_internalizing_1168_; uint8_t v_inconsistent_1169_; lean_object* v_nextIdx_1170_; lean_object* v_newRawFacts_1171_; lean_object* v_facts_1172_; lean_object* v_extThms_1173_; lean_object* v_ematch_1174_; lean_object* v_inj_1175_; lean_object* v_clean_1176_; lean_object* v_sstates_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1209_; 
v_nextDeclIdx_1160_ = lean_ctor_get(v_toGoalState_1154_, 0);
v_enodeMap_1161_ = lean_ctor_get(v_toGoalState_1154_, 1);
v_exprs_1162_ = lean_ctor_get(v_toGoalState_1154_, 2);
v_parents_1163_ = lean_ctor_get(v_toGoalState_1154_, 3);
v_congrTable_1164_ = lean_ctor_get(v_toGoalState_1154_, 4);
v_appMap_1165_ = lean_ctor_get(v_toGoalState_1154_, 5);
v_indicesFound_1166_ = lean_ctor_get(v_toGoalState_1154_, 6);
v_toProcess_1167_ = lean_ctor_get(v_toGoalState_1154_, 7);
v_internalizing_1168_ = lean_ctor_get(v_toGoalState_1154_, 8);
v_inconsistent_1169_ = lean_ctor_get_uint8(v_toGoalState_1154_, sizeof(void*)*18);
v_nextIdx_1170_ = lean_ctor_get(v_toGoalState_1154_, 9);
v_newRawFacts_1171_ = lean_ctor_get(v_toGoalState_1154_, 10);
v_facts_1172_ = lean_ctor_get(v_toGoalState_1154_, 11);
v_extThms_1173_ = lean_ctor_get(v_toGoalState_1154_, 12);
v_ematch_1174_ = lean_ctor_get(v_toGoalState_1154_, 13);
v_inj_1175_ = lean_ctor_get(v_toGoalState_1154_, 14);
v_clean_1176_ = lean_ctor_get(v_toGoalState_1154_, 16);
v_sstates_1177_ = lean_ctor_get(v_toGoalState_1154_, 17);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_toGoalState_1154_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_toGoalState_1154_, 15);
lean_dec(v_unused_1210_);
v___x_1179_ = v_toGoalState_1154_;
v_isShared_1180_ = v_isSharedCheck_1209_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_sstates_1177_);
lean_inc(v_clean_1176_);
lean_inc(v_inj_1175_);
lean_inc(v_ematch_1174_);
lean_inc(v_extThms_1173_);
lean_inc(v_facts_1172_);
lean_inc(v_newRawFacts_1171_);
lean_inc(v_nextIdx_1170_);
lean_inc(v_internalizing_1168_);
lean_inc(v_toProcess_1167_);
lean_inc(v_indicesFound_1166_);
lean_inc(v_appMap_1165_);
lean_inc(v_congrTable_1164_);
lean_inc(v_parents_1163_);
lean_inc(v_exprs_1162_);
lean_inc(v_enodeMap_1161_);
lean_inc(v_nextDeclIdx_1160_);
lean_dec(v_toGoalState_1154_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1209_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_num_1181_; lean_object* v_candidates_1182_; lean_object* v_added_1183_; lean_object* v_resolved_1184_; lean_object* v_trace_1185_; lean_object* v_lookaheads_1186_; lean_object* v_argPosMap_1187_; lean_object* v_argsAt_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1208_; 
v_num_1181_ = lean_ctor_get(v_split_1155_, 0);
v_candidates_1182_ = lean_ctor_get(v_split_1155_, 1);
v_added_1183_ = lean_ctor_get(v_split_1155_, 2);
v_resolved_1184_ = lean_ctor_get(v_split_1155_, 3);
v_trace_1185_ = lean_ctor_get(v_split_1155_, 4);
v_lookaheads_1186_ = lean_ctor_get(v_split_1155_, 5);
v_argPosMap_1187_ = lean_ctor_get(v_split_1155_, 6);
v_argsAt_1188_ = lean_ctor_get(v_split_1155_, 7);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_split_1155_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1190_ = v_split_1155_;
v_isShared_1191_ = v_isSharedCheck_1208_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_argsAt_1188_);
lean_inc(v_argPosMap_1187_);
lean_inc(v_lookaheads_1186_);
lean_inc(v_trace_1185_);
lean_inc(v_resolved_1184_);
lean_inc(v_added_1183_);
lean_inc(v_candidates_1182_);
lean_inc(v_num_1181_);
lean_dec(v_split_1155_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1208_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = l_List_reverse___redArg(v_fst_1152_);
v___x_1193_ = l_List_appendTR___redArg(v_lookaheads_1186_, v___x_1192_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 5, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_num_1181_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_candidates_1182_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_added_1183_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_resolved_1184_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_trace_1185_);
lean_ctor_set(v_reuseFailAlloc_1207_, 5, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1207_, 6, v_argPosMap_1187_);
lean_ctor_set(v_reuseFailAlloc_1207_, 7, v_argsAt_1188_);
v___x_1195_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 15, v___x_1195_);
v___x_1197_ = v___x_1179_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_nextDeclIdx_1160_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_enodeMap_1161_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_exprs_1162_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_parents_1163_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_congrTable_1164_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v_appMap_1165_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_indicesFound_1166_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_toProcess_1167_);
lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_internalizing_1168_);
lean_ctor_set(v_reuseFailAlloc_1206_, 9, v_nextIdx_1170_);
lean_ctor_set(v_reuseFailAlloc_1206_, 10, v_newRawFacts_1171_);
lean_ctor_set(v_reuseFailAlloc_1206_, 11, v_facts_1172_);
lean_ctor_set(v_reuseFailAlloc_1206_, 12, v_extThms_1173_);
lean_ctor_set(v_reuseFailAlloc_1206_, 13, v_ematch_1174_);
lean_ctor_set(v_reuseFailAlloc_1206_, 14, v_inj_1175_);
lean_ctor_set(v_reuseFailAlloc_1206_, 15, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1206_, 16, v_clean_1176_);
lean_ctor_set(v_reuseFailAlloc_1206_, 17, v_sstates_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*18, v_inconsistent_1169_);
v___x_1197_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1197_);
v___x_1199_ = v___x_1158_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_mvarId_1156_);
v___x_1199_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1200_ = lean_st_ref_put(v_a_1051_, v___x_1199_);
v___x_1201_ = lean_box(v_lookahead_1067_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1201_);
v___x_1203_ = v___x_1142_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
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
lean_object* v_val_1213_; lean_object* v___x_1215_; 
lean_inc_ref(v_fst_1144_);
lean_dec(v_a_1140_);
v_val_1213_ = lean_ctor_get(v_fst_1144_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v_fst_1144_, 1);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_val_1213_);
v___x_1215_ = v___x_1142_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_val_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_a_1218_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1139_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1139_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
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
uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_del_object(v___x_1075_);
v___x_1239_ = 0;
v___x_1240_ = lean_box(v___x_1239_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1240_);
v___x_1242_ = v___x_1065_;
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
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1062_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1062_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_Grind_lookahead(v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec(v_a_1255_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1267_, lean_object* v_as_1268_, lean_object* v_as_x27_1269_, lean_object* v_b_1270_, lean_object* v_a_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1267_, v_as_x27_1269_, v_b_1270_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1284_, lean_object* v_as_1285_, lean_object* v_as_x27_1286_, lean_object* v_b_1287_, lean_object* v_a_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_33796__boxed_1300_; lean_object* v_res_1301_; 
v___x_33796__boxed_1300_ = lean_unbox(v___x_1284_);
v_res_1301_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_33796__boxed_1300_, v_as_1285_, v_as_x27_1286_, v_b_1287_, v_a_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v_as_x27_1286_);
lean_dec(v_as_1285_);
return v_res_1301_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
