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
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(lean_object* v___f_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0));
v___x_21_ = l_Lean_Meta_Grind_Action_orElse(v___x_20_, v___f_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
return v___x_21_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_6_ = stack[0].m_obj;
lean_object* v___y_7_ = stack[1].m_obj;
lean_object* v___y_8_ = stack[2].m_obj;
lean_object* v___y_9_ = stack[3].m_obj;
lean_object* v___y_10_ = stack[4].m_obj;
lean_object* v___y_11_ = stack[5].m_obj;
lean_object* v___y_12_ = stack[6].m_obj;
lean_object* v___y_13_ = stack[7].m_obj;
lean_object* v___y_14_ = stack[8].m_obj;
lean_object* v___y_15_ = stack[9].m_obj;
lean_object* v___y_16_ = stack[10].m_obj;
lean_object* v___y_17_ = stack[11].m_obj;
lean_object* v___y_18_ = stack[12].m_obj;
lean_object* v_res_22_;
v_res_22_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(v___f_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(lean_object* v___f_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(v___f_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
return v_res_37_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(lean_object* v_a_38_, lean_object* v___f_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Grind_Action_orElse(v_a_38_, v___f_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
return v___x_53_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_38_ = stack[0].m_obj;
lean_object* v___f_39_ = stack[1].m_obj;
lean_object* v___y_40_ = stack[2].m_obj;
lean_object* v___y_41_ = stack[3].m_obj;
lean_object* v___y_42_ = stack[4].m_obj;
lean_object* v___y_43_ = stack[5].m_obj;
lean_object* v___y_44_ = stack[6].m_obj;
lean_object* v___y_45_ = stack[7].m_obj;
lean_object* v___y_46_ = stack[8].m_obj;
lean_object* v___y_47_ = stack[9].m_obj;
lean_object* v___y_48_ = stack[10].m_obj;
lean_object* v___y_49_ = stack[11].m_obj;
lean_object* v___y_50_ = stack[12].m_obj;
lean_object* v___y_51_ = stack[13].m_obj;
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(v_a_38_, v___f_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(lean_object* v_a_55_, lean_object* v___f_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(v_a_55_, v___f_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
return v_res_70_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(lean_object* v___f_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(10000u);
v___x_86_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_85_, v___f_71_, v___y_72_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_71_ = stack[0].m_obj;
lean_object* v___y_72_ = stack[1].m_obj;
lean_object* v___y_73_ = stack[2].m_obj;
lean_object* v___y_74_ = stack[3].m_obj;
lean_object* v___y_75_ = stack[4].m_obj;
lean_object* v___y_76_ = stack[5].m_obj;
lean_object* v___y_77_ = stack[6].m_obj;
lean_object* v___y_78_ = stack[7].m_obj;
lean_object* v___y_79_ = stack[8].m_obj;
lean_object* v___y_80_ = stack[9].m_obj;
lean_object* v___y_81_ = stack[10].m_obj;
lean_object* v___y_82_ = stack[11].m_obj;
lean_object* v___y_83_ = stack[12].m_obj;
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(v___f_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(lean_object* v___f_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(v___f_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_90_);
return v_res_102_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(lean_object* v___f_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0));
v___x_119_ = l_Lean_Meta_Grind_Action_andThen(v___x_118_, v___f_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
return v___x_119_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_104_ = stack[0].m_obj;
lean_object* v___y_105_ = stack[1].m_obj;
lean_object* v___y_106_ = stack[2].m_obj;
lean_object* v___y_107_ = stack[3].m_obj;
lean_object* v___y_108_ = stack[4].m_obj;
lean_object* v___y_109_ = stack[5].m_obj;
lean_object* v___y_110_ = stack[6].m_obj;
lean_object* v___y_111_ = stack[7].m_obj;
lean_object* v___y_112_ = stack[8].m_obj;
lean_object* v___y_113_ = stack[9].m_obj;
lean_object* v___y_114_ = stack[10].m_obj;
lean_object* v___y_115_ = stack[11].m_obj;
lean_object* v___y_116_ = stack[12].m_obj;
lean_object* v_res_120_;
v_res_120_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(v___f_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(lean_object* v___f_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(v___f_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
return v_res_135_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(lean_object* v___x_136_, lean_object* v___f_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Action_andThen(v___x_136_, v___f_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
return v___x_151_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_136_ = stack[0].m_obj;
lean_object* v___f_137_ = stack[1].m_obj;
lean_object* v___y_138_ = stack[2].m_obj;
lean_object* v___y_139_ = stack[3].m_obj;
lean_object* v___y_140_ = stack[4].m_obj;
lean_object* v___y_141_ = stack[5].m_obj;
lean_object* v___y_142_ = stack[6].m_obj;
lean_object* v___y_143_ = stack[7].m_obj;
lean_object* v___y_144_ = stack[8].m_obj;
lean_object* v___y_145_ = stack[9].m_obj;
lean_object* v___y_146_ = stack[10].m_obj;
lean_object* v___y_147_ = stack[11].m_obj;
lean_object* v___y_148_ = stack[12].m_obj;
lean_object* v___y_149_ = stack[13].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(v___x_136_, v___f_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(lean_object* v___x_153_, lean_object* v___f_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(v___x_153_, v___f_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
return v_res_168_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(lean_object* v_goal_172_, lean_object* v_generation_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_ref_184_; lean_object* v___f_185_; lean_object* v___x_186_; 
v_ref_184_ = lean_ctor_get(v_a_181_, 2);
v___f_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1));
v___x_186_ = l_Lean_Meta_Grind_Solvers_mkAction();
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___x_193_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
v___f_188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed), 15, 2);
lean_closure_set(v___f_188_, 0, v_a_187_);
lean_closure_set(v___f_188_, 1, v___f_185_);
v___f_189_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed), 14, 1);
lean_closure_set(v___f_189_, 0, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed), 14, 1);
lean_closure_set(v___f_190_, 0, v___f_189_);
v___x_191_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_191_, 0, v_generation_173_);
v___f_192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed), 15, 2);
lean_closure_set(v___f_192_, 0, v___x_191_);
lean_closure_set(v___f_192_, 1, v___f_190_);
lean_inc_ref(v_goal_172_);
v___x_193_ = l_Lean_Meta_Grind_Action_run(v_goal_172_, v___f_192_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_220_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_220_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_220_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_220_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
if (lean_obj_tag(v_a_194_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_200_; 
lean_dec_ref_known(v_a_194_, 1);
lean_dec_ref(v_goal_172_);
v___x_198_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
else
{
lean_object* v_gs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_219_; 
v_gs_202_ = lean_ctor_get(v_a_194_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_219_ == 0)
{
v___x_204_ = v_a_194_;
v_isShared_205_ = v_isSharedCheck_219_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_gs_202_);
lean_dec(v_a_194_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_219_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_gs_202_) == 1)
{
lean_object* v_head_206_; lean_object* v___x_208_; 
lean_dec_ref(v_goal_172_);
v_head_206_ = lean_ctor_get(v_gs_202_, 0);
lean_inc(v_head_206_);
lean_dec_ref_known(v_gs_202_, 2);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v_head_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_head_206_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_208_);
v___x_210_ = v___x_196_;
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
else
{
lean_object* v___x_214_; 
lean_dec(v_gs_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v_goal_172_);
v___x_214_ = v___x_204_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_goal_172_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_214_);
v___x_216_ = v___x_196_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_goal_172_);
v_a_221_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_193_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_193_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_generation_173_);
lean_dec_ref(v_goal_172_);
v_a_229_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_240_ == 0)
{
v___x_231_ = v___x_186_;
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_186_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_233_ = lean_io_error_to_string(v_a_229_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = l_Lean_MessageData_ofFormat(v___x_234_);
lean_inc(v_ref_184_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_ref_184_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_236_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_172_ = stack[0].m_obj;
lean_object* v_generation_173_ = stack[1].m_obj;
lean_object* v_a_174_ = stack[2].m_obj;
lean_object* v_a_175_ = stack[3].m_obj;
lean_object* v_a_176_ = stack[4].m_obj;
lean_object* v_a_177_ = stack[5].m_obj;
lean_object* v_a_178_ = stack[6].m_obj;
lean_object* v_a_179_ = stack[7].m_obj;
lean_object* v_a_180_ = stack[8].m_obj;
lean_object* v_a_181_ = stack[9].m_obj;
lean_object* v_a_182_ = stack[10].m_obj;
lean_object* v_res_241_;
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v_goal_172_, v_generation_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(lean_object* v_goal_242_, lean_object* v_generation_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v_goal_242_, v_generation_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
return v_res_254_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(lean_object* v_e_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Expr_hasMVar(v_e_255_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_e_255_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v_mctx_261_; lean_object* v___x_262_; lean_object* v_fst_263_; lean_object* v_snd_264_; lean_object* v___x_265_; lean_object* v_cache_266_; lean_object* v_zetaDeltaFVarIds_267_; lean_object* v_postponed_268_; lean_object* v_diag_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v___x_260_ = lean_st_ref_get(v___y_256_);
v_mctx_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_mctx_261_);
lean_dec(v___x_260_);
v___x_262_ = l_Lean_instantiateMVarsCore(v_mctx_261_, v_e_255_);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
v_snd_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_snd_264_);
lean_dec_ref(v___x_262_);
v___x_265_ = lean_st_ref_take(v___y_256_);
v_cache_266_ = lean_ctor_get(v___x_265_, 1);
v_zetaDeltaFVarIds_267_ = lean_ctor_get(v___x_265_, 2);
v_postponed_268_ = lean_ctor_get(v___x_265_, 3);
v_diag_269_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_279_);
v___x_271_ = v___x_265_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_diag_269_);
lean_inc(v_postponed_268_);
lean_inc(v_zetaDeltaFVarIds_267_);
lean_inc(v_cache_266_);
lean_dec(v___x_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_snd_264_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_snd_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_cache_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_zetaDeltaFVarIds_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_postponed_268_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_diag_269_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_put(v___y_256_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_fst_263_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_255_ = stack[0].m_obj;
lean_object* v___y_256_ = stack[1].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_255_, v___y_256_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg___boxed(lean_object* v_e_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_281_, v___y_282_);
lean_dec(v___y_282_);
return v_res_284_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(lean_object* v_e_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_285_, v___y_293_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_285_ = stack[0].m_obj;
lean_object* v___y_286_ = stack[1].m_obj;
lean_object* v___y_287_ = stack[2].m_obj;
lean_object* v___y_288_ = stack[3].m_obj;
lean_object* v___y_289_ = stack[4].m_obj;
lean_object* v___y_290_ = stack[5].m_obj;
lean_object* v___y_291_ = stack[6].m_obj;
lean_object* v___y_292_ = stack[7].m_obj;
lean_object* v___y_293_ = stack[8].m_obj;
lean_object* v___y_294_ = stack[9].m_obj;
lean_object* v___y_295_ = stack[10].m_obj;
lean_object* v_res_298_;
v_res_298_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(v_e_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___boxed(lean_object* v_e_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(v_e_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec(v___y_300_);
return v_res_311_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(lean_object* v___y_312_, lean_object* v_mctx_313_, lean_object* v_cache_314_, lean_object* v_a_x3f_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_zetaDeltaFVarIds_318_; lean_object* v_postponed_319_; lean_object* v_diag_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v___x_317_ = lean_st_ref_take(v___y_312_);
v_zetaDeltaFVarIds_318_ = lean_ctor_get(v___x_317_, 2);
v_postponed_319_ = lean_ctor_get(v___x_317_, 3);
v_diag_320_ = lean_ctor_get(v___x_317_, 4);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v___x_317_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_332_);
v___x_322_ = v___x_317_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_diag_320_);
lean_inc(v_postponed_319_);
lean_inc(v_zetaDeltaFVarIds_318_);
lean_dec(v___x_317_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v_cache_314_);
lean_ctor_set(v___x_322_, 0, v_mctx_313_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_mctx_313_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_cache_314_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_zetaDeltaFVarIds_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_postponed_319_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v_diag_320_);
v___x_326_ = v_reuseFailAlloc_329_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_st_ref_put(v___y_312_, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_312_ = stack[0].m_obj;
lean_object* v_mctx_313_ = stack[1].m_obj;
lean_object* v_cache_314_ = stack[2].m_obj;
lean_object* v_a_x3f_315_ = stack[3].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_312_, v_mctx_313_, v_cache_314_, v_a_x3f_315_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0___boxed(lean_object* v___y_334_, lean_object* v_mctx_335_, lean_object* v_cache_336_, lean_object* v_a_x3f_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_334_, v_mctx_335_, v_cache_336_, v_a_x3f_337_);
lean_dec(v_a_x3f_337_);
lean_dec(v___y_334_);
return v_res_339_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_mctx_353_; lean_object* v___x_354_; lean_object* v_cache_355_; lean_object* v___x_356_; 
v___x_352_ = lean_st_ref_get(v___y_348_);
v_mctx_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_352_);
v___x_354_ = lean_st_ref_get(v___y_348_);
v_cache_355_ = lean_ctor_get(v___x_354_, 1);
lean_inc_ref(v_cache_355_);
lean_dec(v___x_354_);
lean_inc(v___y_350_);
lean_inc_ref(v___y_349_);
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
lean_inc(v___y_346_);
lean_inc_ref(v___y_345_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc(v___y_341_);
v___x_356_ = lean_apply_11(v_x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, lean_box(0));
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_373_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_373_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
lean_inc(v_a_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_372_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v___x_363_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_348_, v_mctx_353_, v_cache_355_, v___x_362_);
lean_dec_ref(v___x_362_);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_371_);
v___x_365_ = v___x_363_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_a_357_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_357_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_a_374_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_356_, 1);
v___x_375_ = lean_box(0);
v___x_376_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_348_, v_mctx_353_, v_cache_355_, v___x_375_);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_376_, 0);
lean_dec(v_unused_384_);
v___x_378_ = v___x_376_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_dec(v___x_376_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 1);
lean_ctor_set(v___x_378_, 0, v_a_374_);
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_374_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_340_ = stack[0].m_obj;
lean_object* v___y_341_ = stack[1].m_obj;
lean_object* v___y_342_ = stack[2].m_obj;
lean_object* v___y_343_ = stack[3].m_obj;
lean_object* v___y_344_ = stack[4].m_obj;
lean_object* v___y_345_ = stack[5].m_obj;
lean_object* v___y_346_ = stack[6].m_obj;
lean_object* v___y_347_ = stack[7].m_obj;
lean_object* v___y_348_ = stack[8].m_obj;
lean_object* v___y_349_ = stack[9].m_obj;
lean_object* v___y_350_ = stack[10].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___boxed(lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec(v___y_387_);
return v_res_398_;
}
}
lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(lean_object* v_00_u03b1_399_, lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_400_ = stack[1].m_obj;
lean_object* v___y_401_ = stack[2].m_obj;
lean_object* v___y_402_ = stack[3].m_obj;
lean_object* v___y_403_ = stack[4].m_obj;
lean_object* v___y_404_ = stack[5].m_obj;
lean_object* v___y_405_ = stack[6].m_obj;
lean_object* v___y_406_ = stack[7].m_obj;
lean_object* v___y_407_ = stack[8].m_obj;
lean_object* v___y_408_ = stack[9].m_obj;
lean_object* v___y_409_ = stack[10].m_obj;
lean_object* v___y_410_ = stack[11].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(lean_box(0), v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___boxed(lean_object* v_00_u03b1_414_, lean_object* v_x_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(v_00_u03b1_414_, v_x_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec(v___y_416_);
return v_res_427_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(lean_object* v_mvarId_430_, lean_object* v_e_431_, lean_object* v_toGoalState_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_MVarId_getTag(v_mvarId_430_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_437_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
lean_inc_ref(v_e_431_);
v___x_448_ = l_Lean_mkNot(v_e_431_);
v___x_449_ = l_Lean_mkArrow(v___x_448_, v_a_447_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_450_, v_a_445_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v_nextDeclIdx_453_; lean_object* v_enodeMap_454_; lean_object* v_exprs_455_; lean_object* v_parents_456_; lean_object* v_congrTable_457_; lean_object* v_appMap_458_; lean_object* v_indicesFound_459_; uint8_t v_inconsistent_460_; lean_object* v_nextIdx_461_; lean_object* v_newRawFacts_462_; lean_object* v_facts_463_; lean_object* v_extThms_464_; lean_object* v_ematch_465_; lean_object* v_inj_466_; lean_object* v_split_467_; lean_object* v_clean_468_; lean_object* v_sstates_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_517_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v_nextDeclIdx_453_ = lean_ctor_get(v_toGoalState_432_, 0);
v_enodeMap_454_ = lean_ctor_get(v_toGoalState_432_, 1);
v_exprs_455_ = lean_ctor_get(v_toGoalState_432_, 2);
v_parents_456_ = lean_ctor_get(v_toGoalState_432_, 3);
v_congrTable_457_ = lean_ctor_get(v_toGoalState_432_, 4);
v_appMap_458_ = lean_ctor_get(v_toGoalState_432_, 5);
v_indicesFound_459_ = lean_ctor_get(v_toGoalState_432_, 6);
v_inconsistent_460_ = lean_ctor_get_uint8(v_toGoalState_432_, sizeof(void*)*17);
v_nextIdx_461_ = lean_ctor_get(v_toGoalState_432_, 8);
v_newRawFacts_462_ = lean_ctor_get(v_toGoalState_432_, 9);
v_facts_463_ = lean_ctor_get(v_toGoalState_432_, 10);
v_extThms_464_ = lean_ctor_get(v_toGoalState_432_, 11);
v_ematch_465_ = lean_ctor_get(v_toGoalState_432_, 12);
v_inj_466_ = lean_ctor_get(v_toGoalState_432_, 13);
v_split_467_ = lean_ctor_get(v_toGoalState_432_, 14);
v_clean_468_ = lean_ctor_get(v_toGoalState_432_, 15);
v_sstates_469_ = lean_ctor_get(v_toGoalState_432_, 16);
v_isSharedCheck_517_ = !lean_is_exclusive(v_toGoalState_432_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_toGoalState_432_, 7);
lean_dec(v_unused_518_);
v___x_471_ = v_toGoalState_432_;
v_isShared_472_ = v_isSharedCheck_517_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_sstates_469_);
lean_inc(v_clean_468_);
lean_inc(v_split_467_);
lean_inc(v_inj_466_);
lean_inc(v_ematch_465_);
lean_inc(v_extThms_464_);
lean_inc(v_facts_463_);
lean_inc(v_newRawFacts_462_);
lean_inc(v_nextIdx_461_);
lean_inc(v_indicesFound_459_);
lean_inc(v_appMap_458_);
lean_inc(v_congrTable_457_);
lean_inc(v_parents_456_);
lean_inc(v_exprs_455_);
lean_inc(v_enodeMap_454_);
lean_inc(v_nextDeclIdx_453_);
lean_dec(v_toGoalState_432_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_517_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0));
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 7, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_nextDeclIdx_453_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_enodeMap_454_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_exprs_455_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_parents_456_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_congrTable_457_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v_appMap_458_);
lean_ctor_set(v_reuseFailAlloc_516_, 6, v_indicesFound_459_);
lean_ctor_set(v_reuseFailAlloc_516_, 7, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_516_, 8, v_nextIdx_461_);
lean_ctor_set(v_reuseFailAlloc_516_, 9, v_newRawFacts_462_);
lean_ctor_set(v_reuseFailAlloc_516_, 10, v_facts_463_);
lean_ctor_set(v_reuseFailAlloc_516_, 11, v_extThms_464_);
lean_ctor_set(v_reuseFailAlloc_516_, 12, v_ematch_465_);
lean_ctor_set(v_reuseFailAlloc_516_, 13, v_inj_466_);
lean_ctor_set(v_reuseFailAlloc_516_, 14, v_split_467_);
lean_ctor_set(v_reuseFailAlloc_516_, 15, v_clean_468_);
lean_ctor_set(v_reuseFailAlloc_516_, 16, v_sstates_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_516_, sizeof(void*)*17, v_inconsistent_460_);
v___x_475_ = v_reuseFailAlloc_516_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = l_Lean_Expr_mvarId_x21(v_a_452_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_431_, v___y_433_);
lean_dec_ref(v_e_431_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_477_, v_a_479_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_499_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_499_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_499_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_499_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
if (lean_obj_tag(v_a_481_) == 0)
{
lean_object* v___x_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
lean_del_object(v___x_483_);
v___x_485_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_452_, v___y_440_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_494_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_a_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_497_; 
lean_dec_ref_known(v_a_481_, 1);
lean_dec(v_a_452_);
v___x_495_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_495_);
v___x_497_ = v___x_483_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_452_);
v_a_500_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_480_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_480_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref_known(v___x_477_, 2);
lean_dec(v_a_452_);
v_a_508_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_478_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_478_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
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
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_toGoalState_432_);
lean_dec_ref(v_e_431_);
v_a_519_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_451_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_451_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_445_);
lean_dec_ref(v_toGoalState_432_);
lean_dec_ref(v_e_431_);
v_a_527_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_449_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_449_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_445_);
lean_dec_ref(v_toGoalState_432_);
lean_dec_ref(v_e_431_);
v_a_535_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_446_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_446_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v_toGoalState_432_);
lean_dec_ref(v_e_431_);
v_a_543_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_444_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_444_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_430_ = stack[0].m_obj;
lean_object* v_e_431_ = stack[1].m_obj;
lean_object* v_toGoalState_432_ = stack[2].m_obj;
lean_object* v___y_433_ = stack[3].m_obj;
lean_object* v___y_434_ = stack[4].m_obj;
lean_object* v___y_435_ = stack[5].m_obj;
lean_object* v___y_436_ = stack[6].m_obj;
lean_object* v___y_437_ = stack[7].m_obj;
lean_object* v___y_438_ = stack[8].m_obj;
lean_object* v___y_439_ = stack[9].m_obj;
lean_object* v___y_440_ = stack[10].m_obj;
lean_object* v___y_441_ = stack[11].m_obj;
lean_object* v___y_442_ = stack[12].m_obj;
lean_object* v_res_551_;
v_res_551_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_430_, v_e_431_, v_toGoalState_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* v_mvarId_552_, lean_object* v_e_553_, lean_object* v_toGoalState_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_552_, v_e_553_, v_toGoalState_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
return v_res_566_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_env_574_; uint8_t v___x_575_; lean_object* v_env_576_; lean_object* v___x_577_; lean_object* v_toCold_578_; lean_object* v_mctx_579_; lean_object* v_lctx_580_; lean_object* v_options_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_573_);
v___x_575_ = 0;
v_env_576_ = l_Lean_Environment_setRecordingDeps(v_env_574_, v___x_575_);
v___x_577_ = lean_st_ref_get(v___y_569_);
v_toCold_578_ = lean_ctor_get(v___y_570_, 0);
v_mctx_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_mctx_579_);
lean_dec(v___x_577_);
v_lctx_580_ = lean_ctor_get(v___y_568_, 2);
v_options_581_ = lean_ctor_get(v_toCold_578_, 2);
lean_inc_ref(v_options_581_);
lean_inc_ref(v_lctx_580_);
v___x_582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_582_, 0, v_env_576_);
lean_ctor_set(v___x_582_, 1, v_mctx_579_);
lean_ctor_set(v___x_582_, 2, v_lctx_580_);
lean_ctor_set(v___x_582_, 3, v_options_581_);
v___x_583_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_msgData_567_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_567_ = stack[0].m_obj;
lean_object* v___y_568_ = stack[1].m_obj;
lean_object* v___y_569_ = stack[2].m_obj;
lean_object* v___y_570_ = stack[3].m_obj;
lean_object* v___y_571_ = stack[4].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object* v_msgData_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_593_; double v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_float_of_nat(v___x_593_);
return v___x_594_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_598_, lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_652_; 
v_ref_605_ = lean_ctor_get(v___y_602_, 2);
v___x_606_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_652_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_652_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_652_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_recordedDeps_618_; lean_object* v_messages_619_; lean_object* v_infoState_620_; lean_object* v_snapshotTasks_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_651_; 
v___x_611_ = lean_st_ref_take(v___y_603_);
v_traceState_612_ = lean_ctor_get(v___x_611_, 4);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_cache_617_ = lean_ctor_get(v___x_611_, 5);
v_recordedDeps_618_ = lean_ctor_get(v___x_611_, 6);
v_messages_619_ = lean_ctor_get(v___x_611_, 7);
v_infoState_620_ = lean_ctor_get(v___x_611_, 8);
v_snapshotTasks_621_ = lean_ctor_get(v___x_611_, 9);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_651_ == 0)
{
v___x_623_ = v___x_611_;
v_isShared_624_ = v_isSharedCheck_651_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snapshotTasks_621_);
lean_inc(v_infoState_620_);
lean_inc(v_messages_619_);
lean_inc(v_recordedDeps_618_);
lean_inc(v_cache_617_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_651_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint64_t v_tid_625_; lean_object* v_traces_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_650_; 
v_tid_625_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_626_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_650_ == 0)
{
v___x_628_ = v_traceState_612_;
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_traces_626_);
lean_dec(v_traceState_612_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; double v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_box(0);
v___x_632_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
v___x_633_ = 0;
v___x_634_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_635_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_635_, 0, v_cls_598_);
lean_ctor_set(v___x_635_, 1, v___x_631_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
lean_ctor_set_float(v___x_635_, sizeof(void*)*3, v___x_632_);
lean_ctor_set_float(v___x_635_, sizeof(void*)*3 + 8, v___x_632_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3 + 16, v___x_633_);
v___x_636_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2));
v___x_637_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v_a_607_);
lean_ctor_set(v___x_637_, 2, v___x_636_);
lean_inc(v_ref_605_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_ref_605_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_PersistentArray_push___redArg(v_traces_626_, v___x_638_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_639_);
v___x_641_ = v___x_628_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_639_);
lean_ctor_set_uint64(v_reuseFailAlloc_649_, sizeof(void*)*1, v_tid_625_);
v___x_641_ = v_reuseFailAlloc_649_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___x_641_);
v___x_643_ = v___x_623_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_648_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_648_, 6, v_recordedDeps_618_);
lean_ctor_set(v_reuseFailAlloc_648_, 7, v_messages_619_);
lean_ctor_set(v_reuseFailAlloc_648_, 8, v_infoState_620_);
lean_ctor_set(v_reuseFailAlloc_648_, 9, v_snapshotTasks_621_);
v___x_643_ = v_reuseFailAlloc_648_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_st_ref_put(v___y_603_, v___x_643_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_630_);
v___x_646_ = v___x_609_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_630_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_598_ = stack[0].m_obj;
lean_object* v_msg_599_ = stack[1].m_obj;
lean_object* v___y_600_ = stack[2].m_obj;
lean_object* v___y_601_ = stack[3].m_obj;
lean_object* v___y_602_ = stack[4].m_obj;
lean_object* v___y_603_ = stack[5].m_obj;
lean_object* v_res_653_;
v_res_653_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_598_, v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
stack->m_obj
 = v_res_653_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_654_, v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_box(0);
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_671_ = l_Lean_mkConst(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_684_ = l_Lean_Name_append(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14(void){
_start:
{
lean_object* v_cls_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_cls_690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_692_ = l_Lean_Name_append(v___x_691_, v_cls_690_);
return v___x_692_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_config_747_; lean_object* v_toCold_748_; lean_object* v_options_749_; lean_object* v_simp_750_; lean_object* v_simpMethods_751_; lean_object* v_symSimpMethods_752_; lean_object* v_symDSimpMethods_753_; lean_object* v_anchorRefs_x3f_754_; uint8_t v_reportMVarIssue_755_; lean_object* v_splitSource_756_; lean_object* v_ematchDiagSource_757_; lean_object* v_symPrios_758_; lean_object* v_extensions_759_; uint8_t v_debug_760_; uint8_t v_ematchDiag_761_; uint8_t v_trace_762_; uint8_t v_markInstances_763_; uint8_t v_lax_764_; uint8_t v_suggestions_765_; uint8_t v_locals_766_; lean_object* v_splits_767_; lean_object* v_ematch_768_; lean_object* v_gen_769_; lean_object* v_genLocal_770_; lean_object* v_instances_771_; uint8_t v_matchEqs_772_; uint8_t v_splitMatch_773_; uint8_t v_splitIte_774_; uint8_t v_splitIndPred_775_; uint8_t v_splitImp_776_; lean_object* v_canonHeartbeats_777_; uint8_t v_ext_778_; uint8_t v_extAll_779_; uint8_t v_etaStruct_780_; uint8_t v_funext_781_; uint8_t v_lookahead_782_; uint8_t v_verbose_783_; uint8_t v_clean_784_; uint8_t v_mbtc_785_; uint8_t v_zetaDelta_786_; uint8_t v_zeta_787_; uint8_t v_ring_788_; lean_object* v_ringSteps_789_; lean_object* v_ringMaxDegree_790_; uint8_t v_linarith_791_; uint8_t v_lia_792_; lean_object* v_liaSteps_793_; uint8_t v_hom_794_; uint8_t v_ac_795_; lean_object* v_acSteps_796_; lean_object* v_exp_797_; uint8_t v_abstractProof_798_; uint8_t v_inj_799_; uint8_t v_order_800_; lean_object* v_min_801_; lean_object* v_detailed_802_; uint8_t v_useSorry_803_; uint8_t v_revert_804_; uint8_t v_funCC_805_; uint8_t v_reducible_806_; lean_object* v_maxSuggestions_807_; lean_object* v_inheritedTraceOptions_808_; uint8_t v_hasTrace_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_865_; 
v_config_747_ = lean_ctor_get(v_a_696_, 4);
v_toCold_748_ = lean_ctor_get(v_a_702_, 0);
v_options_749_ = lean_ctor_get(v_toCold_748_, 2);
v_simp_750_ = lean_ctor_get(v_a_696_, 0);
v_simpMethods_751_ = lean_ctor_get(v_a_696_, 1);
v_symSimpMethods_752_ = lean_ctor_get(v_a_696_, 2);
v_symDSimpMethods_753_ = lean_ctor_get(v_a_696_, 3);
v_anchorRefs_x3f_754_ = lean_ctor_get(v_a_696_, 5);
v_reportMVarIssue_755_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*10 + 1);
v_splitSource_756_ = lean_ctor_get(v_a_696_, 6);
v_ematchDiagSource_757_ = lean_ctor_get(v_a_696_, 7);
v_symPrios_758_ = lean_ctor_get(v_a_696_, 8);
v_extensions_759_ = lean_ctor_get(v_a_696_, 9);
v_debug_760_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*10 + 2);
v_ematchDiag_761_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*10 + 3);
v_trace_762_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14);
v_markInstances_763_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 1);
v_lax_764_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 2);
v_suggestions_765_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 3);
v_locals_766_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 4);
v_splits_767_ = lean_ctor_get(v_config_747_, 0);
v_ematch_768_ = lean_ctor_get(v_config_747_, 1);
v_gen_769_ = lean_ctor_get(v_config_747_, 2);
v_genLocal_770_ = lean_ctor_get(v_config_747_, 3);
v_instances_771_ = lean_ctor_get(v_config_747_, 4);
v_matchEqs_772_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 5);
v_splitMatch_773_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 6);
v_splitIte_774_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 7);
v_splitIndPred_775_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 8);
v_splitImp_776_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 9);
v_canonHeartbeats_777_ = lean_ctor_get(v_config_747_, 5);
v_ext_778_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 10);
v_extAll_779_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 11);
v_etaStruct_780_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 12);
v_funext_781_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 13);
v_lookahead_782_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 14);
v_verbose_783_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 15);
v_clean_784_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 16);
v_mbtc_785_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 18);
v_zetaDelta_786_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 19);
v_zeta_787_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 20);
v_ring_788_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 21);
v_ringSteps_789_ = lean_ctor_get(v_config_747_, 6);
v_ringMaxDegree_790_ = lean_ctor_get(v_config_747_, 7);
v_linarith_791_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 22);
v_lia_792_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 23);
v_liaSteps_793_ = lean_ctor_get(v_config_747_, 8);
v_hom_794_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 24);
v_ac_795_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 25);
v_acSteps_796_ = lean_ctor_get(v_config_747_, 9);
v_exp_797_ = lean_ctor_get(v_config_747_, 10);
v_abstractProof_798_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 26);
v_inj_799_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 27);
v_order_800_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 28);
v_min_801_ = lean_ctor_get(v_config_747_, 11);
v_detailed_802_ = lean_ctor_get(v_config_747_, 12);
v_useSorry_803_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 29);
v_revert_804_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 30);
v_funCC_805_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 31);
v_reducible_806_ = lean_ctor_get_uint8(v_config_747_, sizeof(void*)*14 + 32);
v_maxSuggestions_807_ = lean_ctor_get(v_config_747_, 13);
v_inheritedTraceOptions_808_ = lean_ctor_get(v_toCold_748_, 11);
v_hasTrace_809_ = lean_ctor_get_uint8(v_options_749_, sizeof(void*)*1);
v___x_810_ = 1;
lean_inc(v_maxSuggestions_807_);
lean_inc(v_detailed_802_);
lean_inc(v_min_801_);
lean_inc(v_exp_797_);
lean_inc(v_acSteps_796_);
lean_inc(v_liaSteps_793_);
lean_inc(v_ringMaxDegree_790_);
lean_inc(v_ringSteps_789_);
lean_inc(v_canonHeartbeats_777_);
lean_inc(v_instances_771_);
lean_inc(v_genLocal_770_);
lean_inc(v_gen_769_);
lean_inc(v_ematch_768_);
lean_inc(v_splits_767_);
v___x_811_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_811_, 0, v_splits_767_);
lean_ctor_set(v___x_811_, 1, v_ematch_768_);
lean_ctor_set(v___x_811_, 2, v_gen_769_);
lean_ctor_set(v___x_811_, 3, v_genLocal_770_);
lean_ctor_set(v___x_811_, 4, v_instances_771_);
lean_ctor_set(v___x_811_, 5, v_canonHeartbeats_777_);
lean_ctor_set(v___x_811_, 6, v_ringSteps_789_);
lean_ctor_set(v___x_811_, 7, v_ringMaxDegree_790_);
lean_ctor_set(v___x_811_, 8, v_liaSteps_793_);
lean_ctor_set(v___x_811_, 9, v_acSteps_796_);
lean_ctor_set(v___x_811_, 10, v_exp_797_);
lean_ctor_set(v___x_811_, 11, v_min_801_);
lean_ctor_set(v___x_811_, 12, v_detailed_802_);
lean_ctor_set(v___x_811_, 13, v_maxSuggestions_807_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14, v_trace_762_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 1, v_markInstances_763_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 2, v_lax_764_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 3, v_suggestions_765_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 4, v_locals_766_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 5, v_matchEqs_772_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 6, v_splitMatch_773_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 7, v_splitIte_774_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 8, v_splitIndPred_775_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 9, v_splitImp_776_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 10, v_ext_778_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 11, v_extAll_779_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 12, v_etaStruct_780_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 13, v_funext_781_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 14, v_lookahead_782_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 15, v_verbose_783_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 16, v_clean_784_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 17, v___x_810_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 18, v_mbtc_785_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 19, v_zetaDelta_786_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 20, v_zeta_787_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 21, v_ring_788_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 22, v_linarith_791_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 23, v_lia_792_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 24, v_hom_794_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 25, v_ac_795_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 26, v_abstractProof_798_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 27, v_inj_799_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 28, v_order_800_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 29, v_useSorry_803_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 30, v_revert_804_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 31, v_funCC_805_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 32, v_reducible_806_);
lean_inc_ref(v_extensions_759_);
lean_inc_ref(v_symPrios_758_);
lean_inc(v_ematchDiagSource_757_);
lean_inc(v_splitSource_756_);
lean_inc(v_anchorRefs_x3f_754_);
lean_inc_ref(v_symDSimpMethods_753_);
lean_inc_ref(v_symSimpMethods_752_);
lean_inc_ref(v_simpMethods_751_);
lean_inc_ref(v_simp_750_);
v___x_865_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_865_, 0, v_simp_750_);
lean_ctor_set(v___x_865_, 1, v_simpMethods_751_);
lean_ctor_set(v___x_865_, 2, v_symSimpMethods_752_);
lean_ctor_set(v___x_865_, 3, v_symDSimpMethods_753_);
lean_ctor_set(v___x_865_, 4, v___x_811_);
lean_ctor_set(v___x_865_, 5, v_anchorRefs_x3f_754_);
lean_ctor_set(v___x_865_, 6, v_splitSource_756_);
lean_ctor_set(v___x_865_, 7, v_ematchDiagSource_757_);
lean_ctor_set(v___x_865_, 8, v_symPrios_758_);
lean_ctor_set(v___x_865_, 9, v_extensions_759_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*10, v___x_810_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*10 + 1, v_reportMVarIssue_755_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*10 + 2, v_debug_760_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*10 + 3, v_ematchDiag_761_);
if (v_hasTrace_809_ == 0)
{
v___y_813_ = v_a_694_;
v___y_814_ = v_a_695_;
v___y_815_ = v___x_865_;
v___y_816_ = v_a_697_;
v___y_817_ = v_a_698_;
v___y_818_ = v_a_699_;
v___y_819_ = v_a_700_;
v___y_820_ = v_a_701_;
v___y_821_ = v_a_702_;
v___y_822_ = v_a_703_;
goto v___jp_812_;
}
else
{
lean_object* v_cls_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_cls_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
v___x_868_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_808_, v_options_749_, v___x_867_);
if (v___x_868_ == 0)
{
v___y_813_ = v_a_694_;
v___y_814_ = v_a_695_;
v___y_815_ = v___x_865_;
v___y_816_ = v_a_697_;
v___y_817_ = v_a_698_;
v___y_818_ = v_a_699_;
v___y_819_ = v_a_700_;
v___y_820_ = v_a_701_;
v___y_821_ = v_a_702_;
v___y_822_ = v_a_703_;
goto v___jp_812_;
}
else
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Grind_updateLastTag(v_a_694_, v_a_695_, v___x_865_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref_known(v___x_869_, 1);
lean_inc_ref(v_e_693_);
v___x_870_ = l_Lean_MessageData_ofExpr(v_e_693_);
v___x_871_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_866_, v___x_870_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_dec_ref_known(v___x_871_, 1);
v___y_813_ = v_a_694_;
v___y_814_ = v_a_695_;
v___y_815_ = v___x_865_;
v___y_816_ = v_a_697_;
v___y_817_ = v_a_698_;
v___y_818_ = v_a_699_;
v___y_819_ = v_a_700_;
v___y_820_ = v_a_701_;
v___y_821_ = v_a_702_;
v___y_822_ = v_a_703_;
goto v___jp_812_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref_known(v___x_865_, 10);
lean_dec_ref(v_e_693_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref_known(v___x_865_, 10);
lean_dec_ref(v_e_693_);
v_a_880_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_869_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_869_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
v___jp_705_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_693_);
v___x_718_ = l_Lean_mkAppB(v___x_717_, v_e_693_, v___y_706_);
v___x_719_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_693_, v___x_718_, v___y_707_, v___y_709_, v___y_711_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; 
lean_dec_ref_known(v___x_719_, 1);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc(v___y_708_);
lean_inc(v___y_707_);
v___x_720_ = lean_grind_process_to_do(v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_729_; 
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_730_);
v___x_722_ = v___x_720_;
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
else
{
lean_dec(v___x_720_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = 1;
v___x_725_ = lean_box(v___x_724_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_720_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_720_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___y_709_);
v_a_739_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_719_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_719_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
v___jp_812_:
{
lean_object* v___x_823_; lean_object* v_toGoalState_824_; lean_object* v_mvarId_825_; lean_object* v___f_826_; lean_object* v___x_827_; 
v___x_823_ = lean_st_ref_get(v___y_813_);
v_toGoalState_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_toGoalState_824_);
v_mvarId_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_mvarId_825_);
lean_dec(v___x_823_);
lean_inc_ref(v_e_693_);
v___f_826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_826_, 0, v_mvarId_825_);
lean_closure_set(v___f_826_, 1, v_e_693_);
lean_closure_set(v___f_826_, 2, v_toGoalState_824_);
v___x_827_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_826_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_856_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_856_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_856_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_856_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
if (lean_obj_tag(v_a_828_) == 1)
{
lean_object* v_toCold_832_; lean_object* v_options_833_; uint8_t v_hasTrace_834_; 
lean_del_object(v___x_830_);
v_toCold_832_ = lean_ctor_get(v___y_821_, 0);
v_options_833_ = lean_ctor_get(v_toCold_832_, 2);
v_hasTrace_834_ = lean_ctor_get_uint8(v_options_833_, sizeof(void*)*1);
if (v_hasTrace_834_ == 0)
{
lean_object* v_val_835_; 
v_val_835_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_a_828_, 1);
v___y_706_ = v_val_835_;
v___y_707_ = v___y_813_;
v___y_708_ = v___y_814_;
v___y_709_ = v___y_815_;
v___y_710_ = v___y_816_;
v___y_711_ = v___y_817_;
v___y_712_ = v___y_818_;
v___y_713_ = v___y_819_;
v___y_714_ = v___y_820_;
v___y_715_ = v___y_821_;
v___y_716_ = v___y_822_;
goto v___jp_705_;
}
else
{
lean_object* v_val_836_; lean_object* v_inheritedTraceOptions_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_val_836_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_a_828_, 1);
v_inheritedTraceOptions_837_ = lean_ctor_get(v_toCold_832_, 11);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
v___x_840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_837_, v_options_833_, v___x_839_);
if (v___x_840_ == 0)
{
v___y_706_ = v_val_836_;
v___y_707_ = v___y_813_;
v___y_708_ = v___y_814_;
v___y_709_ = v___y_815_;
v___y_710_ = v___y_816_;
v___y_711_ = v___y_817_;
v___y_712_ = v___y_818_;
v___y_713_ = v___y_819_;
v___y_714_ = v___y_820_;
v___y_715_ = v___y_821_;
v___y_716_ = v___y_822_;
goto v___jp_705_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc_ref(v_e_693_);
v___x_841_ = l_Lean_MessageData_ofExpr(v_e_693_);
v___x_842_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_838_, v___x_841_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref_known(v___x_842_, 1);
v___y_706_ = v_val_836_;
v___y_707_ = v___y_813_;
v___y_708_ = v___y_814_;
v___y_709_ = v___y_815_;
v___y_710_ = v___y_816_;
v___y_711_ = v___y_817_;
v___y_712_ = v___y_818_;
v___y_713_ = v___y_819_;
v___y_714_ = v___y_820_;
v___y_715_ = v___y_821_;
v___y_716_ = v___y_822_;
goto v___jp_705_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_val_836_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_e_693_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec(v_a_828_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_e_693_);
v___x_851_ = 0;
v___x_852_ = lean_box(v___x_851_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_852_);
v___x_854_ = v___x_830_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___y_815_);
lean_dec_ref(v_e_693_);
v_a_857_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_827_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_827_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_693_ = stack[0].m_obj;
lean_object* v_a_694_ = stack[1].m_obj;
lean_object* v_a_695_ = stack[2].m_obj;
lean_object* v_a_696_ = stack[3].m_obj;
lean_object* v_a_697_ = stack[4].m_obj;
lean_object* v_a_698_ = stack[5].m_obj;
lean_object* v_a_699_ = stack[6].m_obj;
lean_object* v_a_700_ = stack[7].m_obj;
lean_object* v_a_701_ = stack[8].m_obj;
lean_object* v_a_702_ = stack[9].m_obj;
lean_object* v_a_703_ = stack[10].m_obj;
lean_object* v_res_888_;
v_res_888_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
return v_res_901_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_902_, lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_902_, v_msg_903_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_902_ = stack[0].m_obj;
lean_object* v_msg_903_ = stack[1].m_obj;
lean_object* v___y_904_ = stack[2].m_obj;
lean_object* v___y_905_ = stack[3].m_obj;
lean_object* v___y_906_ = stack[4].m_obj;
lean_object* v___y_907_ = stack[5].m_obj;
lean_object* v___y_908_ = stack[6].m_obj;
lean_object* v___y_909_ = stack[7].m_obj;
lean_object* v___y_910_ = stack[8].m_obj;
lean_object* v___y_911_ = stack[9].m_obj;
lean_object* v___y_912_ = stack[10].m_obj;
lean_object* v___y_913_ = stack[11].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_902_, v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_917_, lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_917_, v_msg_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec(v___y_919_);
return v_res_930_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_931_, lean_object* v_as_x27_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
if (lean_obj_tag(v_as_x27_932_) == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_b_933_);
return v___x_945_;
}
else
{
lean_object* v_snd_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1048_; 
v_snd_946_ = lean_ctor_get(v_b_933_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_b_933_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_b_933_, 0);
lean_dec(v_unused_1049_);
v___x_948_ = v_b_933_;
v_isShared_949_ = v_isSharedCheck_1048_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_946_);
lean_dec(v_b_933_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1048_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_head_950_; lean_object* v_tail_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1047_; 
v_head_950_ = lean_ctor_get(v_as_x27_932_, 0);
v_tail_951_ = lean_ctor_get(v_as_x27_932_, 1);
v_fst_952_ = lean_ctor_get(v_snd_946_, 0);
v_snd_953_ = lean_ctor_get(v_snd_946_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_snd_946_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_955_ = v_snd_946_;
v_isShared_956_ = v_isSharedCheck_1047_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_dec(v_snd_946_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1047_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_box(0);
v___x_958_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_934_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1038_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1038_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1038_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___x_963_; 
v___x_963_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_del_object(v___x_961_);
lean_inc(v_head_950_);
v___x_964_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_950_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
switch(lean_obj_tag(v_a_965_))
{
case 0:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v_snd_953_);
v___x_966_ = lean_box(v___x_931_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_966_);
v___x_968_ = v___x_955_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_973_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_968_);
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_970_ = v___x_948_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_as_x27_932_ = v_tail_951_;
v_b_933_ = v___x_970_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_inc(v_head_950_);
v___x_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_974_, 0, v_head_950_);
lean_ctor_set(v___x_974_, 1, v_fst_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_974_);
v___x_976_ = v___x_955_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_snd_953_);
v___x_976_ = v_reuseFailAlloc_981_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_976_);
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_978_ = v___x_948_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
v_as_x27_932_ = v_tail_951_;
v_b_933_ = v___x_978_;
goto _start;
}
}
}
default: 
{
uint8_t v_tryPostpone_982_; 
v_tryPostpone_982_ = lean_ctor_get_uint8(v_a_965_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_965_, 1);
if (v_tryPostpone_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_950_);
v___x_984_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_983_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = lean_unbox(v_a_985_);
lean_dec(v_a_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_inc(v_head_950_);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v_head_950_);
lean_ctor_set(v___x_987_, 1, v_fst_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_987_);
v___x_989_ = v___x_955_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_snd_953_);
v___x_989_ = v_reuseFailAlloc_994_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_989_);
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_991_ = v___x_948_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_as_x27_932_ = v_tail_951_;
v_b_933_ = v___x_991_;
goto _start;
}
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec(v_snd_953_);
v___x_995_ = lean_box(v___x_931_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_995_);
v___x_997_ = v___x_955_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1002_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_997_);
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_999_ = v___x_948_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
v_as_x27_932_ = v_tail_951_;
v_b_933_ = v___x_999_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_fst_952_);
lean_del_object(v___x_948_);
v_a_1003_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_984_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_984_);
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
else
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_inc(v_head_950_);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_head_950_);
lean_ctor_set(v___x_1011_, 1, v_fst_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_1011_);
v___x_1013_ = v___x_955_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_snd_953_);
v___x_1013_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_1013_);
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_1015_ = v___x_948_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v_as_x27_932_ = v_tail_951_;
v_b_933_ = v___x_1015_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_fst_952_);
lean_del_object(v___x_948_);
v_a_1019_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_964_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_964_);
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
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_box(v___x_931_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
if (v_isShared_956_ == 0)
{
v___x_1030_ = v___x_955_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_snd_953_);
v___x_1030_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_1030_);
lean_ctor_set(v___x_948_, 0, v___x_1028_);
v___x_1032_ = v___x_948_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_1032_);
v___x_1034_ = v___x_961_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_fst_952_);
lean_del_object(v___x_948_);
v_a_1039_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_958_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_958_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_931_ = stack[0].m_num;
lean_object* v_as_x27_932_ = stack[1].m_obj;
lean_object* v_b_933_ = stack[2].m_obj;
lean_object* v___y_934_ = stack[3].m_obj;
lean_object* v___y_935_ = stack[4].m_obj;
lean_object* v___y_936_ = stack[5].m_obj;
lean_object* v___y_937_ = stack[6].m_obj;
lean_object* v___y_938_ = stack[7].m_obj;
lean_object* v___y_939_ = stack[8].m_obj;
lean_object* v___y_940_ = stack[9].m_obj;
lean_object* v___y_941_ = stack[10].m_obj;
lean_object* v___y_942_ = stack[11].m_obj;
lean_object* v___y_943_ = stack[12].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_931_, v_as_x27_932_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1051_, lean_object* v_as_x27_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_33112__boxed_1065_; lean_object* v_res_1066_; 
v___x_33112__boxed_1065_ = lean_unbox(v___x_1051_);
v_res_1066_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_33112__boxed_1065_, v_as_x27_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v_as_x27_1052_);
return v_res_1066_;
}
}
lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1069_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1260_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1260_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1260_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
uint8_t v_lookahead_1083_; 
v_lookahead_1083_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*14 + 14);
lean_dec(v_a_1079_);
if (v_lookahead_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(v_lookahead_1083_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v_toGoalState_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1258_; 
v___x_1088_ = lean_st_ref_get(v_a_1067_);
v_toGoalState_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1088_, 1);
lean_dec(v_unused_1259_);
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1258_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_toGoalState_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1258_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_split_1093_; lean_object* v_lookaheads_1094_; uint8_t v___x_1095_; 
v_split_1093_ = lean_ctor_get(v_toGoalState_1089_, 14);
lean_inc_ref(v_split_1093_);
lean_dec_ref(v_toGoalState_1089_);
v_lookaheads_1094_ = lean_ctor_get(v_split_1093_, 5);
lean_inc(v_lookaheads_1094_);
lean_dec_ref(v_split_1093_);
v___x_1095_ = l_List_isEmpty___redArg(v_lookaheads_1094_);
lean_dec(v_lookaheads_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_toGoalState_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1251_; 
lean_del_object(v___x_1081_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_st_ref_get(v_a_1067_);
v_toGoalState_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1097_, 1);
lean_dec(v_unused_1252_);
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1251_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_toGoalState_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1251_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_split_1102_; lean_object* v_lookaheads_1103_; lean_object* v___x_1104_; lean_object* v_toGoalState_1105_; lean_object* v_split_1106_; lean_object* v_mvarId_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1249_; 
v_split_1102_ = lean_ctor_get(v_toGoalState_1098_, 14);
lean_inc_ref(v_split_1102_);
lean_dec_ref(v_toGoalState_1098_);
v_lookaheads_1103_ = lean_ctor_get(v_split_1102_, 5);
lean_inc(v_lookaheads_1103_);
lean_dec_ref(v_split_1102_);
v___x_1104_ = lean_st_ref_take(v_a_1067_);
v_toGoalState_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_toGoalState_1105_);
v_split_1106_ = lean_ctor_get(v_toGoalState_1105_, 14);
lean_inc_ref(v_split_1106_);
v_mvarId_1107_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1104_, 0);
lean_dec(v_unused_1250_);
v___x_1109_ = v___x_1104_;
v_isShared_1110_ = v_isSharedCheck_1249_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_mvarId_1107_);
lean_dec(v___x_1104_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1249_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_nextDeclIdx_1111_; lean_object* v_enodeMap_1112_; lean_object* v_exprs_1113_; lean_object* v_parents_1114_; lean_object* v_congrTable_1115_; lean_object* v_appMap_1116_; lean_object* v_indicesFound_1117_; lean_object* v_toProcess_1118_; uint8_t v_inconsistent_1119_; lean_object* v_nextIdx_1120_; lean_object* v_newRawFacts_1121_; lean_object* v_facts_1122_; lean_object* v_extThms_1123_; lean_object* v_ematch_1124_; lean_object* v_inj_1125_; lean_object* v_clean_1126_; lean_object* v_sstates_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1247_; 
v_nextDeclIdx_1111_ = lean_ctor_get(v_toGoalState_1105_, 0);
v_enodeMap_1112_ = lean_ctor_get(v_toGoalState_1105_, 1);
v_exprs_1113_ = lean_ctor_get(v_toGoalState_1105_, 2);
v_parents_1114_ = lean_ctor_get(v_toGoalState_1105_, 3);
v_congrTable_1115_ = lean_ctor_get(v_toGoalState_1105_, 4);
v_appMap_1116_ = lean_ctor_get(v_toGoalState_1105_, 5);
v_indicesFound_1117_ = lean_ctor_get(v_toGoalState_1105_, 6);
v_toProcess_1118_ = lean_ctor_get(v_toGoalState_1105_, 7);
v_inconsistent_1119_ = lean_ctor_get_uint8(v_toGoalState_1105_, sizeof(void*)*17);
v_nextIdx_1120_ = lean_ctor_get(v_toGoalState_1105_, 8);
v_newRawFacts_1121_ = lean_ctor_get(v_toGoalState_1105_, 9);
v_facts_1122_ = lean_ctor_get(v_toGoalState_1105_, 10);
v_extThms_1123_ = lean_ctor_get(v_toGoalState_1105_, 11);
v_ematch_1124_ = lean_ctor_get(v_toGoalState_1105_, 12);
v_inj_1125_ = lean_ctor_get(v_toGoalState_1105_, 13);
v_clean_1126_ = lean_ctor_get(v_toGoalState_1105_, 15);
v_sstates_1127_ = lean_ctor_get(v_toGoalState_1105_, 16);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_toGoalState_1105_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_toGoalState_1105_, 14);
lean_dec(v_unused_1248_);
v___x_1129_ = v_toGoalState_1105_;
v_isShared_1130_ = v_isSharedCheck_1247_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_sstates_1127_);
lean_inc(v_clean_1126_);
lean_inc(v_inj_1125_);
lean_inc(v_ematch_1124_);
lean_inc(v_extThms_1123_);
lean_inc(v_facts_1122_);
lean_inc(v_newRawFacts_1121_);
lean_inc(v_nextIdx_1120_);
lean_inc(v_toProcess_1118_);
lean_inc(v_indicesFound_1117_);
lean_inc(v_appMap_1116_);
lean_inc(v_congrTable_1115_);
lean_inc(v_parents_1114_);
lean_inc(v_exprs_1113_);
lean_inc(v_enodeMap_1112_);
lean_inc(v_nextDeclIdx_1111_);
lean_dec(v_toGoalState_1105_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1247_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_num_1131_; lean_object* v_candidates_1132_; lean_object* v_added_1133_; lean_object* v_resolved_1134_; lean_object* v_trace_1135_; lean_object* v_argPosMap_1136_; lean_object* v_argsAt_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1245_; 
v_num_1131_ = lean_ctor_get(v_split_1106_, 0);
v_candidates_1132_ = lean_ctor_get(v_split_1106_, 1);
v_added_1133_ = lean_ctor_get(v_split_1106_, 2);
v_resolved_1134_ = lean_ctor_get(v_split_1106_, 3);
v_trace_1135_ = lean_ctor_get(v_split_1106_, 4);
v_argPosMap_1136_ = lean_ctor_get(v_split_1106_, 6);
v_argsAt_1137_ = lean_ctor_get(v_split_1106_, 7);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_split_1106_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_split_1106_, 5);
lean_dec(v_unused_1246_);
v___x_1139_ = v_split_1106_;
v_isShared_1140_ = v_isSharedCheck_1245_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_argsAt_1137_);
lean_inc(v_argPosMap_1136_);
lean_inc(v_trace_1135_);
lean_inc(v_resolved_1134_);
lean_inc(v_added_1133_);
lean_inc(v_candidates_1132_);
lean_inc(v_num_1131_);
lean_dec(v_split_1106_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1245_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 5, v___x_1096_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_num_1131_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_candidates_1132_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_added_1133_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_resolved_1134_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_trace_1135_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_argPosMap_1136_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_argsAt_1137_);
v___x_1142_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 14, v___x_1142_);
v___x_1144_ = v___x_1129_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_nextDeclIdx_1111_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_enodeMap_1112_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_exprs_1113_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_parents_1114_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_congrTable_1115_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v_appMap_1116_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v_indicesFound_1117_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_toProcess_1118_);
lean_ctor_set(v_reuseFailAlloc_1243_, 8, v_nextIdx_1120_);
lean_ctor_set(v_reuseFailAlloc_1243_, 9, v_newRawFacts_1121_);
lean_ctor_set(v_reuseFailAlloc_1243_, 10, v_facts_1122_);
lean_ctor_set(v_reuseFailAlloc_1243_, 11, v_extThms_1123_);
lean_ctor_set(v_reuseFailAlloc_1243_, 12, v_ematch_1124_);
lean_ctor_set(v_reuseFailAlloc_1243_, 13, v_inj_1125_);
lean_ctor_set(v_reuseFailAlloc_1243_, 14, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1243_, 15, v_clean_1126_);
lean_ctor_set(v_reuseFailAlloc_1243_, 16, v_sstates_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*17, v_inconsistent_1119_);
v___x_1144_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1144_);
v___x_1146_ = v___x_1109_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_mvarId_1107_);
v___x_1146_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1147_ = lean_st_ref_put(v_a_1067_, v___x_1146_);
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_box(v___x_1095_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1149_);
lean_ctor_set(v___x_1100_, 0, v___x_1096_);
v___x_1151_ = v___x_1100_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1151_);
lean_ctor_set(v___x_1091_, 0, v___x_1148_);
v___x_1153_ = v___x_1091_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1083_, v_lookaheads_1103_, v___x_1153_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_lookaheads_1103_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1231_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1231_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1231_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_fst_1159_; 
v_fst_1159_ = lean_ctor_get(v_a_1155_, 0);
if (lean_obj_tag(v_fst_1159_) == 0)
{
lean_object* v_snd_1160_; lean_object* v_snd_1161_; uint8_t v___x_1162_; 
v_snd_1160_ = lean_ctor_get(v_a_1155_, 1);
lean_inc(v_snd_1160_);
lean_dec(v_a_1155_);
v_snd_1161_ = lean_ctor_get(v_snd_1160_, 1);
v___x_1162_ = lean_unbox(v_snd_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_snd_1160_);
v___x_1163_ = lean_box(v___x_1095_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1163_);
v___x_1165_ = v___x_1157_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
else
{
lean_object* v_fst_1167_; lean_object* v___x_1168_; lean_object* v_toGoalState_1169_; lean_object* v_split_1170_; lean_object* v_mvarId_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1225_; 
v_fst_1167_ = lean_ctor_get(v_snd_1160_, 0);
lean_inc(v_fst_1167_);
lean_dec(v_snd_1160_);
v___x_1168_ = lean_st_ref_take(v_a_1067_);
v_toGoalState_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_toGoalState_1169_);
v_split_1170_ = lean_ctor_get(v_toGoalState_1169_, 14);
lean_inc_ref(v_split_1170_);
v_mvarId_1171_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1168_, 0);
lean_dec(v_unused_1226_);
v___x_1173_ = v___x_1168_;
v_isShared_1174_ = v_isSharedCheck_1225_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_mvarId_1171_);
lean_dec(v___x_1168_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1225_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_nextDeclIdx_1175_; lean_object* v_enodeMap_1176_; lean_object* v_exprs_1177_; lean_object* v_parents_1178_; lean_object* v_congrTable_1179_; lean_object* v_appMap_1180_; lean_object* v_indicesFound_1181_; lean_object* v_toProcess_1182_; uint8_t v_inconsistent_1183_; lean_object* v_nextIdx_1184_; lean_object* v_newRawFacts_1185_; lean_object* v_facts_1186_; lean_object* v_extThms_1187_; lean_object* v_ematch_1188_; lean_object* v_inj_1189_; lean_object* v_clean_1190_; lean_object* v_sstates_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1223_; 
v_nextDeclIdx_1175_ = lean_ctor_get(v_toGoalState_1169_, 0);
v_enodeMap_1176_ = lean_ctor_get(v_toGoalState_1169_, 1);
v_exprs_1177_ = lean_ctor_get(v_toGoalState_1169_, 2);
v_parents_1178_ = lean_ctor_get(v_toGoalState_1169_, 3);
v_congrTable_1179_ = lean_ctor_get(v_toGoalState_1169_, 4);
v_appMap_1180_ = lean_ctor_get(v_toGoalState_1169_, 5);
v_indicesFound_1181_ = lean_ctor_get(v_toGoalState_1169_, 6);
v_toProcess_1182_ = lean_ctor_get(v_toGoalState_1169_, 7);
v_inconsistent_1183_ = lean_ctor_get_uint8(v_toGoalState_1169_, sizeof(void*)*17);
v_nextIdx_1184_ = lean_ctor_get(v_toGoalState_1169_, 8);
v_newRawFacts_1185_ = lean_ctor_get(v_toGoalState_1169_, 9);
v_facts_1186_ = lean_ctor_get(v_toGoalState_1169_, 10);
v_extThms_1187_ = lean_ctor_get(v_toGoalState_1169_, 11);
v_ematch_1188_ = lean_ctor_get(v_toGoalState_1169_, 12);
v_inj_1189_ = lean_ctor_get(v_toGoalState_1169_, 13);
v_clean_1190_ = lean_ctor_get(v_toGoalState_1169_, 15);
v_sstates_1191_ = lean_ctor_get(v_toGoalState_1169_, 16);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_toGoalState_1169_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_toGoalState_1169_, 14);
lean_dec(v_unused_1224_);
v___x_1193_ = v_toGoalState_1169_;
v_isShared_1194_ = v_isSharedCheck_1223_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_sstates_1191_);
lean_inc(v_clean_1190_);
lean_inc(v_inj_1189_);
lean_inc(v_ematch_1188_);
lean_inc(v_extThms_1187_);
lean_inc(v_facts_1186_);
lean_inc(v_newRawFacts_1185_);
lean_inc(v_nextIdx_1184_);
lean_inc(v_toProcess_1182_);
lean_inc(v_indicesFound_1181_);
lean_inc(v_appMap_1180_);
lean_inc(v_congrTable_1179_);
lean_inc(v_parents_1178_);
lean_inc(v_exprs_1177_);
lean_inc(v_enodeMap_1176_);
lean_inc(v_nextDeclIdx_1175_);
lean_dec(v_toGoalState_1169_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1223_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_num_1195_; lean_object* v_candidates_1196_; lean_object* v_added_1197_; lean_object* v_resolved_1198_; lean_object* v_trace_1199_; lean_object* v_lookaheads_1200_; lean_object* v_argPosMap_1201_; lean_object* v_argsAt_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1222_; 
v_num_1195_ = lean_ctor_get(v_split_1170_, 0);
v_candidates_1196_ = lean_ctor_get(v_split_1170_, 1);
v_added_1197_ = lean_ctor_get(v_split_1170_, 2);
v_resolved_1198_ = lean_ctor_get(v_split_1170_, 3);
v_trace_1199_ = lean_ctor_get(v_split_1170_, 4);
v_lookaheads_1200_ = lean_ctor_get(v_split_1170_, 5);
v_argPosMap_1201_ = lean_ctor_get(v_split_1170_, 6);
v_argsAt_1202_ = lean_ctor_get(v_split_1170_, 7);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_split_1170_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1204_ = v_split_1170_;
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_argsAt_1202_);
lean_inc(v_argPosMap_1201_);
lean_inc(v_lookaheads_1200_);
lean_inc(v_trace_1199_);
lean_inc(v_resolved_1198_);
lean_inc(v_added_1197_);
lean_inc(v_candidates_1196_);
lean_inc(v_num_1195_);
lean_dec(v_split_1170_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = l_List_reverse___redArg(v_fst_1167_);
v___x_1207_ = l_List_appendTR___redArg(v_lookaheads_1200_, v___x_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 5, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_num_1195_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_candidates_1196_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_added_1197_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_resolved_1198_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_trace_1199_);
lean_ctor_set(v_reuseFailAlloc_1221_, 5, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 6, v_argPosMap_1201_);
lean_ctor_set(v_reuseFailAlloc_1221_, 7, v_argsAt_1202_);
v___x_1209_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 14, v___x_1209_);
v___x_1211_ = v___x_1193_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_nextDeclIdx_1175_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_enodeMap_1176_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_exprs_1177_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_parents_1178_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_congrTable_1179_);
lean_ctor_set(v_reuseFailAlloc_1220_, 5, v_appMap_1180_);
lean_ctor_set(v_reuseFailAlloc_1220_, 6, v_indicesFound_1181_);
lean_ctor_set(v_reuseFailAlloc_1220_, 7, v_toProcess_1182_);
lean_ctor_set(v_reuseFailAlloc_1220_, 8, v_nextIdx_1184_);
lean_ctor_set(v_reuseFailAlloc_1220_, 9, v_newRawFacts_1185_);
lean_ctor_set(v_reuseFailAlloc_1220_, 10, v_facts_1186_);
lean_ctor_set(v_reuseFailAlloc_1220_, 11, v_extThms_1187_);
lean_ctor_set(v_reuseFailAlloc_1220_, 12, v_ematch_1188_);
lean_ctor_set(v_reuseFailAlloc_1220_, 13, v_inj_1189_);
lean_ctor_set(v_reuseFailAlloc_1220_, 14, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1220_, 15, v_clean_1190_);
lean_ctor_set(v_reuseFailAlloc_1220_, 16, v_sstates_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*17, v_inconsistent_1183_);
v___x_1211_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1211_);
v___x_1213_ = v___x_1173_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_mvarId_1171_);
v___x_1213_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = lean_st_ref_put(v_a_1067_, v___x_1213_);
v___x_1215_ = lean_box(v_lookahead_1083_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1215_);
v___x_1217_ = v___x_1157_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
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
lean_object* v_val_1227_; lean_object* v___x_1229_; 
lean_inc_ref(v_fst_1159_);
lean_dec(v_a_1155_);
v_val_1227_ = lean_ctor_get(v_fst_1159_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_fst_1159_, 1);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_val_1227_);
v___x_1229_ = v___x_1157_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_val_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1154_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1154_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
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
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_del_object(v___x_1091_);
v___x_1253_ = 0;
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1254_);
v___x_1256_ = v___x_1081_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1078_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1078_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_lookahead_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1067_ = stack[0].m_obj;
lean_object* v_a_1068_ = stack[1].m_obj;
lean_object* v_a_1069_ = stack[2].m_obj;
lean_object* v_a_1070_ = stack[3].m_obj;
lean_object* v_a_1071_ = stack[4].m_obj;
lean_object* v_a_1072_ = stack[5].m_obj;
lean_object* v_a_1073_ = stack[6].m_obj;
lean_object* v_a_1074_ = stack[7].m_obj;
lean_object* v_a_1075_ = stack[8].m_obj;
lean_object* v_a_1076_ = stack[9].m_obj;
lean_object* v_res_1269_;
v_res_1269_ = l_Lean_Meta_Grind_lookahead(v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_Grind_lookahead(v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
return v_res_1281_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1282_, lean_object* v_as_1283_, lean_object* v_as_x27_1284_, lean_object* v_b_1285_, lean_object* v_a_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1282_, v_as_x27_1284_, v_b_1285_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1282_ = stack[0].m_num;
lean_object* v_as_1283_ = stack[1].m_obj;
lean_object* v_as_x27_1284_ = stack[2].m_obj;
lean_object* v_b_1285_ = stack[3].m_obj;
lean_object* v___y_1287_ = stack[5].m_obj;
lean_object* v___y_1288_ = stack[6].m_obj;
lean_object* v___y_1289_ = stack[7].m_obj;
lean_object* v___y_1290_ = stack[8].m_obj;
lean_object* v___y_1291_ = stack[9].m_obj;
lean_object* v___y_1292_ = stack[10].m_obj;
lean_object* v___y_1293_ = stack[11].m_obj;
lean_object* v___y_1294_ = stack[12].m_obj;
lean_object* v___y_1295_ = stack[13].m_obj;
lean_object* v___y_1296_ = stack[14].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_1282_, v_as_1283_, v_as_x27_1284_, v_b_1285_, lean_box(0), v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1300_, lean_object* v_as_1301_, lean_object* v_as_x27_1302_, lean_object* v_b_1303_, lean_object* v_a_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_33858__boxed_1316_; lean_object* v_res_1317_; 
v___x_33858__boxed_1316_ = lean_unbox(v___x_1300_);
v_res_1317_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_33858__boxed_1316_, v_as_1301_, v_as_x27_1302_, v_b_1303_, v_a_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec(v_as_x27_1302_);
lean_dec(v_as_1301_);
return v_res_1317_;
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
