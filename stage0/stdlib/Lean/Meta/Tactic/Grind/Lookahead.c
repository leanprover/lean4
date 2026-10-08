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
lean_object* v_a_441_; lean_object* v_nextDeclIdx_442_; lean_object* v_enodeMap_443_; lean_object* v_exprs_444_; lean_object* v_parents_445_; lean_object* v_congrTable_446_; lean_object* v_appMap_447_; lean_object* v_indicesFound_448_; uint8_t v_inconsistent_449_; lean_object* v_nextIdx_450_; lean_object* v_newRawFacts_451_; lean_object* v_facts_452_; lean_object* v_extThms_453_; lean_object* v_ematch_454_; lean_object* v_inj_455_; lean_object* v_split_456_; lean_object* v_clean_457_; lean_object* v_sstates_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_506_; 
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
v_inconsistent_449_ = lean_ctor_get_uint8(v_toGoalState_421_, sizeof(void*)*17);
v_nextIdx_450_ = lean_ctor_get(v_toGoalState_421_, 8);
v_newRawFacts_451_ = lean_ctor_get(v_toGoalState_421_, 9);
v_facts_452_ = lean_ctor_get(v_toGoalState_421_, 10);
v_extThms_453_ = lean_ctor_get(v_toGoalState_421_, 11);
v_ematch_454_ = lean_ctor_get(v_toGoalState_421_, 12);
v_inj_455_ = lean_ctor_get(v_toGoalState_421_, 13);
v_split_456_ = lean_ctor_get(v_toGoalState_421_, 14);
v_clean_457_ = lean_ctor_get(v_toGoalState_421_, 15);
v_sstates_458_ = lean_ctor_get(v_toGoalState_421_, 16);
v_isSharedCheck_506_ = !lean_is_exclusive(v_toGoalState_421_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_toGoalState_421_, 7);
lean_dec(v_unused_507_);
v___x_460_ = v_toGoalState_421_;
v_isShared_461_ = v_isSharedCheck_506_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_sstates_458_);
lean_inc(v_clean_457_);
lean_inc(v_split_456_);
lean_inc(v_inj_455_);
lean_inc(v_ematch_454_);
lean_inc(v_extThms_453_);
lean_inc(v_facts_452_);
lean_inc(v_newRawFacts_451_);
lean_inc(v_nextIdx_450_);
lean_inc(v_indicesFound_448_);
lean_inc(v_appMap_447_);
lean_inc(v_congrTable_446_);
lean_inc(v_parents_445_);
lean_inc(v_exprs_444_);
lean_inc(v_enodeMap_443_);
lean_inc(v_nextDeclIdx_442_);
lean_dec(v_toGoalState_421_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_506_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0));
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 7, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_nextDeclIdx_442_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_enodeMap_443_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_exprs_444_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_parents_445_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_congrTable_446_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_appMap_447_);
lean_ctor_set(v_reuseFailAlloc_505_, 6, v_indicesFound_448_);
lean_ctor_set(v_reuseFailAlloc_505_, 7, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_505_, 8, v_nextIdx_450_);
lean_ctor_set(v_reuseFailAlloc_505_, 9, v_newRawFacts_451_);
lean_ctor_set(v_reuseFailAlloc_505_, 10, v_facts_452_);
lean_ctor_set(v_reuseFailAlloc_505_, 11, v_extThms_453_);
lean_ctor_set(v_reuseFailAlloc_505_, 12, v_ematch_454_);
lean_ctor_set(v_reuseFailAlloc_505_, 13, v_inj_455_);
lean_ctor_set(v_reuseFailAlloc_505_, 14, v_split_456_);
lean_ctor_set(v_reuseFailAlloc_505_, 15, v_clean_457_);
lean_ctor_set(v_reuseFailAlloc_505_, 16, v_sstates_458_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*17, v_inconsistent_449_);
v___x_464_ = v_reuseFailAlloc_505_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = l_Lean_Expr_mvarId_x21(v_a_441_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_420_, v___y_422_);
lean_dec_ref(v_e_420_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_466_, v_a_468_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_488_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_488_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
if (lean_obj_tag(v_a_470_) == 0)
{
lean_object* v___x_474_; lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
lean_del_object(v___x_472_);
v___x_474_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_441_, v___y_429_);
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_a_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec_ref_known(v_a_470_, 1);
lean_dec(v_a_441_);
v___x_484_ = lean_box(0);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_484_);
v___x_486_ = v___x_472_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_a_441_);
v_a_489_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_469_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_469_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref_known(v___x_466_, 2);
lean_dec(v_a_441_);
v_a_497_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_467_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_467_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_508_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_440_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_440_);
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
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_516_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_438_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_438_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_524_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_435_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_435_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_532_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_433_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_433_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* v_mvarId_540_, lean_object* v_e_541_, lean_object* v_toGoalState_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_540_, v_e_541_, v_toGoalState_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec(v___y_543_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(lean_object* v_msgData_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_env_562_; uint8_t v___x_563_; lean_object* v_env_564_; lean_object* v___x_565_; lean_object* v_toCold_566_; lean_object* v_mctx_567_; lean_object* v_lctx_568_; lean_object* v_options_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = 0;
v_env_564_ = l_Lean_Environment_setRecordingDeps(v_env_562_, v___x_563_);
v___x_565_ = lean_st_ref_get(v___y_557_);
v_toCold_566_ = lean_ctor_get(v___y_558_, 0);
v_mctx_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_mctx_567_);
lean_dec(v___x_565_);
v_lctx_568_ = lean_ctor_get(v___y_556_, 2);
v_options_569_ = lean_ctor_get(v_toCold_566_, 2);
lean_inc_ref(v_options_569_);
lean_inc_ref(v_lctx_568_);
v___x_570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_570_, 0, v_env_564_);
lean_ctor_set(v___x_570_, 1, v_mctx_567_);
lean_ctor_set(v___x_570_, 2, v_lctx_568_);
lean_ctor_set(v___x_570_, 3, v_options_569_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_msgData_555_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_580_; double v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_float_of_nat(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_585_, lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ref_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_639_; 
v_ref_592_ = lean_ctor_get(v___y_589_, 2);
v___x_593_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_639_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_639_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_639_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v_traceState_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_cache_604_; lean_object* v_recordedDeps_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_638_; 
v___x_598_ = lean_st_ref_take(v___y_590_);
v_traceState_599_ = lean_ctor_get(v___x_598_, 4);
v_env_600_ = lean_ctor_get(v___x_598_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_598_, 1);
v_ngen_602_ = lean_ctor_get(v___x_598_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_598_, 3);
v_cache_604_ = lean_ctor_get(v___x_598_, 5);
v_recordedDeps_605_ = lean_ctor_get(v___x_598_, 6);
v_messages_606_ = lean_ctor_get(v___x_598_, 7);
v_infoState_607_ = lean_ctor_get(v___x_598_, 8);
v_snapshotTasks_608_ = lean_ctor_get(v___x_598_, 9);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_638_ == 0)
{
v___x_610_ = v___x_598_;
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_recordedDeps_605_);
lean_inc(v_cache_604_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_637_; 
v_tid_612_ = lean_ctor_get_uint64(v_traceState_599_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_traceState_599_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_traceState_599_);
if (v_isSharedCheck_637_ == 0)
{
v___x_615_ = v_traceState_599_;
v_isShared_616_ = v_isSharedCheck_637_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_traceState_599_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_637_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; double v___x_619_; uint8_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_box(0);
v___x_619_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
v___x_620_ = 0;
v___x_621_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_622_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_622_, 0, v_cls_585_);
lean_ctor_set(v___x_622_, 1, v___x_618_);
lean_ctor_set(v___x_622_, 2, v___x_621_);
lean_ctor_set_float(v___x_622_, sizeof(void*)*3, v___x_619_);
lean_ctor_set_float(v___x_622_, sizeof(void*)*3 + 8, v___x_619_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*3 + 16, v___x_620_);
v___x_623_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2));
v___x_624_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v_a_594_);
lean_ctor_set(v___x_624_, 2, v___x_623_);
lean_inc(v_ref_592_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_ref_592_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_PersistentArray_push___redArg(v_traces_613_, v___x_625_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_626_);
v___x_628_ = v___x_615_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_626_);
lean_ctor_set_uint64(v_reuseFailAlloc_636_, sizeof(void*)*1, v_tid_612_);
v___x_628_ = v_reuseFailAlloc_636_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v___x_628_);
v___x_630_ = v___x_610_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_env_600_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 5, v_cache_604_);
lean_ctor_set(v_reuseFailAlloc_635_, 6, v_recordedDeps_605_);
lean_ctor_set(v_reuseFailAlloc_635_, 7, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_635_, 8, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_635_, 9, v_snapshotTasks_608_);
v___x_630_ = v_reuseFailAlloc_635_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_st_ref_put(v___y_590_, v___x_630_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_617_);
v___x_633_ = v___x_596_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_617_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_640_, v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_657_ = l_Lean_mkConst(v___x_656_, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_670_ = l_Lean_Name_append(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14(void){
_start:
{
lean_object* v_cls_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_cls_676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_678_ = l_Lean_Name_append(v___x_677_, v_cls_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v_config_733_; lean_object* v_toCold_734_; lean_object* v_options_735_; lean_object* v_simp_736_; lean_object* v_simpMethods_737_; lean_object* v_symSimpMethods_738_; lean_object* v_symDSimpMethods_739_; lean_object* v_anchorRefs_x3f_740_; uint8_t v_reportMVarIssue_741_; lean_object* v_splitSource_742_; lean_object* v_ematchDiagSource_743_; lean_object* v_symPrios_744_; lean_object* v_extensions_745_; uint8_t v_debug_746_; uint8_t v_ematchDiag_747_; uint8_t v_trace_748_; uint8_t v_markInstances_749_; uint8_t v_lax_750_; uint8_t v_suggestions_751_; uint8_t v_locals_752_; lean_object* v_splits_753_; lean_object* v_ematch_754_; lean_object* v_gen_755_; lean_object* v_genLocal_756_; lean_object* v_instances_757_; uint8_t v_matchEqs_758_; uint8_t v_splitMatch_759_; uint8_t v_splitIte_760_; uint8_t v_splitIndPred_761_; uint8_t v_splitImp_762_; lean_object* v_canonHeartbeats_763_; uint8_t v_ext_764_; uint8_t v_extAll_765_; uint8_t v_etaStruct_766_; uint8_t v_funext_767_; uint8_t v_lookahead_768_; uint8_t v_verbose_769_; uint8_t v_clean_770_; uint8_t v_mbtc_771_; uint8_t v_zetaDelta_772_; uint8_t v_zeta_773_; uint8_t v_ring_774_; lean_object* v_ringSteps_775_; lean_object* v_ringMaxDegree_776_; uint8_t v_linarith_777_; uint8_t v_lia_778_; lean_object* v_liaSteps_779_; uint8_t v_hom_780_; uint8_t v_ac_781_; lean_object* v_acSteps_782_; lean_object* v_exp_783_; uint8_t v_abstractProof_784_; uint8_t v_inj_785_; uint8_t v_order_786_; lean_object* v_min_787_; lean_object* v_detailed_788_; uint8_t v_useSorry_789_; uint8_t v_revert_790_; uint8_t v_funCC_791_; uint8_t v_reducible_792_; lean_object* v_maxSuggestions_793_; lean_object* v_inheritedTraceOptions_794_; uint8_t v_hasTrace_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___x_851_; 
v_config_733_ = lean_ctor_get(v_a_682_, 4);
v_toCold_734_ = lean_ctor_get(v_a_688_, 0);
v_options_735_ = lean_ctor_get(v_toCold_734_, 2);
v_simp_736_ = lean_ctor_get(v_a_682_, 0);
v_simpMethods_737_ = lean_ctor_get(v_a_682_, 1);
v_symSimpMethods_738_ = lean_ctor_get(v_a_682_, 2);
v_symDSimpMethods_739_ = lean_ctor_get(v_a_682_, 3);
v_anchorRefs_x3f_740_ = lean_ctor_get(v_a_682_, 5);
v_reportMVarIssue_741_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*10 + 1);
v_splitSource_742_ = lean_ctor_get(v_a_682_, 6);
v_ematchDiagSource_743_ = lean_ctor_get(v_a_682_, 7);
v_symPrios_744_ = lean_ctor_get(v_a_682_, 8);
v_extensions_745_ = lean_ctor_get(v_a_682_, 9);
v_debug_746_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*10 + 2);
v_ematchDiag_747_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*10 + 3);
v_trace_748_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14);
v_markInstances_749_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 1);
v_lax_750_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 2);
v_suggestions_751_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 3);
v_locals_752_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 4);
v_splits_753_ = lean_ctor_get(v_config_733_, 0);
v_ematch_754_ = lean_ctor_get(v_config_733_, 1);
v_gen_755_ = lean_ctor_get(v_config_733_, 2);
v_genLocal_756_ = lean_ctor_get(v_config_733_, 3);
v_instances_757_ = lean_ctor_get(v_config_733_, 4);
v_matchEqs_758_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 5);
v_splitMatch_759_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 6);
v_splitIte_760_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 7);
v_splitIndPred_761_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 8);
v_splitImp_762_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 9);
v_canonHeartbeats_763_ = lean_ctor_get(v_config_733_, 5);
v_ext_764_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 10);
v_extAll_765_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 11);
v_etaStruct_766_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 12);
v_funext_767_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 13);
v_lookahead_768_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 14);
v_verbose_769_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 15);
v_clean_770_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 16);
v_mbtc_771_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 18);
v_zetaDelta_772_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 19);
v_zeta_773_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 20);
v_ring_774_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 21);
v_ringSteps_775_ = lean_ctor_get(v_config_733_, 6);
v_ringMaxDegree_776_ = lean_ctor_get(v_config_733_, 7);
v_linarith_777_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 22);
v_lia_778_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 23);
v_liaSteps_779_ = lean_ctor_get(v_config_733_, 8);
v_hom_780_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 24);
v_ac_781_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 25);
v_acSteps_782_ = lean_ctor_get(v_config_733_, 9);
v_exp_783_ = lean_ctor_get(v_config_733_, 10);
v_abstractProof_784_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 26);
v_inj_785_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 27);
v_order_786_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 28);
v_min_787_ = lean_ctor_get(v_config_733_, 11);
v_detailed_788_ = lean_ctor_get(v_config_733_, 12);
v_useSorry_789_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 29);
v_revert_790_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 30);
v_funCC_791_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 31);
v_reducible_792_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*14 + 32);
v_maxSuggestions_793_ = lean_ctor_get(v_config_733_, 13);
v_inheritedTraceOptions_794_ = lean_ctor_get(v_toCold_734_, 11);
v_hasTrace_795_ = lean_ctor_get_uint8(v_options_735_, sizeof(void*)*1);
v___x_796_ = 1;
lean_inc(v_maxSuggestions_793_);
lean_inc(v_detailed_788_);
lean_inc(v_min_787_);
lean_inc(v_exp_783_);
lean_inc(v_acSteps_782_);
lean_inc(v_liaSteps_779_);
lean_inc(v_ringMaxDegree_776_);
lean_inc(v_ringSteps_775_);
lean_inc(v_canonHeartbeats_763_);
lean_inc(v_instances_757_);
lean_inc(v_genLocal_756_);
lean_inc(v_gen_755_);
lean_inc(v_ematch_754_);
lean_inc(v_splits_753_);
v___x_797_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_797_, 0, v_splits_753_);
lean_ctor_set(v___x_797_, 1, v_ematch_754_);
lean_ctor_set(v___x_797_, 2, v_gen_755_);
lean_ctor_set(v___x_797_, 3, v_genLocal_756_);
lean_ctor_set(v___x_797_, 4, v_instances_757_);
lean_ctor_set(v___x_797_, 5, v_canonHeartbeats_763_);
lean_ctor_set(v___x_797_, 6, v_ringSteps_775_);
lean_ctor_set(v___x_797_, 7, v_ringMaxDegree_776_);
lean_ctor_set(v___x_797_, 8, v_liaSteps_779_);
lean_ctor_set(v___x_797_, 9, v_acSteps_782_);
lean_ctor_set(v___x_797_, 10, v_exp_783_);
lean_ctor_set(v___x_797_, 11, v_min_787_);
lean_ctor_set(v___x_797_, 12, v_detailed_788_);
lean_ctor_set(v___x_797_, 13, v_maxSuggestions_793_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14, v_trace_748_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 1, v_markInstances_749_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 2, v_lax_750_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 3, v_suggestions_751_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 4, v_locals_752_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 5, v_matchEqs_758_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 6, v_splitMatch_759_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 7, v_splitIte_760_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 8, v_splitIndPred_761_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 9, v_splitImp_762_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 10, v_ext_764_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 11, v_extAll_765_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 12, v_etaStruct_766_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 13, v_funext_767_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 14, v_lookahead_768_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 15, v_verbose_769_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 16, v_clean_770_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 17, v___x_796_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 18, v_mbtc_771_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 19, v_zetaDelta_772_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 20, v_zeta_773_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 21, v_ring_774_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 22, v_linarith_777_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 23, v_lia_778_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 24, v_hom_780_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 25, v_ac_781_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 26, v_abstractProof_784_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 27, v_inj_785_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 28, v_order_786_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 29, v_useSorry_789_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 30, v_revert_790_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 31, v_funCC_791_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*14 + 32, v_reducible_792_);
lean_inc_ref(v_extensions_745_);
lean_inc_ref(v_symPrios_744_);
lean_inc(v_ematchDiagSource_743_);
lean_inc(v_splitSource_742_);
lean_inc(v_anchorRefs_x3f_740_);
lean_inc_ref(v_symDSimpMethods_739_);
lean_inc_ref(v_symSimpMethods_738_);
lean_inc_ref(v_simpMethods_737_);
lean_inc_ref(v_simp_736_);
v___x_851_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_851_, 0, v_simp_736_);
lean_ctor_set(v___x_851_, 1, v_simpMethods_737_);
lean_ctor_set(v___x_851_, 2, v_symSimpMethods_738_);
lean_ctor_set(v___x_851_, 3, v_symDSimpMethods_739_);
lean_ctor_set(v___x_851_, 4, v___x_797_);
lean_ctor_set(v___x_851_, 5, v_anchorRefs_x3f_740_);
lean_ctor_set(v___x_851_, 6, v_splitSource_742_);
lean_ctor_set(v___x_851_, 7, v_ematchDiagSource_743_);
lean_ctor_set(v___x_851_, 8, v_symPrios_744_);
lean_ctor_set(v___x_851_, 9, v_extensions_745_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*10, v___x_796_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*10 + 1, v_reportMVarIssue_741_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*10 + 2, v_debug_746_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*10 + 3, v_ematchDiag_747_);
if (v_hasTrace_795_ == 0)
{
v___y_799_ = v_a_680_;
v___y_800_ = v_a_681_;
v___y_801_ = v___x_851_;
v___y_802_ = v_a_683_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
goto v___jp_798_;
}
else
{
lean_object* v_cls_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_cls_852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
v___x_854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_794_, v_options_735_, v___x_853_);
if (v___x_854_ == 0)
{
v___y_799_ = v_a_680_;
v___y_800_ = v_a_681_;
v___y_801_ = v___x_851_;
v___y_802_ = v_a_683_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
goto v___jp_798_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Grind_updateLastTag(v_a_680_, v_a_681_, v___x_851_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref_known(v___x_855_, 1);
lean_inc_ref(v_e_679_);
v___x_856_ = l_Lean_MessageData_ofExpr(v_e_679_);
v___x_857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_852_, v___x_856_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_dec_ref_known(v___x_857_, 1);
v___y_799_ = v_a_680_;
v___y_800_ = v_a_681_;
v___y_801_ = v___x_851_;
v___y_802_ = v_a_683_;
v___y_803_ = v_a_684_;
v___y_804_ = v_a_685_;
v___y_805_ = v_a_686_;
v___y_806_ = v_a_687_;
v___y_807_ = v_a_688_;
v___y_808_ = v_a_689_;
goto v___jp_798_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref_known(v___x_851_, 10);
lean_dec_ref(v_e_679_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref_known(v___x_851_, 10);
lean_dec_ref(v_e_679_);
v_a_866_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_855_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
v___jp_691_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_679_);
v___x_704_ = l_Lean_mkAppB(v___x_703_, v_e_679_, v___y_692_);
v___x_705_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_679_, v___x_704_, v___y_693_, v___y_695_, v___y_697_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; 
lean_dec_ref_known(v___x_705_, 1);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc(v___y_694_);
lean_inc(v___y_693_);
v___x_706_ = lean_grind_process_to_do(v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_715_; 
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_706_, 0);
lean_dec(v_unused_716_);
v___x_708_ = v___x_706_;
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
else
{
lean_dec(v___x_706_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = 1;
v___x_711_ = lean_box(v___x_710_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_706_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_706_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v___y_695_);
v_a_725_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_705_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_705_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
v___jp_798_:
{
lean_object* v___x_809_; lean_object* v_toGoalState_810_; lean_object* v_mvarId_811_; lean_object* v___f_812_; lean_object* v___x_813_; 
v___x_809_ = lean_st_ref_get(v___y_799_);
v_toGoalState_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_toGoalState_810_);
v_mvarId_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_mvarId_811_);
lean_dec(v___x_809_);
lean_inc_ref(v_e_679_);
v___f_812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_812_, 0, v_mvarId_811_);
lean_closure_set(v___f_812_, 1, v_e_679_);
lean_closure_set(v___f_812_, 2, v_toGoalState_810_);
v___x_813_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_812_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_842_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_842_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_842_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_842_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
if (lean_obj_tag(v_a_814_) == 1)
{
lean_object* v_toCold_818_; lean_object* v_options_819_; uint8_t v_hasTrace_820_; 
lean_del_object(v___x_816_);
v_toCold_818_ = lean_ctor_get(v___y_807_, 0);
v_options_819_ = lean_ctor_get(v_toCold_818_, 2);
v_hasTrace_820_ = lean_ctor_get_uint8(v_options_819_, sizeof(void*)*1);
if (v_hasTrace_820_ == 0)
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_a_814_, 1);
v___y_692_ = v_val_821_;
v___y_693_ = v___y_799_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
goto v___jp_691_;
}
else
{
lean_object* v_val_822_; lean_object* v_inheritedTraceOptions_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_val_822_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_a_814_, 1);
v_inheritedTraceOptions_823_ = lean_ctor_get(v_toCold_818_, 11);
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
v___x_826_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_823_, v_options_819_, v___x_825_);
if (v___x_826_ == 0)
{
v___y_692_ = v_val_822_;
v___y_693_ = v___y_799_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
goto v___jp_691_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc_ref(v_e_679_);
v___x_827_ = l_Lean_MessageData_ofExpr(v_e_679_);
v___x_828_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_824_, v___x_827_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_dec_ref_known(v___x_828_, 1);
v___y_692_ = v_val_822_;
v___y_693_ = v___y_799_;
v___y_694_ = v___y_800_;
v___y_695_ = v___y_801_;
v___y_696_ = v___y_802_;
v___y_697_ = v___y_803_;
v___y_698_ = v___y_804_;
v___y_699_ = v___y_805_;
v___y_700_ = v___y_806_;
v___y_701_ = v___y_807_;
v___y_702_ = v___y_808_;
goto v___jp_691_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_val_822_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_e_679_);
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
else
{
uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v_a_814_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_e_679_);
v___x_837_ = 0;
v___x_838_ = lean_box(v___x_837_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_838_);
v___x_840_ = v___x_816_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v___y_801_);
lean_dec_ref(v_e_679_);
v_a_843_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_813_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_813_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_a_875_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_887_, lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_887_, v_msg_888_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_901_, lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_901_, v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec(v___y_903_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_915_, lean_object* v_as_x27_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
if (lean_obj_tag(v_as_x27_916_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_b_917_);
return v___x_929_;
}
else
{
lean_object* v_snd_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_1032_; 
v_snd_930_ = lean_ctor_get(v_b_917_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_b_917_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_b_917_, 0);
lean_dec(v_unused_1033_);
v___x_932_ = v_b_917_;
v_isShared_933_ = v_isSharedCheck_1032_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snd_930_);
lean_dec(v_b_917_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_1032_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_head_934_; lean_object* v_tail_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1031_; 
v_head_934_ = lean_ctor_get(v_as_x27_916_, 0);
v_tail_935_ = lean_ctor_get(v_as_x27_916_, 1);
v_fst_936_ = lean_ctor_get(v_snd_930_, 0);
v_snd_937_ = lean_ctor_get(v_snd_930_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_snd_930_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_939_ = v_snd_930_;
v_isShared_940_ = v_isSharedCheck_1031_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v_snd_930_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1031_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_918_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1022_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_1022_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1022_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; 
v___x_947_ = lean_unbox(v_a_943_);
lean_dec(v_a_943_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_del_object(v___x_945_);
lean_inc(v_head_934_);
v___x_948_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_934_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
switch(lean_obj_tag(v_a_949_))
{
case 0:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec(v_snd_937_);
v___x_950_ = lean_box(v___x_915_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_950_);
v___x_952_ = v___x_939_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_957_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_952_);
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_954_ = v___x_932_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_as_x27_916_ = v_tail_935_;
v_b_917_ = v___x_954_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_inc(v_head_934_);
v___x_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_958_, 0, v_head_934_);
lean_ctor_set(v___x_958_, 1, v_fst_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_958_);
v___x_960_ = v___x_939_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_snd_937_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_960_);
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_962_ = v___x_932_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_as_x27_916_ = v_tail_935_;
v_b_917_ = v___x_962_;
goto _start;
}
}
}
default: 
{
uint8_t v_tryPostpone_966_; 
v_tryPostpone_966_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_949_, 1);
if (v_tryPostpone_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_934_);
v___x_968_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_967_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; uint8_t v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_unbox(v_a_969_);
lean_dec(v_a_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_inc(v_head_934_);
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v_head_934_);
lean_ctor_set(v___x_971_, 1, v_fst_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_971_);
v___x_973_ = v___x_939_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_snd_937_);
v___x_973_ = v_reuseFailAlloc_978_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_973_);
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_975_ = v___x_932_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v_as_x27_916_ = v_tail_935_;
v_b_917_ = v___x_975_;
goto _start;
}
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_snd_937_);
v___x_979_ = lean_box(v___x_915_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_979_);
v___x_981_ = v___x_939_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_986_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_981_);
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_983_ = v___x_932_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_as_x27_916_ = v_tail_935_;
v_b_917_ = v___x_983_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_del_object(v___x_939_);
lean_dec(v_snd_937_);
lean_dec(v_fst_936_);
lean_del_object(v___x_932_);
v_a_987_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_968_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_968_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_head_934_);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v_head_934_);
lean_ctor_set(v___x_995_, 1, v_fst_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_995_);
v___x_997_ = v___x_939_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_snd_937_);
v___x_997_ = v_reuseFailAlloc_1002_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_997_);
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_999_ = v___x_932_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
v_as_x27_916_ = v_tail_935_;
v_b_917_ = v___x_999_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_939_);
lean_dec(v_snd_937_);
lean_dec(v_fst_936_);
lean_del_object(v___x_932_);
v_a_1003_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_948_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_948_);
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
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1011_ = lean_box(v___x_915_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
if (v_isShared_940_ == 0)
{
v___x_1014_ = v___x_939_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_snd_937_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_1014_);
lean_ctor_set(v___x_932_, 0, v___x_1012_);
v___x_1016_ = v___x_932_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_1016_);
v___x_1018_ = v___x_945_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_del_object(v___x_939_);
lean_dec(v_snd_937_);
lean_dec(v_fst_936_);
lean_del_object(v___x_932_);
v_a_1023_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_942_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_942_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1034_, lean_object* v_as_x27_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_33112__boxed_1048_; lean_object* v_res_1049_; 
v___x_33112__boxed_1048_ = lean_unbox(v___x_1034_);
v_res_1049_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_33112__boxed_1048_, v_as_x27_1035_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec(v_as_x27_1035_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1052_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1243_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1243_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1243_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v_lookahead_1066_; 
v_lookahead_1066_ = lean_ctor_get_uint8(v_a_1062_, sizeof(void*)*14 + 14);
lean_dec(v_a_1062_);
if (v_lookahead_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(v_lookahead_1066_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1071_; lean_object* v_toGoalState_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1241_; 
v___x_1071_ = lean_st_ref_get(v_a_1050_);
v_toGoalState_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1071_, 1);
lean_dec(v_unused_1242_);
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1241_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_toGoalState_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1241_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_split_1076_; lean_object* v_lookaheads_1077_; uint8_t v___x_1078_; 
v_split_1076_ = lean_ctor_get(v_toGoalState_1072_, 14);
lean_inc_ref(v_split_1076_);
lean_dec_ref(v_toGoalState_1072_);
v_lookaheads_1077_ = lean_ctor_get(v_split_1076_, 5);
lean_inc(v_lookaheads_1077_);
lean_dec_ref(v_split_1076_);
v___x_1078_ = l_List_isEmpty___redArg(v_lookaheads_1077_);
lean_dec(v_lookaheads_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_toGoalState_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1064_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_st_ref_get(v_a_1050_);
v_toGoalState_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1080_, 1);
lean_dec(v_unused_1235_);
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1234_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_toGoalState_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1234_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_split_1085_; lean_object* v_lookaheads_1086_; lean_object* v___x_1087_; lean_object* v_toGoalState_1088_; lean_object* v_split_1089_; lean_object* v_mvarId_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1232_; 
v_split_1085_ = lean_ctor_get(v_toGoalState_1081_, 14);
lean_inc_ref(v_split_1085_);
lean_dec_ref(v_toGoalState_1081_);
v_lookaheads_1086_ = lean_ctor_get(v_split_1085_, 5);
lean_inc(v_lookaheads_1086_);
lean_dec_ref(v_split_1085_);
v___x_1087_ = lean_st_ref_take(v_a_1050_);
v_toGoalState_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_toGoalState_1088_);
v_split_1089_ = lean_ctor_get(v_toGoalState_1088_, 14);
lean_inc_ref(v_split_1089_);
v_mvarId_1090_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1233_);
v___x_1092_ = v___x_1087_;
v_isShared_1093_ = v_isSharedCheck_1232_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_mvarId_1090_);
lean_dec(v___x_1087_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1232_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_nextDeclIdx_1094_; lean_object* v_enodeMap_1095_; lean_object* v_exprs_1096_; lean_object* v_parents_1097_; lean_object* v_congrTable_1098_; lean_object* v_appMap_1099_; lean_object* v_indicesFound_1100_; lean_object* v_toProcess_1101_; uint8_t v_inconsistent_1102_; lean_object* v_nextIdx_1103_; lean_object* v_newRawFacts_1104_; lean_object* v_facts_1105_; lean_object* v_extThms_1106_; lean_object* v_ematch_1107_; lean_object* v_inj_1108_; lean_object* v_clean_1109_; lean_object* v_sstates_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1230_; 
v_nextDeclIdx_1094_ = lean_ctor_get(v_toGoalState_1088_, 0);
v_enodeMap_1095_ = lean_ctor_get(v_toGoalState_1088_, 1);
v_exprs_1096_ = lean_ctor_get(v_toGoalState_1088_, 2);
v_parents_1097_ = lean_ctor_get(v_toGoalState_1088_, 3);
v_congrTable_1098_ = lean_ctor_get(v_toGoalState_1088_, 4);
v_appMap_1099_ = lean_ctor_get(v_toGoalState_1088_, 5);
v_indicesFound_1100_ = lean_ctor_get(v_toGoalState_1088_, 6);
v_toProcess_1101_ = lean_ctor_get(v_toGoalState_1088_, 7);
v_inconsistent_1102_ = lean_ctor_get_uint8(v_toGoalState_1088_, sizeof(void*)*17);
v_nextIdx_1103_ = lean_ctor_get(v_toGoalState_1088_, 8);
v_newRawFacts_1104_ = lean_ctor_get(v_toGoalState_1088_, 9);
v_facts_1105_ = lean_ctor_get(v_toGoalState_1088_, 10);
v_extThms_1106_ = lean_ctor_get(v_toGoalState_1088_, 11);
v_ematch_1107_ = lean_ctor_get(v_toGoalState_1088_, 12);
v_inj_1108_ = lean_ctor_get(v_toGoalState_1088_, 13);
v_clean_1109_ = lean_ctor_get(v_toGoalState_1088_, 15);
v_sstates_1110_ = lean_ctor_get(v_toGoalState_1088_, 16);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_toGoalState_1088_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_toGoalState_1088_, 14);
lean_dec(v_unused_1231_);
v___x_1112_ = v_toGoalState_1088_;
v_isShared_1113_ = v_isSharedCheck_1230_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_sstates_1110_);
lean_inc(v_clean_1109_);
lean_inc(v_inj_1108_);
lean_inc(v_ematch_1107_);
lean_inc(v_extThms_1106_);
lean_inc(v_facts_1105_);
lean_inc(v_newRawFacts_1104_);
lean_inc(v_nextIdx_1103_);
lean_inc(v_toProcess_1101_);
lean_inc(v_indicesFound_1100_);
lean_inc(v_appMap_1099_);
lean_inc(v_congrTable_1098_);
lean_inc(v_parents_1097_);
lean_inc(v_exprs_1096_);
lean_inc(v_enodeMap_1095_);
lean_inc(v_nextDeclIdx_1094_);
lean_dec(v_toGoalState_1088_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1230_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_num_1114_; lean_object* v_candidates_1115_; lean_object* v_added_1116_; lean_object* v_resolved_1117_; lean_object* v_trace_1118_; lean_object* v_argPosMap_1119_; lean_object* v_argsAt_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1228_; 
v_num_1114_ = lean_ctor_get(v_split_1089_, 0);
v_candidates_1115_ = lean_ctor_get(v_split_1089_, 1);
v_added_1116_ = lean_ctor_get(v_split_1089_, 2);
v_resolved_1117_ = lean_ctor_get(v_split_1089_, 3);
v_trace_1118_ = lean_ctor_get(v_split_1089_, 4);
v_argPosMap_1119_ = lean_ctor_get(v_split_1089_, 6);
v_argsAt_1120_ = lean_ctor_get(v_split_1089_, 7);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_split_1089_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_split_1089_, 5);
lean_dec(v_unused_1229_);
v___x_1122_ = v_split_1089_;
v_isShared_1123_ = v_isSharedCheck_1228_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_argsAt_1120_);
lean_inc(v_argPosMap_1119_);
lean_inc(v_trace_1118_);
lean_inc(v_resolved_1117_);
lean_inc(v_added_1116_);
lean_inc(v_candidates_1115_);
lean_inc(v_num_1114_);
lean_dec(v_split_1089_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1228_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 5, v___x_1079_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_num_1114_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_candidates_1115_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_added_1116_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_resolved_1117_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_trace_1118_);
lean_ctor_set(v_reuseFailAlloc_1227_, 5, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1227_, 6, v_argPosMap_1119_);
lean_ctor_set(v_reuseFailAlloc_1227_, 7, v_argsAt_1120_);
v___x_1125_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 14, v___x_1125_);
v___x_1127_ = v___x_1112_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_nextDeclIdx_1094_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_enodeMap_1095_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_exprs_1096_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_parents_1097_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_congrTable_1098_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v_appMap_1099_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_indicesFound_1100_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_toProcess_1101_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_nextIdx_1103_);
lean_ctor_set(v_reuseFailAlloc_1226_, 9, v_newRawFacts_1104_);
lean_ctor_set(v_reuseFailAlloc_1226_, 10, v_facts_1105_);
lean_ctor_set(v_reuseFailAlloc_1226_, 11, v_extThms_1106_);
lean_ctor_set(v_reuseFailAlloc_1226_, 12, v_ematch_1107_);
lean_ctor_set(v_reuseFailAlloc_1226_, 13, v_inj_1108_);
lean_ctor_set(v_reuseFailAlloc_1226_, 14, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1226_, 15, v_clean_1109_);
lean_ctor_set(v_reuseFailAlloc_1226_, 16, v_sstates_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*17, v_inconsistent_1102_);
v___x_1127_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1127_);
v___x_1129_ = v___x_1092_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_mvarId_1090_);
v___x_1129_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1130_ = lean_st_ref_put(v_a_1050_, v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_box(v___x_1078_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1132_);
lean_ctor_set(v___x_1083_, 0, v___x_1079_);
v___x_1134_ = v___x_1083_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1134_);
lean_ctor_set(v___x_1074_, 0, v___x_1131_);
v___x_1136_ = v___x_1074_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1066_, v_lookaheads_1086_, v___x_1136_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_lookaheads_1086_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1214_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1214_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1214_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; 
v_fst_1142_ = lean_ctor_get(v_a_1138_, 0);
if (lean_obj_tag(v_fst_1142_) == 0)
{
lean_object* v_snd_1143_; lean_object* v_snd_1144_; uint8_t v___x_1145_; 
v_snd_1143_ = lean_ctor_get(v_a_1138_, 1);
lean_inc(v_snd_1143_);
lean_dec(v_a_1138_);
v_snd_1144_ = lean_ctor_get(v_snd_1143_, 1);
v___x_1145_ = lean_unbox(v_snd_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v_snd_1143_);
v___x_1146_ = lean_box(v___x_1078_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1146_);
v___x_1148_ = v___x_1140_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v_fst_1150_; lean_object* v___x_1151_; lean_object* v_toGoalState_1152_; lean_object* v_split_1153_; lean_object* v_mvarId_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1208_; 
v_fst_1150_ = lean_ctor_get(v_snd_1143_, 0);
lean_inc(v_fst_1150_);
lean_dec(v_snd_1143_);
v___x_1151_ = lean_st_ref_take(v_a_1050_);
v_toGoalState_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_toGoalState_1152_);
v_split_1153_ = lean_ctor_get(v_toGoalState_1152_, 14);
lean_inc_ref(v_split_1153_);
v_mvarId_1154_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1151_, 0);
lean_dec(v_unused_1209_);
v___x_1156_ = v___x_1151_;
v_isShared_1157_ = v_isSharedCheck_1208_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_mvarId_1154_);
lean_dec(v___x_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1208_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_nextDeclIdx_1158_; lean_object* v_enodeMap_1159_; lean_object* v_exprs_1160_; lean_object* v_parents_1161_; lean_object* v_congrTable_1162_; lean_object* v_appMap_1163_; lean_object* v_indicesFound_1164_; lean_object* v_toProcess_1165_; uint8_t v_inconsistent_1166_; lean_object* v_nextIdx_1167_; lean_object* v_newRawFacts_1168_; lean_object* v_facts_1169_; lean_object* v_extThms_1170_; lean_object* v_ematch_1171_; lean_object* v_inj_1172_; lean_object* v_clean_1173_; lean_object* v_sstates_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1206_; 
v_nextDeclIdx_1158_ = lean_ctor_get(v_toGoalState_1152_, 0);
v_enodeMap_1159_ = lean_ctor_get(v_toGoalState_1152_, 1);
v_exprs_1160_ = lean_ctor_get(v_toGoalState_1152_, 2);
v_parents_1161_ = lean_ctor_get(v_toGoalState_1152_, 3);
v_congrTable_1162_ = lean_ctor_get(v_toGoalState_1152_, 4);
v_appMap_1163_ = lean_ctor_get(v_toGoalState_1152_, 5);
v_indicesFound_1164_ = lean_ctor_get(v_toGoalState_1152_, 6);
v_toProcess_1165_ = lean_ctor_get(v_toGoalState_1152_, 7);
v_inconsistent_1166_ = lean_ctor_get_uint8(v_toGoalState_1152_, sizeof(void*)*17);
v_nextIdx_1167_ = lean_ctor_get(v_toGoalState_1152_, 8);
v_newRawFacts_1168_ = lean_ctor_get(v_toGoalState_1152_, 9);
v_facts_1169_ = lean_ctor_get(v_toGoalState_1152_, 10);
v_extThms_1170_ = lean_ctor_get(v_toGoalState_1152_, 11);
v_ematch_1171_ = lean_ctor_get(v_toGoalState_1152_, 12);
v_inj_1172_ = lean_ctor_get(v_toGoalState_1152_, 13);
v_clean_1173_ = lean_ctor_get(v_toGoalState_1152_, 15);
v_sstates_1174_ = lean_ctor_get(v_toGoalState_1152_, 16);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_toGoalState_1152_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v_toGoalState_1152_, 14);
lean_dec(v_unused_1207_);
v___x_1176_ = v_toGoalState_1152_;
v_isShared_1177_ = v_isSharedCheck_1206_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_sstates_1174_);
lean_inc(v_clean_1173_);
lean_inc(v_inj_1172_);
lean_inc(v_ematch_1171_);
lean_inc(v_extThms_1170_);
lean_inc(v_facts_1169_);
lean_inc(v_newRawFacts_1168_);
lean_inc(v_nextIdx_1167_);
lean_inc(v_toProcess_1165_);
lean_inc(v_indicesFound_1164_);
lean_inc(v_appMap_1163_);
lean_inc(v_congrTable_1162_);
lean_inc(v_parents_1161_);
lean_inc(v_exprs_1160_);
lean_inc(v_enodeMap_1159_);
lean_inc(v_nextDeclIdx_1158_);
lean_dec(v_toGoalState_1152_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1206_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_num_1178_; lean_object* v_candidates_1179_; lean_object* v_added_1180_; lean_object* v_resolved_1181_; lean_object* v_trace_1182_; lean_object* v_lookaheads_1183_; lean_object* v_argPosMap_1184_; lean_object* v_argsAt_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1205_; 
v_num_1178_ = lean_ctor_get(v_split_1153_, 0);
v_candidates_1179_ = lean_ctor_get(v_split_1153_, 1);
v_added_1180_ = lean_ctor_get(v_split_1153_, 2);
v_resolved_1181_ = lean_ctor_get(v_split_1153_, 3);
v_trace_1182_ = lean_ctor_get(v_split_1153_, 4);
v_lookaheads_1183_ = lean_ctor_get(v_split_1153_, 5);
v_argPosMap_1184_ = lean_ctor_get(v_split_1153_, 6);
v_argsAt_1185_ = lean_ctor_get(v_split_1153_, 7);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_split_1153_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1187_ = v_split_1153_;
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_argsAt_1185_);
lean_inc(v_argPosMap_1184_);
lean_inc(v_lookaheads_1183_);
lean_inc(v_trace_1182_);
lean_inc(v_resolved_1181_);
lean_inc(v_added_1180_);
lean_inc(v_candidates_1179_);
lean_inc(v_num_1178_);
lean_dec(v_split_1153_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = l_List_reverse___redArg(v_fst_1150_);
v___x_1190_ = l_List_appendTR___redArg(v_lookaheads_1183_, v___x_1189_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 5, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_num_1178_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_candidates_1179_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_added_1180_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_resolved_1181_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_trace_1182_);
lean_ctor_set(v_reuseFailAlloc_1204_, 5, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1204_, 6, v_argPosMap_1184_);
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_argsAt_1185_);
v___x_1192_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 14, v___x_1192_);
v___x_1194_ = v___x_1176_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_nextDeclIdx_1158_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_enodeMap_1159_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_exprs_1160_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_parents_1161_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_congrTable_1162_);
lean_ctor_set(v_reuseFailAlloc_1203_, 5, v_appMap_1163_);
lean_ctor_set(v_reuseFailAlloc_1203_, 6, v_indicesFound_1164_);
lean_ctor_set(v_reuseFailAlloc_1203_, 7, v_toProcess_1165_);
lean_ctor_set(v_reuseFailAlloc_1203_, 8, v_nextIdx_1167_);
lean_ctor_set(v_reuseFailAlloc_1203_, 9, v_newRawFacts_1168_);
lean_ctor_set(v_reuseFailAlloc_1203_, 10, v_facts_1169_);
lean_ctor_set(v_reuseFailAlloc_1203_, 11, v_extThms_1170_);
lean_ctor_set(v_reuseFailAlloc_1203_, 12, v_ematch_1171_);
lean_ctor_set(v_reuseFailAlloc_1203_, 13, v_inj_1172_);
lean_ctor_set(v_reuseFailAlloc_1203_, 14, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1203_, 15, v_clean_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 16, v_sstates_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*17, v_inconsistent_1166_);
v___x_1194_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1194_);
v___x_1196_ = v___x_1156_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_mvarId_1154_);
v___x_1196_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_st_ref_put(v_a_1050_, v___x_1196_);
v___x_1198_ = lean_box(v_lookahead_1066_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1198_);
v___x_1200_ = v___x_1140_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
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
lean_object* v_val_1210_; lean_object* v___x_1212_; 
lean_inc_ref(v_fst_1142_);
lean_dec(v_a_1138_);
v_val_1210_ = lean_ctor_get(v_fst_1142_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_fst_1142_, 1);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_val_1210_);
v___x_1212_ = v___x_1140_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_val_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1137_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1137_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
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
uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_del_object(v___x_1074_);
v___x_1236_ = 0;
v___x_1237_ = lean_box(v___x_1236_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1237_);
v___x_1239_ = v___x_1064_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1061_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1061_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_Grind_lookahead(v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec(v_a_1252_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1264_, lean_object* v_as_1265_, lean_object* v_as_x27_1266_, lean_object* v_b_1267_, lean_object* v_a_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1264_, v_as_x27_1266_, v_b_1267_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1281_, lean_object* v_as_1282_, lean_object* v_as_x27_1283_, lean_object* v_b_1284_, lean_object* v_a_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
uint8_t v___x_33605__boxed_1297_; lean_object* v_res_1298_; 
v___x_33605__boxed_1297_ = lean_unbox(v___x_1281_);
v_res_1298_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_33605__boxed_1297_, v_as_1282_, v_as_x27_1283_, v_b_1284_, v_a_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v_as_x27_1283_);
lean_dec(v_as_1282_);
return v_res_1298_;
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
