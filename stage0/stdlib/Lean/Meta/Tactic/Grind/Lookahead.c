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
lean_object* v_a_441_; lean_object* v_nextDeclIdx_442_; lean_object* v_enodeMap_443_; lean_object* v_exprs_444_; lean_object* v_parents_445_; lean_object* v_congrTable_446_; lean_object* v_appMap_447_; lean_object* v_indicesFound_448_; lean_object* v_internalizing_449_; uint8_t v_inconsistent_450_; lean_object* v_nextIdx_451_; lean_object* v_newRawFacts_452_; lean_object* v_facts_453_; lean_object* v_extThms_454_; lean_object* v_ematch_455_; lean_object* v_inj_456_; lean_object* v_split_457_; lean_object* v_clean_458_; lean_object* v_sstates_459_; lean_object* v_goalStack_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_508_; 
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
v_inconsistent_450_ = lean_ctor_get_uint8(v_toGoalState_421_, sizeof(void*)*19);
v_nextIdx_451_ = lean_ctor_get(v_toGoalState_421_, 9);
v_newRawFacts_452_ = lean_ctor_get(v_toGoalState_421_, 10);
v_facts_453_ = lean_ctor_get(v_toGoalState_421_, 11);
v_extThms_454_ = lean_ctor_get(v_toGoalState_421_, 12);
v_ematch_455_ = lean_ctor_get(v_toGoalState_421_, 13);
v_inj_456_ = lean_ctor_get(v_toGoalState_421_, 14);
v_split_457_ = lean_ctor_get(v_toGoalState_421_, 15);
v_clean_458_ = lean_ctor_get(v_toGoalState_421_, 16);
v_sstates_459_ = lean_ctor_get(v_toGoalState_421_, 17);
v_goalStack_460_ = lean_ctor_get(v_toGoalState_421_, 18);
v_isSharedCheck_508_ = !lean_is_exclusive(v_toGoalState_421_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_toGoalState_421_, 7);
lean_dec(v_unused_509_);
v___x_462_ = v_toGoalState_421_;
v_isShared_463_ = v_isSharedCheck_508_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_goalStack_460_);
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
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_508_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0));
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 7, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_nextDeclIdx_442_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_enodeMap_443_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_exprs_444_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_parents_445_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_congrTable_446_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_appMap_447_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_indicesFound_448_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_internalizing_449_);
lean_ctor_set(v_reuseFailAlloc_507_, 9, v_nextIdx_451_);
lean_ctor_set(v_reuseFailAlloc_507_, 10, v_newRawFacts_452_);
lean_ctor_set(v_reuseFailAlloc_507_, 11, v_facts_453_);
lean_ctor_set(v_reuseFailAlloc_507_, 12, v_extThms_454_);
lean_ctor_set(v_reuseFailAlloc_507_, 13, v_ematch_455_);
lean_ctor_set(v_reuseFailAlloc_507_, 14, v_inj_456_);
lean_ctor_set(v_reuseFailAlloc_507_, 15, v_split_457_);
lean_ctor_set(v_reuseFailAlloc_507_, 16, v_clean_458_);
lean_ctor_set(v_reuseFailAlloc_507_, 17, v_sstates_459_);
lean_ctor_set(v_reuseFailAlloc_507_, 18, v_goalStack_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*19, v_inconsistent_450_);
v___x_466_ = v_reuseFailAlloc_507_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_Expr_mvarId_x21(v_a_441_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_420_, v___y_422_);
lean_dec_ref(v_e_420_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_468_, v_a_470_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_490_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
lean_del_object(v___x_474_);
v___x_476_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_441_, v___y_429_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v_a_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec_ref_known(v_a_472_, 1);
lean_dec(v_a_441_);
v___x_486_ = lean_box(0);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_486_);
v___x_488_ = v___x_474_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_a_441_);
v_a_491_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_471_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_471_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref_known(v___x_468_, 2);
lean_dec(v_a_441_);
v_a_499_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_469_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_469_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_510_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_440_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_440_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_518_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_438_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_438_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_434_);
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_526_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_435_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_435_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_toGoalState_421_);
lean_dec_ref(v_e_420_);
v_a_534_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_433_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_433_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(lean_object* v_mvarId_542_, lean_object* v_e_543_, lean_object* v_toGoalState_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(v_mvarId_542_, v_e_543_, v_toGoalState_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_env_564_; uint8_t v___x_565_; lean_object* v_env_566_; lean_object* v___x_567_; lean_object* v_toCold_568_; lean_object* v_mctx_569_; lean_object* v_lctx_570_; lean_object* v_options_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_563_ = lean_st_ref_get(v___y_561_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_563_);
v___x_565_ = 0;
v_env_566_ = l_Lean_Environment_setRecordingDeps(v_env_564_, v___x_565_);
v___x_567_ = lean_st_ref_get(v___y_559_);
v_toCold_568_ = lean_ctor_get(v___y_560_, 0);
v_mctx_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_mctx_569_);
lean_dec(v___x_567_);
v_lctx_570_ = lean_ctor_get(v___y_558_, 2);
v_options_571_ = lean_ctor_get(v_toCold_568_, 2);
lean_inc_ref(v_options_571_);
lean_inc_ref(v_lctx_570_);
v___x_572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_572_, 0, v_env_566_);
lean_ctor_set(v___x_572_, 1, v_mctx_569_);
lean_ctor_set(v___x_572_, 2, v_lctx_570_);
lean_ctor_set(v___x_572_, 3, v_options_571_);
v___x_573_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_msgData_557_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object* v_msgData_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_582_; double v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_float_of_nat(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_ref_594_; lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_641_; 
v_ref_594_ = lean_ctor_get(v___y_591_, 2);
v___x_595_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_641_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_641_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_641_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v_traceState_601_; lean_object* v_env_602_; lean_object* v_nextMacroScope_603_; lean_object* v_ngen_604_; lean_object* v_auxDeclNGen_605_; lean_object* v_cache_606_; lean_object* v_recordedDeps_607_; lean_object* v_messages_608_; lean_object* v_infoState_609_; lean_object* v_snapshotTasks_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_640_; 
v___x_600_ = lean_st_ref_take(v___y_592_);
v_traceState_601_ = lean_ctor_get(v___x_600_, 4);
v_env_602_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_603_ = lean_ctor_get(v___x_600_, 1);
v_ngen_604_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_605_ = lean_ctor_get(v___x_600_, 3);
v_cache_606_ = lean_ctor_get(v___x_600_, 5);
v_recordedDeps_607_ = lean_ctor_get(v___x_600_, 6);
v_messages_608_ = lean_ctor_get(v___x_600_, 7);
v_infoState_609_ = lean_ctor_get(v___x_600_, 8);
v_snapshotTasks_610_ = lean_ctor_get(v___x_600_, 9);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_640_ == 0)
{
v___x_612_ = v___x_600_;
v_isShared_613_ = v_isSharedCheck_640_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snapshotTasks_610_);
lean_inc(v_infoState_609_);
lean_inc(v_messages_608_);
lean_inc(v_recordedDeps_607_);
lean_inc(v_cache_606_);
lean_inc(v_traceState_601_);
lean_inc(v_auxDeclNGen_605_);
lean_inc(v_ngen_604_);
lean_inc(v_nextMacroScope_603_);
lean_inc(v_env_602_);
lean_dec(v___x_600_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_640_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint64_t v_tid_614_; lean_object* v_traces_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_639_; 
v_tid_614_ = lean_ctor_get_uint64(v_traceState_601_, sizeof(void*)*1);
v_traces_615_ = lean_ctor_get(v_traceState_601_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_traceState_601_);
if (v_isSharedCheck_639_ == 0)
{
v___x_617_ = v_traceState_601_;
v_isShared_618_ = v_isSharedCheck_639_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_traces_615_);
lean_dec(v_traceState_601_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_639_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; double v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_box(0);
v___x_621_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
v___x_622_ = 0;
v___x_623_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_624_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_624_, 0, v_cls_587_);
lean_ctor_set(v___x_624_, 1, v___x_620_);
lean_ctor_set(v___x_624_, 2, v___x_623_);
lean_ctor_set_float(v___x_624_, sizeof(void*)*3, v___x_621_);
lean_ctor_set_float(v___x_624_, sizeof(void*)*3 + 8, v___x_621_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*3 + 16, v___x_622_);
v___x_625_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2));
v___x_626_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v_a_596_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_inc(v_ref_594_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_ref_594_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_PersistentArray_push___redArg(v_traces_615_, v___x_627_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_628_);
v___x_630_ = v___x_617_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_628_);
lean_ctor_set_uint64(v_reuseFailAlloc_638_, sizeof(void*)*1, v_tid_614_);
v___x_630_ = v_reuseFailAlloc_638_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 4, v___x_630_);
v___x_632_ = v___x_612_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_env_602_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_nextMacroScope_603_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_ngen_604_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_auxDeclNGen_605_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_cache_606_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_recordedDeps_607_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_messages_608_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_infoState_609_);
lean_ctor_set(v_reuseFailAlloc_637_, 9, v_snapshotTasks_610_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_st_ref_put(v___y_592_, v___x_632_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_619_);
v___x_635_ = v___x_598_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_619_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_642_, lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_642_, v_msg_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_672_ = l_Lean_Name_append(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14(void){
_start:
{
lean_object* v_cls_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_cls_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_680_ = l_Lean_Name_append(v___x_679_, v_cls_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v_config_735_; lean_object* v_toCold_736_; lean_object* v_options_737_; lean_object* v_simp_738_; lean_object* v_simpMethods_739_; lean_object* v_symSimpMethods_740_; lean_object* v_symDSimpMethods_741_; lean_object* v_identity_742_; lean_object* v_activeSolvers_743_; lean_object* v_anchorRefs_x3f_744_; uint8_t v_reportMVarIssue_745_; lean_object* v_splitSource_746_; lean_object* v_ematchDiagSource_747_; lean_object* v_symPrios_748_; lean_object* v_extensions_749_; uint8_t v_debug_750_; uint8_t v_ematchDiag_751_; uint8_t v_trace_752_; uint8_t v_markInstances_753_; uint8_t v_lax_754_; uint8_t v_suggestions_755_; uint8_t v_locals_756_; lean_object* v_splits_757_; lean_object* v_ematch_758_; lean_object* v_gen_759_; lean_object* v_genLocal_760_; lean_object* v_instances_761_; uint8_t v_matchEqs_762_; uint8_t v_splitMatch_763_; uint8_t v_splitIte_764_; uint8_t v_splitIndPred_765_; uint8_t v_splitImp_766_; lean_object* v_canonHeartbeats_767_; uint8_t v_ext_768_; uint8_t v_extAll_769_; uint8_t v_etaStruct_770_; uint8_t v_funext_771_; uint8_t v_lookahead_772_; uint8_t v_verbose_773_; uint8_t v_clean_774_; uint8_t v_mbtc_775_; uint8_t v_zetaDelta_776_; uint8_t v_zeta_777_; uint8_t v_distrib_778_; lean_object* v_maxChar_779_; uint8_t v_ring_780_; lean_object* v_ringSteps_781_; lean_object* v_ringMaxDegree_782_; uint8_t v_linarith_783_; uint8_t v_lia_784_; lean_object* v_liaSteps_785_; lean_object* v_liaReorders_786_; lean_object* v_liaReorderCases_787_; uint8_t v_hom_788_; uint8_t v_ac_789_; lean_object* v_acSteps_790_; lean_object* v_exp_791_; uint8_t v_abstractProof_792_; uint8_t v_inj_793_; uint8_t v_order_794_; lean_object* v_min_795_; lean_object* v_detailed_796_; uint8_t v_useSorry_797_; uint8_t v_revert_798_; uint8_t v_funCC_799_; uint8_t v_reducible_800_; lean_object* v_maxSuggestions_801_; lean_object* v_inheritedTraceOptions_802_; uint8_t v_hasTrace_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___x_859_; 
v_config_735_ = lean_ctor_get(v_a_684_, 4);
v_toCold_736_ = lean_ctor_get(v_a_690_, 0);
v_options_737_ = lean_ctor_get(v_toCold_736_, 2);
v_simp_738_ = lean_ctor_get(v_a_684_, 0);
v_simpMethods_739_ = lean_ctor_get(v_a_684_, 1);
v_symSimpMethods_740_ = lean_ctor_get(v_a_684_, 2);
v_symDSimpMethods_741_ = lean_ctor_get(v_a_684_, 3);
v_identity_742_ = lean_ctor_get(v_a_684_, 5);
v_activeSolvers_743_ = lean_ctor_get(v_a_684_, 6);
v_anchorRefs_x3f_744_ = lean_ctor_get(v_a_684_, 7);
v_reportMVarIssue_745_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*12 + 1);
v_splitSource_746_ = lean_ctor_get(v_a_684_, 8);
v_ematchDiagSource_747_ = lean_ctor_get(v_a_684_, 9);
v_symPrios_748_ = lean_ctor_get(v_a_684_, 10);
v_extensions_749_ = lean_ctor_get(v_a_684_, 11);
v_debug_750_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*12 + 2);
v_ematchDiag_751_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*12 + 3);
v_trace_752_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17);
v_markInstances_753_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 1);
v_lax_754_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 2);
v_suggestions_755_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 3);
v_locals_756_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 4);
v_splits_757_ = lean_ctor_get(v_config_735_, 0);
v_ematch_758_ = lean_ctor_get(v_config_735_, 1);
v_gen_759_ = lean_ctor_get(v_config_735_, 2);
v_genLocal_760_ = lean_ctor_get(v_config_735_, 3);
v_instances_761_ = lean_ctor_get(v_config_735_, 4);
v_matchEqs_762_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 5);
v_splitMatch_763_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 6);
v_splitIte_764_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 7);
v_splitIndPred_765_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 8);
v_splitImp_766_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 9);
v_canonHeartbeats_767_ = lean_ctor_get(v_config_735_, 5);
v_ext_768_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 10);
v_extAll_769_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 11);
v_etaStruct_770_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 12);
v_funext_771_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 13);
v_lookahead_772_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 14);
v_verbose_773_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 15);
v_clean_774_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 16);
v_mbtc_775_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 18);
v_zetaDelta_776_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 19);
v_zeta_777_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 20);
v_distrib_778_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 21);
v_maxChar_779_ = lean_ctor_get(v_config_735_, 6);
v_ring_780_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 22);
v_ringSteps_781_ = lean_ctor_get(v_config_735_, 7);
v_ringMaxDegree_782_ = lean_ctor_get(v_config_735_, 8);
v_linarith_783_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 23);
v_lia_784_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 24);
v_liaSteps_785_ = lean_ctor_get(v_config_735_, 9);
v_liaReorders_786_ = lean_ctor_get(v_config_735_, 10);
v_liaReorderCases_787_ = lean_ctor_get(v_config_735_, 11);
v_hom_788_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 25);
v_ac_789_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 26);
v_acSteps_790_ = lean_ctor_get(v_config_735_, 12);
v_exp_791_ = lean_ctor_get(v_config_735_, 13);
v_abstractProof_792_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 27);
v_inj_793_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 28);
v_order_794_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 29);
v_min_795_ = lean_ctor_get(v_config_735_, 14);
v_detailed_796_ = lean_ctor_get(v_config_735_, 15);
v_useSorry_797_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 30);
v_revert_798_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 31);
v_funCC_799_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 32);
v_reducible_800_ = lean_ctor_get_uint8(v_config_735_, sizeof(void*)*17 + 33);
v_maxSuggestions_801_ = lean_ctor_get(v_config_735_, 16);
v_inheritedTraceOptions_802_ = lean_ctor_get(v_toCold_736_, 11);
v_hasTrace_803_ = lean_ctor_get_uint8(v_options_737_, sizeof(void*)*1);
v___x_804_ = 1;
lean_inc(v_maxSuggestions_801_);
lean_inc(v_detailed_796_);
lean_inc(v_min_795_);
lean_inc(v_exp_791_);
lean_inc(v_acSteps_790_);
lean_inc(v_liaReorderCases_787_);
lean_inc(v_liaReorders_786_);
lean_inc(v_liaSteps_785_);
lean_inc(v_ringMaxDegree_782_);
lean_inc(v_ringSteps_781_);
lean_inc(v_maxChar_779_);
lean_inc(v_canonHeartbeats_767_);
lean_inc(v_instances_761_);
lean_inc(v_genLocal_760_);
lean_inc(v_gen_759_);
lean_inc(v_ematch_758_);
lean_inc(v_splits_757_);
v___x_805_ = lean_alloc_ctor(0, 17, 34);
lean_ctor_set(v___x_805_, 0, v_splits_757_);
lean_ctor_set(v___x_805_, 1, v_ematch_758_);
lean_ctor_set(v___x_805_, 2, v_gen_759_);
lean_ctor_set(v___x_805_, 3, v_genLocal_760_);
lean_ctor_set(v___x_805_, 4, v_instances_761_);
lean_ctor_set(v___x_805_, 5, v_canonHeartbeats_767_);
lean_ctor_set(v___x_805_, 6, v_maxChar_779_);
lean_ctor_set(v___x_805_, 7, v_ringSteps_781_);
lean_ctor_set(v___x_805_, 8, v_ringMaxDegree_782_);
lean_ctor_set(v___x_805_, 9, v_liaSteps_785_);
lean_ctor_set(v___x_805_, 10, v_liaReorders_786_);
lean_ctor_set(v___x_805_, 11, v_liaReorderCases_787_);
lean_ctor_set(v___x_805_, 12, v_acSteps_790_);
lean_ctor_set(v___x_805_, 13, v_exp_791_);
lean_ctor_set(v___x_805_, 14, v_min_795_);
lean_ctor_set(v___x_805_, 15, v_detailed_796_);
lean_ctor_set(v___x_805_, 16, v_maxSuggestions_801_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17, v_trace_752_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 1, v_markInstances_753_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 2, v_lax_754_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 3, v_suggestions_755_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 4, v_locals_756_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 5, v_matchEqs_762_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 6, v_splitMatch_763_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 7, v_splitIte_764_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 8, v_splitIndPred_765_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 9, v_splitImp_766_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 10, v_ext_768_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 11, v_extAll_769_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 12, v_etaStruct_770_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 13, v_funext_771_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 14, v_lookahead_772_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 15, v_verbose_773_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 16, v_clean_774_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 17, v___x_804_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 18, v_mbtc_775_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 19, v_zetaDelta_776_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 20, v_zeta_777_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 21, v_distrib_778_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 22, v_ring_780_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 23, v_linarith_783_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 24, v_lia_784_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 25, v_hom_788_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 26, v_ac_789_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 27, v_abstractProof_792_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 28, v_inj_793_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 29, v_order_794_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 30, v_useSorry_797_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 31, v_revert_798_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 32, v_funCC_799_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*17 + 33, v_reducible_800_);
lean_inc_ref(v_extensions_749_);
lean_inc_ref(v_symPrios_748_);
lean_inc(v_ematchDiagSource_747_);
lean_inc(v_splitSource_746_);
lean_inc(v_anchorRefs_x3f_744_);
lean_inc_ref(v_activeSolvers_743_);
lean_inc(v_identity_742_);
lean_inc_ref(v_symDSimpMethods_741_);
lean_inc_ref(v_symSimpMethods_740_);
lean_inc_ref(v_simpMethods_739_);
lean_inc_ref(v_simp_738_);
v___x_859_ = lean_alloc_ctor(0, 12, 4);
lean_ctor_set(v___x_859_, 0, v_simp_738_);
lean_ctor_set(v___x_859_, 1, v_simpMethods_739_);
lean_ctor_set(v___x_859_, 2, v_symSimpMethods_740_);
lean_ctor_set(v___x_859_, 3, v_symDSimpMethods_741_);
lean_ctor_set(v___x_859_, 4, v___x_805_);
lean_ctor_set(v___x_859_, 5, v_identity_742_);
lean_ctor_set(v___x_859_, 6, v_activeSolvers_743_);
lean_ctor_set(v___x_859_, 7, v_anchorRefs_x3f_744_);
lean_ctor_set(v___x_859_, 8, v_splitSource_746_);
lean_ctor_set(v___x_859_, 9, v_ematchDiagSource_747_);
lean_ctor_set(v___x_859_, 10, v_symPrios_748_);
lean_ctor_set(v___x_859_, 11, v_extensions_749_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*12, v___x_804_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*12 + 1, v_reportMVarIssue_745_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*12 + 2, v_debug_750_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*12 + 3, v_ematchDiag_751_);
if (v_hasTrace_803_ == 0)
{
v___y_807_ = v_a_682_;
v___y_808_ = v_a_683_;
v___y_809_ = v___x_859_;
v___y_810_ = v_a_685_;
v___y_811_ = v_a_686_;
v___y_812_ = v_a_687_;
v___y_813_ = v_a_688_;
v___y_814_ = v_a_689_;
v___y_815_ = v_a_690_;
v___y_816_ = v_a_691_;
goto v___jp_806_;
}
else
{
lean_object* v_cls_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_cls_860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
v___x_862_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_802_, v_options_737_, v___x_861_);
if (v___x_862_ == 0)
{
v___y_807_ = v_a_682_;
v___y_808_ = v_a_683_;
v___y_809_ = v___x_859_;
v___y_810_ = v_a_685_;
v___y_811_ = v_a_686_;
v___y_812_ = v_a_687_;
v___y_813_ = v_a_688_;
v___y_814_ = v_a_689_;
v___y_815_ = v_a_690_;
v___y_816_ = v_a_691_;
goto v___jp_806_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Grind_updateLastTag(v_a_682_, v_a_683_, v___x_859_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref_known(v___x_863_, 1);
lean_inc_ref(v_e_681_);
v___x_864_ = l_Lean_MessageData_ofExpr(v_e_681_);
v___x_865_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_860_, v___x_864_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec_ref_known(v___x_865_, 1);
v___y_807_ = v_a_682_;
v___y_808_ = v_a_683_;
v___y_809_ = v___x_859_;
v___y_810_ = v_a_685_;
v___y_811_ = v_a_686_;
v___y_812_ = v_a_687_;
v___y_813_ = v_a_688_;
v___y_814_ = v_a_689_;
v___y_815_ = v_a_690_;
v___y_816_ = v_a_691_;
goto v___jp_806_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref_known(v___x_859_, 12);
lean_dec_ref(v_e_681_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
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
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref_known(v___x_859_, 12);
lean_dec_ref(v_e_681_);
v_a_874_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_863_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_863_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
v___jp_693_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_681_);
v___x_706_ = l_Lean_mkAppB(v___x_705_, v_e_681_, v___y_694_);
v___x_707_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_681_, v___x_706_, v___y_695_, v___y_697_, v___y_699_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; 
lean_dec_ref_known(v___x_707_, 1);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc(v___y_696_);
lean_inc(v___y_695_);
v___x_708_ = lean_grind_process_to_do(v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v___x_708_, 0);
lean_dec(v_unused_718_);
v___x_710_ = v___x_708_;
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_708_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = 1;
v___x_713_ = lean_box(v___x_712_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___y_697_);
v_a_727_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_707_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_707_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
v___jp_806_:
{
lean_object* v___x_817_; lean_object* v_toGoalState_818_; lean_object* v_mvarId_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v___x_817_ = lean_st_ref_get(v___y_807_);
v_toGoalState_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_toGoalState_818_);
v_mvarId_819_ = lean_ctor_get(v___x_817_, 1);
lean_inc(v_mvarId_819_);
lean_dec(v___x_817_);
lean_inc_ref(v_e_681_);
v___f_820_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_820_, 0, v_mvarId_819_);
lean_closure_set(v___f_820_, 1, v_e_681_);
lean_closure_set(v___f_820_, 2, v_toGoalState_818_);
v___x_821_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_820_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_850_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_850_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_850_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_850_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
if (lean_obj_tag(v_a_822_) == 1)
{
lean_object* v_toCold_826_; lean_object* v_options_827_; uint8_t v_hasTrace_828_; 
lean_del_object(v___x_824_);
v_toCold_826_ = lean_ctor_get(v___y_815_, 0);
v_options_827_ = lean_ctor_get(v_toCold_826_, 2);
v_hasTrace_828_ = lean_ctor_get_uint8(v_options_827_, sizeof(void*)*1);
if (v_hasTrace_828_ == 0)
{
lean_object* v_val_829_; 
v_val_829_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_a_822_, 1);
v___y_694_ = v_val_829_;
v___y_695_ = v___y_807_;
v___y_696_ = v___y_808_;
v___y_697_ = v___y_809_;
v___y_698_ = v___y_810_;
v___y_699_ = v___y_811_;
v___y_700_ = v___y_812_;
v___y_701_ = v___y_813_;
v___y_702_ = v___y_814_;
v___y_703_ = v___y_815_;
v___y_704_ = v___y_816_;
goto v___jp_693_;
}
else
{
lean_object* v_val_830_; lean_object* v_inheritedTraceOptions_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_val_830_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v_a_822_, 1);
v_inheritedTraceOptions_831_ = lean_ctor_get(v_toCold_826_, 11);
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
v___x_834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_831_, v_options_827_, v___x_833_);
if (v___x_834_ == 0)
{
v___y_694_ = v_val_830_;
v___y_695_ = v___y_807_;
v___y_696_ = v___y_808_;
v___y_697_ = v___y_809_;
v___y_698_ = v___y_810_;
v___y_699_ = v___y_811_;
v___y_700_ = v___y_812_;
v___y_701_ = v___y_813_;
v___y_702_ = v___y_814_;
v___y_703_ = v___y_815_;
v___y_704_ = v___y_816_;
goto v___jp_693_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc_ref(v_e_681_);
v___x_835_ = l_Lean_MessageData_ofExpr(v_e_681_);
v___x_836_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_832_, v___x_835_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_dec_ref_known(v___x_836_, 1);
v___y_694_ = v_val_830_;
v___y_695_ = v___y_807_;
v___y_696_ = v___y_808_;
v___y_697_ = v___y_809_;
v___y_698_ = v___y_810_;
v___y_699_ = v___y_811_;
v___y_700_ = v___y_812_;
v___y_701_ = v___y_813_;
v___y_702_ = v___y_814_;
v___y_703_ = v___y_815_;
v___y_704_ = v___y_816_;
goto v___jp_693_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_val_830_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_e_681_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
else
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec(v_a_822_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_e_681_);
v___x_845_ = 0;
v___x_846_ = lean_box(v___x_845_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_846_);
v___x_848_ = v___x_824_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
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
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___y_809_);
lean_dec_ref(v_e_681_);
v_a_851_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_821_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_821_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec(v_a_883_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_895_, v_msg_896_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_909_, lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_909_, v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec(v___y_911_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_923_, lean_object* v_as_x27_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
if (lean_obj_tag(v_as_x27_924_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_925_);
return v___x_937_;
}
else
{
lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1040_; 
v_snd_938_ = lean_ctor_get(v_b_925_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_b_925_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_b_925_, 0);
lean_dec(v_unused_1041_);
v___x_940_ = v_b_925_;
v_isShared_941_ = v_isSharedCheck_1040_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_dec(v_b_925_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1040_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1039_; 
v_head_942_ = lean_ctor_get(v_as_x27_924_, 0);
v_tail_943_ = lean_ctor_get(v_as_x27_924_, 1);
v_fst_944_ = lean_ctor_get(v_snd_938_, 0);
v_snd_945_ = lean_ctor_get(v_snd_938_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_snd_938_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_947_ = v_snd_938_;
v_isShared_948_ = v_isSharedCheck_1039_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_944_);
lean_dec(v_snd_938_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1039_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_926_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1030_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_1030_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1030_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = lean_unbox(v_a_951_);
lean_dec(v_a_951_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_del_object(v___x_953_);
lean_inc(v_head_942_);
v___x_956_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_942_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
switch(lean_obj_tag(v_a_957_))
{
case 0:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v_snd_945_);
v___x_958_ = lean_box(v___x_923_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_958_);
v___x_960_ = v___x_947_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_960_);
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_962_ = v___x_940_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_as_x27_924_ = v_tail_943_;
v_b_925_ = v___x_962_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_inc(v_head_942_);
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v_head_942_);
lean_ctor_set(v___x_966_, 1, v_fst_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_966_);
v___x_968_ = v___x_947_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_snd_945_);
v___x_968_ = v_reuseFailAlloc_973_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_968_);
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_970_ = v___x_940_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_as_x27_924_ = v_tail_943_;
v_b_925_ = v___x_970_;
goto _start;
}
}
}
default: 
{
uint8_t v_tryPostpone_974_; 
v_tryPostpone_974_ = lean_ctor_get_uint8(v_a_957_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_957_, 1);
if (v_tryPostpone_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_942_);
v___x_976_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_975_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; uint8_t v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = lean_unbox(v_a_977_);
lean_dec(v_a_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_inc(v_head_942_);
v___x_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_979_, 0, v_head_942_);
lean_ctor_set(v___x_979_, 1, v_fst_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_979_);
v___x_981_ = v___x_947_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_snd_945_);
v___x_981_ = v_reuseFailAlloc_986_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_981_);
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_983_ = v___x_940_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_as_x27_924_ = v_tail_943_;
v_b_925_ = v___x_983_;
goto _start;
}
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_dec(v_snd_945_);
v___x_987_ = lean_box(v___x_923_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_987_);
v___x_989_ = v___x_947_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_994_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_989_);
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_991_ = v___x_940_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_as_x27_924_ = v_tail_943_;
v_b_925_ = v___x_991_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_947_);
lean_dec(v_snd_945_);
lean_dec(v_fst_944_);
lean_del_object(v___x_940_);
v_a_995_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_976_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_976_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_inc(v_head_942_);
v___x_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_head_942_);
lean_ctor_set(v___x_1003_, 1, v_fst_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_1003_);
v___x_1005_ = v___x_947_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_snd_945_);
v___x_1005_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_1005_);
lean_ctor_set(v___x_940_, 0, v___x_949_);
v___x_1007_ = v___x_940_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
v_as_x27_924_ = v_tail_943_;
v_b_925_ = v___x_1007_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_947_);
lean_dec(v_snd_945_);
lean_dec(v_fst_944_);
lean_del_object(v___x_940_);
v_a_1011_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_956_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_956_);
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
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1019_ = lean_box(v___x_923_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
if (v_isShared_948_ == 0)
{
v___x_1022_ = v___x_947_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_snd_945_);
v___x_1022_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_1022_);
lean_ctor_set(v___x_940_, 0, v___x_1020_);
v___x_1024_ = v___x_940_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_1024_);
v___x_1026_ = v___x_953_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_947_);
lean_dec(v_snd_945_);
lean_dec(v_fst_944_);
lean_del_object(v___x_940_);
v_a_1031_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_950_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_950_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1042_, lean_object* v_as_x27_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v___x_33494__boxed_1056_; lean_object* v_res_1057_; 
v___x_33494__boxed_1056_ = lean_unbox(v___x_1042_);
v_res_1057_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_33494__boxed_1056_, v_as_x27_1043_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v_as_x27_1043_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1060_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1255_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1255_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1255_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
uint8_t v_lookahead_1074_; 
v_lookahead_1074_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*17 + 14);
lean_dec(v_a_1070_);
if (v_lookahead_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_box(v_lookahead_1074_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v_toGoalState_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1253_; 
v___x_1079_ = lean_st_ref_get(v_a_1058_);
v_toGoalState_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v___x_1079_, 1);
lean_dec(v_unused_1254_);
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1253_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_toGoalState_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1253_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_split_1084_; lean_object* v_lookaheads_1085_; uint8_t v___x_1086_; 
v_split_1084_ = lean_ctor_get(v_toGoalState_1080_, 15);
lean_inc_ref(v_split_1084_);
lean_dec_ref(v_toGoalState_1080_);
v_lookaheads_1085_ = lean_ctor_get(v_split_1084_, 5);
lean_inc(v_lookaheads_1085_);
lean_dec_ref(v_split_1084_);
v___x_1086_ = l_List_isEmpty___redArg(v_lookaheads_1085_);
lean_dec(v_lookaheads_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_toGoalState_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1246_; 
lean_del_object(v___x_1072_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_st_ref_get(v_a_1058_);
v_toGoalState_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1088_, 1);
lean_dec(v_unused_1247_);
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1246_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_toGoalState_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1246_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_split_1093_; lean_object* v_lookaheads_1094_; lean_object* v___x_1095_; lean_object* v_toGoalState_1096_; lean_object* v_split_1097_; lean_object* v_mvarId_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1244_; 
v_split_1093_ = lean_ctor_get(v_toGoalState_1089_, 15);
lean_inc_ref(v_split_1093_);
lean_dec_ref(v_toGoalState_1089_);
v_lookaheads_1094_ = lean_ctor_get(v_split_1093_, 5);
lean_inc(v_lookaheads_1094_);
lean_dec_ref(v_split_1093_);
v___x_1095_ = lean_st_ref_take(v_a_1058_);
v_toGoalState_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_toGoalState_1096_);
v_split_1097_ = lean_ctor_get(v_toGoalState_1096_, 15);
lean_inc_ref(v_split_1097_);
v_mvarId_1098_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1095_, 0);
lean_dec(v_unused_1245_);
v___x_1100_ = v___x_1095_;
v_isShared_1101_ = v_isSharedCheck_1244_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_mvarId_1098_);
lean_dec(v___x_1095_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1244_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_nextDeclIdx_1102_; lean_object* v_enodeMap_1103_; lean_object* v_exprs_1104_; lean_object* v_parents_1105_; lean_object* v_congrTable_1106_; lean_object* v_appMap_1107_; lean_object* v_indicesFound_1108_; lean_object* v_toProcess_1109_; lean_object* v_internalizing_1110_; uint8_t v_inconsistent_1111_; lean_object* v_nextIdx_1112_; lean_object* v_newRawFacts_1113_; lean_object* v_facts_1114_; lean_object* v_extThms_1115_; lean_object* v_ematch_1116_; lean_object* v_inj_1117_; lean_object* v_clean_1118_; lean_object* v_sstates_1119_; lean_object* v_goalStack_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1242_; 
v_nextDeclIdx_1102_ = lean_ctor_get(v_toGoalState_1096_, 0);
v_enodeMap_1103_ = lean_ctor_get(v_toGoalState_1096_, 1);
v_exprs_1104_ = lean_ctor_get(v_toGoalState_1096_, 2);
v_parents_1105_ = lean_ctor_get(v_toGoalState_1096_, 3);
v_congrTable_1106_ = lean_ctor_get(v_toGoalState_1096_, 4);
v_appMap_1107_ = lean_ctor_get(v_toGoalState_1096_, 5);
v_indicesFound_1108_ = lean_ctor_get(v_toGoalState_1096_, 6);
v_toProcess_1109_ = lean_ctor_get(v_toGoalState_1096_, 7);
v_internalizing_1110_ = lean_ctor_get(v_toGoalState_1096_, 8);
v_inconsistent_1111_ = lean_ctor_get_uint8(v_toGoalState_1096_, sizeof(void*)*19);
v_nextIdx_1112_ = lean_ctor_get(v_toGoalState_1096_, 9);
v_newRawFacts_1113_ = lean_ctor_get(v_toGoalState_1096_, 10);
v_facts_1114_ = lean_ctor_get(v_toGoalState_1096_, 11);
v_extThms_1115_ = lean_ctor_get(v_toGoalState_1096_, 12);
v_ematch_1116_ = lean_ctor_get(v_toGoalState_1096_, 13);
v_inj_1117_ = lean_ctor_get(v_toGoalState_1096_, 14);
v_clean_1118_ = lean_ctor_get(v_toGoalState_1096_, 16);
v_sstates_1119_ = lean_ctor_get(v_toGoalState_1096_, 17);
v_goalStack_1120_ = lean_ctor_get(v_toGoalState_1096_, 18);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_toGoalState_1096_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_toGoalState_1096_, 15);
lean_dec(v_unused_1243_);
v___x_1122_ = v_toGoalState_1096_;
v_isShared_1123_ = v_isSharedCheck_1242_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_goalStack_1120_);
lean_inc(v_sstates_1119_);
lean_inc(v_clean_1118_);
lean_inc(v_inj_1117_);
lean_inc(v_ematch_1116_);
lean_inc(v_extThms_1115_);
lean_inc(v_facts_1114_);
lean_inc(v_newRawFacts_1113_);
lean_inc(v_nextIdx_1112_);
lean_inc(v_internalizing_1110_);
lean_inc(v_toProcess_1109_);
lean_inc(v_indicesFound_1108_);
lean_inc(v_appMap_1107_);
lean_inc(v_congrTable_1106_);
lean_inc(v_parents_1105_);
lean_inc(v_exprs_1104_);
lean_inc(v_enodeMap_1103_);
lean_inc(v_nextDeclIdx_1102_);
lean_dec(v_toGoalState_1096_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1242_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_num_1124_; lean_object* v_candidates_1125_; lean_object* v_added_1126_; lean_object* v_resolved_1127_; lean_object* v_trace_1128_; lean_object* v_argPosMap_1129_; lean_object* v_argsAt_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1240_; 
v_num_1124_ = lean_ctor_get(v_split_1097_, 0);
v_candidates_1125_ = lean_ctor_get(v_split_1097_, 1);
v_added_1126_ = lean_ctor_get(v_split_1097_, 2);
v_resolved_1127_ = lean_ctor_get(v_split_1097_, 3);
v_trace_1128_ = lean_ctor_get(v_split_1097_, 4);
v_argPosMap_1129_ = lean_ctor_get(v_split_1097_, 6);
v_argsAt_1130_ = lean_ctor_get(v_split_1097_, 7);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_split_1097_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v_split_1097_, 5);
lean_dec(v_unused_1241_);
v___x_1132_ = v_split_1097_;
v_isShared_1133_ = v_isSharedCheck_1240_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_argsAt_1130_);
lean_inc(v_argPosMap_1129_);
lean_inc(v_trace_1128_);
lean_inc(v_resolved_1127_);
lean_inc(v_added_1126_);
lean_inc(v_candidates_1125_);
lean_inc(v_num_1124_);
lean_dec(v_split_1097_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1240_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 5, v___x_1087_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_num_1124_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_candidates_1125_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_added_1126_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_resolved_1127_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_trace_1128_);
lean_ctor_set(v_reuseFailAlloc_1239_, 5, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1239_, 6, v_argPosMap_1129_);
lean_ctor_set(v_reuseFailAlloc_1239_, 7, v_argsAt_1130_);
v___x_1135_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 15, v___x_1135_);
v___x_1137_ = v___x_1122_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_nextDeclIdx_1102_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_enodeMap_1103_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_exprs_1104_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_parents_1105_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_congrTable_1106_);
lean_ctor_set(v_reuseFailAlloc_1238_, 5, v_appMap_1107_);
lean_ctor_set(v_reuseFailAlloc_1238_, 6, v_indicesFound_1108_);
lean_ctor_set(v_reuseFailAlloc_1238_, 7, v_toProcess_1109_);
lean_ctor_set(v_reuseFailAlloc_1238_, 8, v_internalizing_1110_);
lean_ctor_set(v_reuseFailAlloc_1238_, 9, v_nextIdx_1112_);
lean_ctor_set(v_reuseFailAlloc_1238_, 10, v_newRawFacts_1113_);
lean_ctor_set(v_reuseFailAlloc_1238_, 11, v_facts_1114_);
lean_ctor_set(v_reuseFailAlloc_1238_, 12, v_extThms_1115_);
lean_ctor_set(v_reuseFailAlloc_1238_, 13, v_ematch_1116_);
lean_ctor_set(v_reuseFailAlloc_1238_, 14, v_inj_1117_);
lean_ctor_set(v_reuseFailAlloc_1238_, 15, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1238_, 16, v_clean_1118_);
lean_ctor_set(v_reuseFailAlloc_1238_, 17, v_sstates_1119_);
lean_ctor_set(v_reuseFailAlloc_1238_, 18, v_goalStack_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*19, v_inconsistent_1111_);
v___x_1137_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1137_);
v___x_1139_ = v___x_1100_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_mvarId_1098_);
v___x_1139_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1140_ = lean_st_ref_put(v_a_1058_, v___x_1139_);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_box(v___x_1086_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1142_);
lean_ctor_set(v___x_1091_, 0, v___x_1087_);
v___x_1144_ = v___x_1091_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1144_);
lean_ctor_set(v___x_1082_, 0, v___x_1141_);
v___x_1146_ = v___x_1082_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1074_, v_lookaheads_1094_, v___x_1146_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_lookaheads_1094_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1226_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1226_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1226_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_fst_1152_; 
v_fst_1152_ = lean_ctor_get(v_a_1148_, 0);
if (lean_obj_tag(v_fst_1152_) == 0)
{
lean_object* v_snd_1153_; lean_object* v_snd_1154_; uint8_t v___x_1155_; 
v_snd_1153_ = lean_ctor_get(v_a_1148_, 1);
lean_inc(v_snd_1153_);
lean_dec(v_a_1148_);
v_snd_1154_ = lean_ctor_get(v_snd_1153_, 1);
v___x_1155_ = lean_unbox(v_snd_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
lean_dec(v_snd_1153_);
v___x_1156_ = lean_box(v___x_1086_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1156_);
v___x_1158_ = v___x_1150_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v_fst_1160_; lean_object* v___x_1161_; lean_object* v_toGoalState_1162_; lean_object* v_split_1163_; lean_object* v_mvarId_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1220_; 
v_fst_1160_ = lean_ctor_get(v_snd_1153_, 0);
lean_inc(v_fst_1160_);
lean_dec(v_snd_1153_);
v___x_1161_ = lean_st_ref_take(v_a_1058_);
v_toGoalState_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_ref(v_toGoalState_1162_);
v_split_1163_ = lean_ctor_get(v_toGoalState_1162_, 15);
lean_inc_ref(v_split_1163_);
v_mvarId_1164_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1221_);
v___x_1166_ = v___x_1161_;
v_isShared_1167_ = v_isSharedCheck_1220_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_mvarId_1164_);
lean_dec(v___x_1161_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1220_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_nextDeclIdx_1168_; lean_object* v_enodeMap_1169_; lean_object* v_exprs_1170_; lean_object* v_parents_1171_; lean_object* v_congrTable_1172_; lean_object* v_appMap_1173_; lean_object* v_indicesFound_1174_; lean_object* v_toProcess_1175_; lean_object* v_internalizing_1176_; uint8_t v_inconsistent_1177_; lean_object* v_nextIdx_1178_; lean_object* v_newRawFacts_1179_; lean_object* v_facts_1180_; lean_object* v_extThms_1181_; lean_object* v_ematch_1182_; lean_object* v_inj_1183_; lean_object* v_clean_1184_; lean_object* v_sstates_1185_; lean_object* v_goalStack_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1218_; 
v_nextDeclIdx_1168_ = lean_ctor_get(v_toGoalState_1162_, 0);
v_enodeMap_1169_ = lean_ctor_get(v_toGoalState_1162_, 1);
v_exprs_1170_ = lean_ctor_get(v_toGoalState_1162_, 2);
v_parents_1171_ = lean_ctor_get(v_toGoalState_1162_, 3);
v_congrTable_1172_ = lean_ctor_get(v_toGoalState_1162_, 4);
v_appMap_1173_ = lean_ctor_get(v_toGoalState_1162_, 5);
v_indicesFound_1174_ = lean_ctor_get(v_toGoalState_1162_, 6);
v_toProcess_1175_ = lean_ctor_get(v_toGoalState_1162_, 7);
v_internalizing_1176_ = lean_ctor_get(v_toGoalState_1162_, 8);
v_inconsistent_1177_ = lean_ctor_get_uint8(v_toGoalState_1162_, sizeof(void*)*19);
v_nextIdx_1178_ = lean_ctor_get(v_toGoalState_1162_, 9);
v_newRawFacts_1179_ = lean_ctor_get(v_toGoalState_1162_, 10);
v_facts_1180_ = lean_ctor_get(v_toGoalState_1162_, 11);
v_extThms_1181_ = lean_ctor_get(v_toGoalState_1162_, 12);
v_ematch_1182_ = lean_ctor_get(v_toGoalState_1162_, 13);
v_inj_1183_ = lean_ctor_get(v_toGoalState_1162_, 14);
v_clean_1184_ = lean_ctor_get(v_toGoalState_1162_, 16);
v_sstates_1185_ = lean_ctor_get(v_toGoalState_1162_, 17);
v_goalStack_1186_ = lean_ctor_get(v_toGoalState_1162_, 18);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_toGoalState_1162_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_toGoalState_1162_, 15);
lean_dec(v_unused_1219_);
v___x_1188_ = v_toGoalState_1162_;
v_isShared_1189_ = v_isSharedCheck_1218_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_goalStack_1186_);
lean_inc(v_sstates_1185_);
lean_inc(v_clean_1184_);
lean_inc(v_inj_1183_);
lean_inc(v_ematch_1182_);
lean_inc(v_extThms_1181_);
lean_inc(v_facts_1180_);
lean_inc(v_newRawFacts_1179_);
lean_inc(v_nextIdx_1178_);
lean_inc(v_internalizing_1176_);
lean_inc(v_toProcess_1175_);
lean_inc(v_indicesFound_1174_);
lean_inc(v_appMap_1173_);
lean_inc(v_congrTable_1172_);
lean_inc(v_parents_1171_);
lean_inc(v_exprs_1170_);
lean_inc(v_enodeMap_1169_);
lean_inc(v_nextDeclIdx_1168_);
lean_dec(v_toGoalState_1162_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1218_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_num_1190_; lean_object* v_candidates_1191_; lean_object* v_added_1192_; lean_object* v_resolved_1193_; lean_object* v_trace_1194_; lean_object* v_lookaheads_1195_; lean_object* v_argPosMap_1196_; lean_object* v_argsAt_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1217_; 
v_num_1190_ = lean_ctor_get(v_split_1163_, 0);
v_candidates_1191_ = lean_ctor_get(v_split_1163_, 1);
v_added_1192_ = lean_ctor_get(v_split_1163_, 2);
v_resolved_1193_ = lean_ctor_get(v_split_1163_, 3);
v_trace_1194_ = lean_ctor_get(v_split_1163_, 4);
v_lookaheads_1195_ = lean_ctor_get(v_split_1163_, 5);
v_argPosMap_1196_ = lean_ctor_get(v_split_1163_, 6);
v_argsAt_1197_ = lean_ctor_get(v_split_1163_, 7);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_split_1163_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1199_ = v_split_1163_;
v_isShared_1200_ = v_isSharedCheck_1217_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_argsAt_1197_);
lean_inc(v_argPosMap_1196_);
lean_inc(v_lookaheads_1195_);
lean_inc(v_trace_1194_);
lean_inc(v_resolved_1193_);
lean_inc(v_added_1192_);
lean_inc(v_candidates_1191_);
lean_inc(v_num_1190_);
lean_dec(v_split_1163_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1217_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = l_List_reverse___redArg(v_fst_1160_);
v___x_1202_ = l_List_appendTR___redArg(v_lookaheads_1195_, v___x_1201_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 5, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_num_1190_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_candidates_1191_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_added_1192_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_resolved_1193_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_trace_1194_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v_argPosMap_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_argsAt_1197_);
v___x_1204_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 15, v___x_1204_);
v___x_1206_ = v___x_1188_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_nextDeclIdx_1168_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_enodeMap_1169_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_exprs_1170_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_parents_1171_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_congrTable_1172_);
lean_ctor_set(v_reuseFailAlloc_1215_, 5, v_appMap_1173_);
lean_ctor_set(v_reuseFailAlloc_1215_, 6, v_indicesFound_1174_);
lean_ctor_set(v_reuseFailAlloc_1215_, 7, v_toProcess_1175_);
lean_ctor_set(v_reuseFailAlloc_1215_, 8, v_internalizing_1176_);
lean_ctor_set(v_reuseFailAlloc_1215_, 9, v_nextIdx_1178_);
lean_ctor_set(v_reuseFailAlloc_1215_, 10, v_newRawFacts_1179_);
lean_ctor_set(v_reuseFailAlloc_1215_, 11, v_facts_1180_);
lean_ctor_set(v_reuseFailAlloc_1215_, 12, v_extThms_1181_);
lean_ctor_set(v_reuseFailAlloc_1215_, 13, v_ematch_1182_);
lean_ctor_set(v_reuseFailAlloc_1215_, 14, v_inj_1183_);
lean_ctor_set(v_reuseFailAlloc_1215_, 15, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1215_, 16, v_clean_1184_);
lean_ctor_set(v_reuseFailAlloc_1215_, 17, v_sstates_1185_);
lean_ctor_set(v_reuseFailAlloc_1215_, 18, v_goalStack_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*19, v_inconsistent_1177_);
v___x_1206_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1206_);
v___x_1208_ = v___x_1166_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_mvarId_1164_);
v___x_1208_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = lean_st_ref_put(v_a_1058_, v___x_1208_);
v___x_1210_ = lean_box(v_lookahead_1074_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1210_);
v___x_1212_ = v___x_1150_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
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
}
}
}
}
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1224_; 
lean_inc_ref(v_fst_1152_);
lean_dec(v_a_1148_);
v_val_1222_ = lean_ctor_get(v_fst_1152_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v_fst_1152_, 1);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_val_1222_);
v___x_1224_ = v___x_1150_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_val_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1147_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1147_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
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
uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_del_object(v___x_1082_);
v___x_1248_ = 0;
v___x_1249_ = lean_box(v___x_1248_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1249_);
v___x_1251_ = v___x_1072_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1069_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1069_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_Grind_lookahead(v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec(v_a_1264_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1276_, lean_object* v_as_1277_, lean_object* v_as_x27_1278_, lean_object* v_b_1279_, lean_object* v_a_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1276_, v_as_x27_1278_, v_b_1279_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1293_, lean_object* v_as_1294_, lean_object* v_as_x27_1295_, lean_object* v_b_1296_, lean_object* v_a_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_33987__boxed_1309_; lean_object* v_res_1310_; 
v___x_33987__boxed_1309_ = lean_unbox(v___x_1293_);
v_res_1310_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_33987__boxed_1309_, v_as_1294_, v_as_x27_1295_, v_b_1296_, v_a_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v_as_x27_1295_);
lean_dec(v_as_1294_);
return v_res_1310_;
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
