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
v___x_228_ = lean_io_error_to_string(v_a_223_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
lean_inc(v_ref_227_);
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
v___x_354_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_345_, v_cache_346_, v___x_353_);
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
lean_dec_ref(v___x_347_);
v___x_366_ = lean_box(0);
v___x_367_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_339_, v_mctx_345_, v_cache_346_, v___x_366_);
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
lean_dec_ref(v___x_433_);
v___x_435_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_426_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
lean_inc_ref(v_e_420_);
v___x_437_ = l_Lean_mkNot(v_e_420_);
v___x_438_ = l_Lean_mkArrow(v___x_437_, v_a_436_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v___x_440_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_439_, v_a_434_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v___x_442_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_420_, v___y_422_);
lean_dec_ref(v_e_420_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v_nextDeclIdx_444_; lean_object* v_enodeMap_445_; lean_object* v_exprs_446_; lean_object* v_parents_447_; lean_object* v_congrTable_448_; lean_object* v_appMap_449_; lean_object* v_indicesFound_450_; uint8_t v_inconsistent_451_; lean_object* v_nextIdx_452_; lean_object* v_newRawFacts_453_; lean_object* v_facts_454_; lean_object* v_extThms_455_; lean_object* v_ematch_456_; lean_object* v_inj_457_; lean_object* v_split_458_; lean_object* v_clean_459_; lean_object* v_sstates_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_498_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v_nextDeclIdx_444_ = lean_ctor_get(v_toGoalState_421_, 0);
v_enodeMap_445_ = lean_ctor_get(v_toGoalState_421_, 1);
v_exprs_446_ = lean_ctor_get(v_toGoalState_421_, 2);
v_parents_447_ = lean_ctor_get(v_toGoalState_421_, 3);
v_congrTable_448_ = lean_ctor_get(v_toGoalState_421_, 4);
v_appMap_449_ = lean_ctor_get(v_toGoalState_421_, 5);
v_indicesFound_450_ = lean_ctor_get(v_toGoalState_421_, 6);
v_inconsistent_451_ = lean_ctor_get_uint8(v_toGoalState_421_, sizeof(void*)*17);
v_nextIdx_452_ = lean_ctor_get(v_toGoalState_421_, 8);
v_newRawFacts_453_ = lean_ctor_get(v_toGoalState_421_, 9);
v_facts_454_ = lean_ctor_get(v_toGoalState_421_, 10);
v_extThms_455_ = lean_ctor_get(v_toGoalState_421_, 11);
v_ematch_456_ = lean_ctor_get(v_toGoalState_421_, 12);
v_inj_457_ = lean_ctor_get(v_toGoalState_421_, 13);
v_split_458_ = lean_ctor_get(v_toGoalState_421_, 14);
v_clean_459_ = lean_ctor_get(v_toGoalState_421_, 15);
v_sstates_460_ = lean_ctor_get(v_toGoalState_421_, 16);
v_isSharedCheck_498_ = !lean_is_exclusive(v_toGoalState_421_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_toGoalState_421_, 7);
lean_dec(v_unused_499_);
v___x_462_ = v_toGoalState_421_;
v_isShared_463_ = v_isSharedCheck_498_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_sstates_460_);
lean_inc(v_clean_459_);
lean_inc(v_split_458_);
lean_inc(v_inj_457_);
lean_inc(v_ematch_456_);
lean_inc(v_extThms_455_);
lean_inc(v_facts_454_);
lean_inc(v_newRawFacts_453_);
lean_inc(v_nextIdx_452_);
lean_inc(v_indicesFound_450_);
lean_inc(v_appMap_449_);
lean_inc(v_congrTable_448_);
lean_inc(v_parents_447_);
lean_inc(v_exprs_446_);
lean_inc(v_enodeMap_445_);
lean_inc(v_nextDeclIdx_444_);
lean_dec(v_toGoalState_421_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_498_;
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
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_nextDeclIdx_444_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_enodeMap_445_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_exprs_446_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_parents_447_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_congrTable_448_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_appMap_449_);
lean_ctor_set(v_reuseFailAlloc_497_, 6, v_indicesFound_450_);
lean_ctor_set(v_reuseFailAlloc_497_, 7, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_497_, 8, v_nextIdx_452_);
lean_ctor_set(v_reuseFailAlloc_497_, 9, v_newRawFacts_453_);
lean_ctor_set(v_reuseFailAlloc_497_, 10, v_facts_454_);
lean_ctor_set(v_reuseFailAlloc_497_, 11, v_extThms_455_);
lean_ctor_set(v_reuseFailAlloc_497_, 12, v_ematch_456_);
lean_ctor_set(v_reuseFailAlloc_497_, 13, v_inj_457_);
lean_ctor_set(v_reuseFailAlloc_497_, 14, v_split_458_);
lean_ctor_set(v_reuseFailAlloc_497_, 15, v_clean_459_);
lean_ctor_set(v_reuseFailAlloc_497_, 16, v_sstates_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*17, v_inconsistent_451_);
v___x_466_ = v_reuseFailAlloc_497_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = l_Lean_Expr_mvarId_x21(v_a_441_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(v___x_468_, v_a_443_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
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
lean_dec_ref(v_a_470_);
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
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_441_);
lean_dec_ref(v_toGoalState_421_);
v_a_500_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_442_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_442_);
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
lean_object* v___x_561_; lean_object* v_env_562_; lean_object* v___x_563_; lean_object* v_mctx_564_; lean_object* v_lctx_565_; lean_object* v_options_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = lean_st_ref_get(v___y_557_);
v_mctx_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_mctx_564_);
lean_dec(v___x_563_);
v_lctx_565_ = lean_ctor_get(v___y_556_, 2);
v_options_566_ = lean_ctor_get(v___y_558_, 2);
lean_inc_ref(v_options_566_);
lean_inc_ref(v_lctx_565_);
v___x_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_567_, 0, v_env_562_);
lean_ctor_set(v___x_567_, 1, v_mctx_564_);
lean_ctor_set(v___x_567_, 2, v_lctx_565_);
lean_ctor_set(v___x_567_, 3, v_options_566_);
v___x_568_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_msgData_555_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(lean_object* v_msgData_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_576_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_577_; double v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_float_of_nat(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(lean_object* v_cls_582_, lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_ref_589_; lean_object* v___x_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_636_; 
v_ref_589_ = lean_ctor_get(v___y_586_, 5);
v___x_590_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_636_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_636_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_636_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_traceState_596_; lean_object* v_env_597_; lean_object* v_nextMacroScope_598_; lean_object* v_ngen_599_; lean_object* v_auxDeclNGen_600_; lean_object* v_cache_601_; lean_object* v_messages_602_; lean_object* v_infoState_603_; lean_object* v_snapshotTasks_604_; lean_object* v_newDecls_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_635_; 
v___x_595_ = lean_st_ref_take(v___y_587_);
v_traceState_596_ = lean_ctor_get(v___x_595_, 4);
v_env_597_ = lean_ctor_get(v___x_595_, 0);
v_nextMacroScope_598_ = lean_ctor_get(v___x_595_, 1);
v_ngen_599_ = lean_ctor_get(v___x_595_, 2);
v_auxDeclNGen_600_ = lean_ctor_get(v___x_595_, 3);
v_cache_601_ = lean_ctor_get(v___x_595_, 5);
v_messages_602_ = lean_ctor_get(v___x_595_, 6);
v_infoState_603_ = lean_ctor_get(v___x_595_, 7);
v_snapshotTasks_604_ = lean_ctor_get(v___x_595_, 8);
v_newDecls_605_ = lean_ctor_get(v___x_595_, 9);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_635_ == 0)
{
v___x_607_ = v___x_595_;
v_isShared_608_ = v_isSharedCheck_635_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_newDecls_605_);
lean_inc(v_snapshotTasks_604_);
lean_inc(v_infoState_603_);
lean_inc(v_messages_602_);
lean_inc(v_cache_601_);
lean_inc(v_traceState_596_);
lean_inc(v_auxDeclNGen_600_);
lean_inc(v_ngen_599_);
lean_inc(v_nextMacroScope_598_);
lean_inc(v_env_597_);
lean_dec(v___x_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_635_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint64_t v_tid_609_; lean_object* v_traces_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_634_; 
v_tid_609_ = lean_ctor_get_uint64(v_traceState_596_, sizeof(void*)*1);
v_traces_610_ = lean_ctor_get(v_traceState_596_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_traceState_596_);
if (v_isSharedCheck_634_ == 0)
{
v___x_612_ = v_traceState_596_;
v_isShared_613_ = v_isSharedCheck_634_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_traces_610_);
lean_dec(v_traceState_596_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_634_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; double v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
v___x_616_ = 0;
v___x_617_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1));
v___x_618_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_618_, 0, v_cls_582_);
lean_ctor_set(v___x_618_, 1, v___x_614_);
lean_ctor_set(v___x_618_, 2, v___x_617_);
lean_ctor_set_float(v___x_618_, sizeof(void*)*3, v___x_615_);
lean_ctor_set_float(v___x_618_, sizeof(void*)*3 + 8, v___x_615_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*3 + 16, v___x_616_);
v___x_619_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2));
v___x_620_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v_a_591_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
lean_inc(v_ref_589_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_ref_589_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_PersistentArray_push___redArg(v_traces_610_, v___x_621_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_622_);
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_622_);
lean_ctor_set_uint64(v_reuseFailAlloc_633_, sizeof(void*)*1, v_tid_609_);
v___x_624_ = v_reuseFailAlloc_633_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v___x_624_);
v___x_626_ = v___x_607_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_env_597_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_nextMacroScope_598_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_ngen_599_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_auxDeclNGen_600_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_cache_601_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_messages_602_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_infoState_603_);
lean_ctor_set(v_reuseFailAlloc_632_, 8, v_snapshotTasks_604_);
lean_ctor_set(v_reuseFailAlloc_632_, 9, v_newDecls_605_);
v___x_626_ = v_reuseFailAlloc_632_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_st_ref_set(v___y_587_, v___x_626_);
v___x_628_ = lean_box(0);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_628_);
v___x_630_ = v___x_593_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(lean_object* v_cls_637_, lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_637_, v_msg_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box(0);
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3));
v___x_654_ = l_Lean_mkConst(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_667_ = l_Lean_Name_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14(void){
_start:
{
lean_object* v_cls_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_cls_673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10));
v___x_675_ = l_Lean_Name_append(v___x_674_, v_cls_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_config_730_; lean_object* v_options_731_; lean_object* v_simp_732_; lean_object* v_simpMethods_733_; lean_object* v_anchorRefs_x3f_734_; uint8_t v_reportMVarIssue_735_; lean_object* v_splitSource_736_; lean_object* v_ematchDiagSource_737_; lean_object* v_symPrios_738_; lean_object* v_extensions_739_; uint8_t v_debug_740_; uint8_t v_ematchDiag_741_; uint8_t v_trace_742_; uint8_t v_markInstances_743_; uint8_t v_lax_744_; uint8_t v_suggestions_745_; uint8_t v_locals_746_; lean_object* v_splits_747_; lean_object* v_ematch_748_; lean_object* v_gen_749_; lean_object* v_genLocal_750_; lean_object* v_instances_751_; uint8_t v_matchEqs_752_; uint8_t v_splitMatch_753_; uint8_t v_splitIte_754_; uint8_t v_splitIndPred_755_; uint8_t v_splitImp_756_; lean_object* v_canonHeartbeats_757_; uint8_t v_ext_758_; uint8_t v_extAll_759_; uint8_t v_etaStruct_760_; uint8_t v_funext_761_; uint8_t v_lookahead_762_; uint8_t v_verbose_763_; uint8_t v_clean_764_; uint8_t v_mbtc_765_; uint8_t v_zetaDelta_766_; uint8_t v_zeta_767_; uint8_t v_ring_768_; lean_object* v_ringSteps_769_; lean_object* v_ringMaxDegree_770_; uint8_t v_linarith_771_; uint8_t v_lia_772_; uint8_t v_ac_773_; lean_object* v_acSteps_774_; lean_object* v_exp_775_; uint8_t v_abstractProof_776_; uint8_t v_inj_777_; uint8_t v_order_778_; lean_object* v_min_779_; lean_object* v_detailed_780_; uint8_t v_useSorry_781_; uint8_t v_revert_782_; uint8_t v_funCC_783_; uint8_t v_reducible_784_; lean_object* v_maxSuggestions_785_; lean_object* v_inheritedTraceOptions_786_; uint8_t v_hasTrace_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___x_842_; 
v_config_730_ = lean_ctor_get(v_a_679_, 2);
v_options_731_ = lean_ctor_get(v_a_685_, 2);
v_simp_732_ = lean_ctor_get(v_a_679_, 0);
v_simpMethods_733_ = lean_ctor_get(v_a_679_, 1);
v_anchorRefs_x3f_734_ = lean_ctor_get(v_a_679_, 3);
v_reportMVarIssue_735_ = lean_ctor_get_uint8(v_a_679_, sizeof(void*)*8 + 1);
v_splitSource_736_ = lean_ctor_get(v_a_679_, 4);
v_ematchDiagSource_737_ = lean_ctor_get(v_a_679_, 5);
v_symPrios_738_ = lean_ctor_get(v_a_679_, 6);
v_extensions_739_ = lean_ctor_get(v_a_679_, 7);
v_debug_740_ = lean_ctor_get_uint8(v_a_679_, sizeof(void*)*8 + 2);
v_ematchDiag_741_ = lean_ctor_get_uint8(v_a_679_, sizeof(void*)*8 + 3);
v_trace_742_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13);
v_markInstances_743_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 1);
v_lax_744_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 2);
v_suggestions_745_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 3);
v_locals_746_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 4);
v_splits_747_ = lean_ctor_get(v_config_730_, 0);
v_ematch_748_ = lean_ctor_get(v_config_730_, 1);
v_gen_749_ = lean_ctor_get(v_config_730_, 2);
v_genLocal_750_ = lean_ctor_get(v_config_730_, 3);
v_instances_751_ = lean_ctor_get(v_config_730_, 4);
v_matchEqs_752_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 5);
v_splitMatch_753_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 6);
v_splitIte_754_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 7);
v_splitIndPred_755_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 8);
v_splitImp_756_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 9);
v_canonHeartbeats_757_ = lean_ctor_get(v_config_730_, 5);
v_ext_758_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 10);
v_extAll_759_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 11);
v_etaStruct_760_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 12);
v_funext_761_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 13);
v_lookahead_762_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 14);
v_verbose_763_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 15);
v_clean_764_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 16);
v_mbtc_765_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 18);
v_zetaDelta_766_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 19);
v_zeta_767_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 20);
v_ring_768_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 21);
v_ringSteps_769_ = lean_ctor_get(v_config_730_, 6);
v_ringMaxDegree_770_ = lean_ctor_get(v_config_730_, 7);
v_linarith_771_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 22);
v_lia_772_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 23);
v_ac_773_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 24);
v_acSteps_774_ = lean_ctor_get(v_config_730_, 8);
v_exp_775_ = lean_ctor_get(v_config_730_, 9);
v_abstractProof_776_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 25);
v_inj_777_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 26);
v_order_778_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 27);
v_min_779_ = lean_ctor_get(v_config_730_, 10);
v_detailed_780_ = lean_ctor_get(v_config_730_, 11);
v_useSorry_781_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 28);
v_revert_782_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 29);
v_funCC_783_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 30);
v_reducible_784_ = lean_ctor_get_uint8(v_config_730_, sizeof(void*)*13 + 31);
v_maxSuggestions_785_ = lean_ctor_get(v_config_730_, 12);
v_inheritedTraceOptions_786_ = lean_ctor_get(v_a_685_, 13);
v_hasTrace_787_ = lean_ctor_get_uint8(v_options_731_, sizeof(void*)*1);
v___x_788_ = 1;
lean_inc(v_maxSuggestions_785_);
lean_inc(v_detailed_780_);
lean_inc(v_min_779_);
lean_inc(v_exp_775_);
lean_inc(v_acSteps_774_);
lean_inc(v_ringMaxDegree_770_);
lean_inc(v_ringSteps_769_);
lean_inc(v_canonHeartbeats_757_);
lean_inc(v_instances_751_);
lean_inc(v_genLocal_750_);
lean_inc(v_gen_749_);
lean_inc(v_ematch_748_);
lean_inc(v_splits_747_);
v___x_789_ = lean_alloc_ctor(0, 13, 32);
lean_ctor_set(v___x_789_, 0, v_splits_747_);
lean_ctor_set(v___x_789_, 1, v_ematch_748_);
lean_ctor_set(v___x_789_, 2, v_gen_749_);
lean_ctor_set(v___x_789_, 3, v_genLocal_750_);
lean_ctor_set(v___x_789_, 4, v_instances_751_);
lean_ctor_set(v___x_789_, 5, v_canonHeartbeats_757_);
lean_ctor_set(v___x_789_, 6, v_ringSteps_769_);
lean_ctor_set(v___x_789_, 7, v_ringMaxDegree_770_);
lean_ctor_set(v___x_789_, 8, v_acSteps_774_);
lean_ctor_set(v___x_789_, 9, v_exp_775_);
lean_ctor_set(v___x_789_, 10, v_min_779_);
lean_ctor_set(v___x_789_, 11, v_detailed_780_);
lean_ctor_set(v___x_789_, 12, v_maxSuggestions_785_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13, v_trace_742_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 1, v_markInstances_743_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 2, v_lax_744_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 3, v_suggestions_745_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 4, v_locals_746_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 5, v_matchEqs_752_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 6, v_splitMatch_753_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 7, v_splitIte_754_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 8, v_splitIndPred_755_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 9, v_splitImp_756_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 10, v_ext_758_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 11, v_extAll_759_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 12, v_etaStruct_760_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 13, v_funext_761_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 14, v_lookahead_762_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 15, v_verbose_763_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 16, v_clean_764_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 17, v___x_788_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 18, v_mbtc_765_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 19, v_zetaDelta_766_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 20, v_zeta_767_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 21, v_ring_768_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 22, v_linarith_771_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 23, v_lia_772_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 24, v_ac_773_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 25, v_abstractProof_776_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 26, v_inj_777_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 27, v_order_778_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 28, v_useSorry_781_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 29, v_revert_782_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 30, v_funCC_783_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*13 + 31, v_reducible_784_);
lean_inc_ref(v_extensions_739_);
lean_inc_ref(v_symPrios_738_);
lean_inc(v_ematchDiagSource_737_);
lean_inc(v_splitSource_736_);
lean_inc(v_anchorRefs_x3f_734_);
lean_inc_ref(v_simpMethods_733_);
lean_inc_ref(v_simp_732_);
v___x_842_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_842_, 0, v_simp_732_);
lean_ctor_set(v___x_842_, 1, v_simpMethods_733_);
lean_ctor_set(v___x_842_, 2, v___x_789_);
lean_ctor_set(v___x_842_, 3, v_anchorRefs_x3f_734_);
lean_ctor_set(v___x_842_, 4, v_splitSource_736_);
lean_ctor_set(v___x_842_, 5, v_ematchDiagSource_737_);
lean_ctor_set(v___x_842_, 6, v_symPrios_738_);
lean_ctor_set(v___x_842_, 7, v_extensions_739_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*8, v___x_788_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*8 + 1, v_reportMVarIssue_735_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*8 + 2, v_debug_740_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*8 + 3, v_ematchDiag_741_);
if (v_hasTrace_787_ == 0)
{
v___y_791_ = v_a_677_;
v___y_792_ = v_a_678_;
v___y_793_ = v___x_842_;
v___y_794_ = v_a_680_;
v___y_795_ = v_a_681_;
v___y_796_ = v_a_682_;
v___y_797_ = v_a_683_;
v___y_798_ = v_a_684_;
v___y_799_ = v_a_685_;
v___y_800_ = v_a_686_;
goto v___jp_790_;
}
else
{
lean_object* v_cls_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_cls_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13));
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
v___x_845_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_786_, v_options_731_, v___x_844_);
if (v___x_845_ == 0)
{
v___y_791_ = v_a_677_;
v___y_792_ = v_a_678_;
v___y_793_ = v___x_842_;
v___y_794_ = v_a_680_;
v___y_795_ = v_a_681_;
v___y_796_ = v_a_682_;
v___y_797_ = v_a_683_;
v___y_798_ = v_a_684_;
v___y_799_ = v_a_685_;
v___y_800_ = v_a_686_;
goto v___jp_790_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_Grind_updateLastTag(v_a_677_, v_a_678_, v___x_842_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___x_846_);
lean_inc_ref(v_e_676_);
v___x_847_ = l_Lean_MessageData_ofExpr(v_e_676_);
v___x_848_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_843_, v___x_847_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_dec_ref(v___x_848_);
v___y_791_ = v_a_677_;
v___y_792_ = v_a_678_;
v___y_793_ = v___x_842_;
v___y_794_ = v_a_680_;
v___y_795_ = v_a_681_;
v___y_796_ = v_a_682_;
v___y_797_ = v_a_683_;
v___y_798_ = v_a_684_;
v___y_799_ = v_a_685_;
v___y_800_ = v_a_686_;
goto v___jp_790_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_842_);
lean_dec_ref(v_e_676_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
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
lean_dec_ref(v___x_842_);
lean_dec_ref(v_e_676_);
v_a_857_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_846_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_846_);
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
v___jp_688_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
lean_inc_ref(v_e_676_);
v___x_701_ = l_Lean_mkAppB(v___x_700_, v_e_676_, v___y_689_);
v___x_702_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_676_, v___x_701_, v___y_690_, v___y_692_, v___y_694_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v___x_702_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
lean_inc(v___y_691_);
lean_inc(v___y_690_);
v___x_703_ = lean_grind_process_new_facts(v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_713_);
v___x_705_ = v___x_703_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_703_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = 1;
v___x_708_ = lean_box(v___x_707_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_708_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_703_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_703_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v___y_692_);
v_a_722_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_702_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_702_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
v___jp_790_:
{
lean_object* v___x_801_; lean_object* v_toGoalState_802_; lean_object* v_mvarId_803_; lean_object* v___f_804_; lean_object* v___x_805_; 
v___x_801_ = lean_st_ref_get(v___y_791_);
v_toGoalState_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_ref(v_toGoalState_802_);
v_mvarId_803_ = lean_ctor_get(v___x_801_, 1);
lean_inc(v_mvarId_803_);
lean_dec(v___x_801_);
lean_inc_ref(v_e_676_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed), 14, 3);
lean_closure_set(v___f_804_, 0, v_mvarId_803_);
lean_closure_set(v___f_804_, 1, v_e_676_);
lean_closure_set(v___f_804_, 2, v_toGoalState_802_);
v___x_805_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_804_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_833_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_833_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_833_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_833_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
if (lean_obj_tag(v_a_806_) == 1)
{
lean_object* v_options_810_; uint8_t v_hasTrace_811_; 
lean_del_object(v___x_808_);
v_options_810_ = lean_ctor_get(v___y_799_, 2);
v_hasTrace_811_ = lean_ctor_get_uint8(v_options_810_, sizeof(void*)*1);
if (v_hasTrace_811_ == 0)
{
lean_object* v_val_812_; 
v_val_812_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v_a_806_);
v___y_689_ = v_val_812_;
v___y_690_ = v___y_791_;
v___y_691_ = v___y_792_;
v___y_692_ = v___y_793_;
v___y_693_ = v___y_794_;
v___y_694_ = v___y_795_;
v___y_695_ = v___y_796_;
v___y_696_ = v___y_797_;
v___y_697_ = v___y_798_;
v___y_698_ = v___y_799_;
v___y_699_ = v___y_800_;
goto v___jp_688_;
}
else
{
lean_object* v_val_813_; lean_object* v_inheritedTraceOptions_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_val_813_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_a_806_);
v_inheritedTraceOptions_814_ = lean_ctor_get(v___y_799_, 13);
v___x_815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8));
v___x_816_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11, &l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
v___x_817_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_814_, v_options_810_, v___x_816_);
if (v___x_817_ == 0)
{
v___y_689_ = v_val_813_;
v___y_690_ = v___y_791_;
v___y_691_ = v___y_792_;
v___y_692_ = v___y_793_;
v___y_693_ = v___y_794_;
v___y_694_ = v___y_795_;
v___y_695_ = v___y_796_;
v___y_696_ = v___y_797_;
v___y_697_ = v___y_798_;
v___y_698_ = v___y_799_;
v___y_699_ = v___y_800_;
goto v___jp_688_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc_ref(v_e_676_);
v___x_818_ = l_Lean_MessageData_ofExpr(v_e_676_);
v___x_819_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_815_, v___x_818_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_dec_ref(v___x_819_);
v___y_689_ = v_val_813_;
v___y_690_ = v___y_791_;
v___y_691_ = v___y_792_;
v___y_692_ = v___y_793_;
v___y_693_ = v___y_794_;
v___y_694_ = v___y_795_;
v___y_695_ = v___y_796_;
v___y_696_ = v___y_797_;
v___y_697_ = v___y_798_;
v___y_698_ = v___y_799_;
v___y_699_ = v___y_800_;
goto v___jp_688_;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_val_813_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_e_676_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
else
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec(v_a_806_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_e_676_);
v___x_828_ = 0;
v___x_829_ = lean_box(v___x_828_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_829_);
v___x_831_ = v___x_808_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v___y_793_);
lean_dec_ref(v_e_676_);
v_a_834_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_805_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_805_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(lean_object* v_e_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v_e_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(lean_object* v_cls_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_878_, v_msg_879_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(lean_object* v_cls_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_892_, v_msg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v___y_894_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(uint8_t v___x_906_, lean_object* v_as_x27_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
if (lean_obj_tag(v_as_x27_907_) == 0)
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v_b_908_);
return v___x_920_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v___x_923_; 
v_head_921_ = lean_ctor_get(v_as_x27_907_, 0);
v_tail_922_ = lean_ctor_get(v_as_x27_907_, 1);
v___x_923_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_909_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_1021_; 
v_snd_924_ = lean_ctor_get(v_b_908_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_b_908_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_b_908_, 0);
lean_dec(v_unused_1022_);
v___x_926_ = v_b_908_;
v_isShared_927_ = v_isSharedCheck_1021_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_dec(v_b_908_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_1021_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_1020_; 
v_a_928_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_930_ = v___x_923_;
v_isShared_931_ = v_isSharedCheck_1020_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_923_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_1020_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
if (v___x_932_ == 0)
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_930_);
v_fst_933_ = lean_ctor_get(v_snd_924_, 0);
v_snd_934_ = lean_ctor_get(v_snd_924_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_snd_924_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_936_ = v_snd_924_;
v_isShared_937_ = v_isSharedCheck_1002_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
lean_dec(v_snd_924_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_1002_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; 
lean_inc(v_head_921_);
v___x_938_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_921_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_938_);
v___x_940_ = lean_box(0);
switch(lean_obj_tag(v_a_939_))
{
case 0:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_snd_934_);
v___x_941_ = lean_box(v___x_906_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_941_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_fst_933_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_948_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_943_);
lean_ctor_set(v___x_926_, 0, v___x_940_);
v___x_945_ = v___x_926_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_as_x27_907_ = v_tail_922_;
v_b_908_ = v___x_945_;
goto _start;
}
}
}
case 1:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_inc(v_head_921_);
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v_head_921_);
lean_ctor_set(v___x_949_, 1, v_fst_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_949_);
v___x_951_ = v___x_936_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_snd_934_);
v___x_951_ = v_reuseFailAlloc_956_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_951_);
lean_ctor_set(v___x_926_, 0, v___x_940_);
v___x_953_ = v___x_926_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_as_x27_907_ = v_tail_922_;
v_b_908_ = v___x_953_;
goto _start;
}
}
}
default: 
{
uint8_t v_tryPostpone_957_; 
v_tryPostpone_957_ = lean_ctor_get_uint8(v_a_939_, sizeof(void*)*1 + 1);
lean_dec_ref(v_a_939_);
if (v_tryPostpone_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_921_);
v___x_959_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_958_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = lean_unbox(v_a_960_);
lean_dec(v_a_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_964_; 
lean_inc(v_head_921_);
v___x_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_962_, 0, v_head_921_);
lean_ctor_set(v___x_962_, 1, v_fst_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_962_);
v___x_964_ = v___x_936_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_934_);
v___x_964_ = v_reuseFailAlloc_969_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_964_);
lean_ctor_set(v___x_926_, 0, v___x_940_);
v___x_966_ = v___x_926_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_968_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
v_as_x27_907_ = v_tail_922_;
v_b_908_ = v___x_966_;
goto _start;
}
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_snd_934_);
v___x_970_ = lean_box(v___x_906_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_970_);
v___x_972_ = v___x_936_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_933_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_977_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_972_);
lean_ctor_set(v___x_926_, 0, v___x_940_);
v___x_974_ = v___x_926_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v_as_x27_907_ = v_tail_922_;
v_b_908_ = v___x_974_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_del_object(v___x_936_);
lean_dec(v_snd_934_);
lean_dec(v_fst_933_);
lean_del_object(v___x_926_);
v_a_978_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_959_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_959_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_988_; 
lean_inc(v_head_921_);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v_head_921_);
lean_ctor_set(v___x_986_, 1, v_fst_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_986_);
v___x_988_ = v___x_936_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_snd_934_);
v___x_988_ = v_reuseFailAlloc_993_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_988_);
lean_ctor_set(v___x_926_, 0, v___x_940_);
v___x_990_ = v___x_926_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v_as_x27_907_ = v_tail_922_;
v_b_908_ = v___x_990_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_del_object(v___x_936_);
lean_dec(v_snd_934_);
lean_dec(v_fst_933_);
lean_del_object(v___x_926_);
v_a_994_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_938_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_938_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_object* v_fst_1003_; lean_object* v_snd_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1019_; 
v_fst_1003_ = lean_ctor_get(v_snd_924_, 0);
v_snd_1004_ = lean_ctor_get(v_snd_924_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_snd_924_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1006_ = v_snd_924_;
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snd_1004_);
lean_inc(v_fst_1003_);
lean_dec(v_snd_924_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1019_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_box(v___x_906_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
if (v_isShared_1007_ == 0)
{
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_fst_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_snd_1004_);
v___x_1011_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_1011_);
lean_ctor_set(v___x_926_, 0, v___x_1009_);
v___x_1013_ = v___x_926_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_1013_);
v___x_1015_ = v___x_930_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
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
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_b_908_);
v_a_1023_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_923_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_923_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(lean_object* v___x_1031_, lean_object* v_as_x27_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_40167__boxed_1045_; lean_object* v_res_1046_; 
v___x_40167__boxed_1045_ = lean_unbox(v___x_1031_);
v_res_1046_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_40167__boxed_1045_, v_as_x27_1032_, v_b_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v_as_x27_1032_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead(lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1049_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1240_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1240_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1240_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v_lookahead_1063_; 
v_lookahead_1063_ = lean_ctor_get_uint8(v_a_1059_, sizeof(void*)*13 + 14);
lean_dec(v_a_1059_);
if (v_lookahead_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_box(v_lookahead_1063_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1068_; lean_object* v_toGoalState_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1238_; 
v___x_1068_ = lean_st_ref_get(v_a_1047_);
v_toGoalState_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1068_, 1);
lean_dec(v_unused_1239_);
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1238_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_toGoalState_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1238_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_split_1073_; lean_object* v_lookaheads_1074_; uint8_t v___x_1075_; 
v_split_1073_ = lean_ctor_get(v_toGoalState_1069_, 14);
lean_inc_ref(v_split_1073_);
lean_dec_ref(v_toGoalState_1069_);
v_lookaheads_1074_ = lean_ctor_get(v_split_1073_, 5);
lean_inc(v_lookaheads_1074_);
lean_dec_ref(v_split_1073_);
v___x_1075_ = l_List_isEmpty___redArg(v_lookaheads_1074_);
lean_dec(v_lookaheads_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_toGoalState_1078_; lean_object* v_split_1079_; lean_object* v_mvarId_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1061_);
v___x_1076_ = lean_st_ref_get(v_a_1047_);
v___x_1077_ = lean_st_ref_take(v_a_1047_);
v_toGoalState_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_toGoalState_1078_);
v_split_1079_ = lean_ctor_get(v_toGoalState_1078_, 14);
lean_inc_ref(v_split_1079_);
v_mvarId_1080_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1077_, 0);
lean_dec(v_unused_1232_);
v___x_1082_ = v___x_1077_;
v_isShared_1083_ = v_isSharedCheck_1231_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_mvarId_1080_);
lean_dec(v___x_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1231_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_nextDeclIdx_1084_; lean_object* v_enodeMap_1085_; lean_object* v_exprs_1086_; lean_object* v_parents_1087_; lean_object* v_congrTable_1088_; lean_object* v_appMap_1089_; lean_object* v_indicesFound_1090_; lean_object* v_newFacts_1091_; uint8_t v_inconsistent_1092_; lean_object* v_nextIdx_1093_; lean_object* v_newRawFacts_1094_; lean_object* v_facts_1095_; lean_object* v_extThms_1096_; lean_object* v_ematch_1097_; lean_object* v_inj_1098_; lean_object* v_clean_1099_; lean_object* v_sstates_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1229_; 
v_nextDeclIdx_1084_ = lean_ctor_get(v_toGoalState_1078_, 0);
v_enodeMap_1085_ = lean_ctor_get(v_toGoalState_1078_, 1);
v_exprs_1086_ = lean_ctor_get(v_toGoalState_1078_, 2);
v_parents_1087_ = lean_ctor_get(v_toGoalState_1078_, 3);
v_congrTable_1088_ = lean_ctor_get(v_toGoalState_1078_, 4);
v_appMap_1089_ = lean_ctor_get(v_toGoalState_1078_, 5);
v_indicesFound_1090_ = lean_ctor_get(v_toGoalState_1078_, 6);
v_newFacts_1091_ = lean_ctor_get(v_toGoalState_1078_, 7);
v_inconsistent_1092_ = lean_ctor_get_uint8(v_toGoalState_1078_, sizeof(void*)*17);
v_nextIdx_1093_ = lean_ctor_get(v_toGoalState_1078_, 8);
v_newRawFacts_1094_ = lean_ctor_get(v_toGoalState_1078_, 9);
v_facts_1095_ = lean_ctor_get(v_toGoalState_1078_, 10);
v_extThms_1096_ = lean_ctor_get(v_toGoalState_1078_, 11);
v_ematch_1097_ = lean_ctor_get(v_toGoalState_1078_, 12);
v_inj_1098_ = lean_ctor_get(v_toGoalState_1078_, 13);
v_clean_1099_ = lean_ctor_get(v_toGoalState_1078_, 15);
v_sstates_1100_ = lean_ctor_get(v_toGoalState_1078_, 16);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_toGoalState_1078_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_toGoalState_1078_, 14);
lean_dec(v_unused_1230_);
v___x_1102_ = v_toGoalState_1078_;
v_isShared_1103_ = v_isSharedCheck_1229_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_sstates_1100_);
lean_inc(v_clean_1099_);
lean_inc(v_inj_1098_);
lean_inc(v_ematch_1097_);
lean_inc(v_extThms_1096_);
lean_inc(v_facts_1095_);
lean_inc(v_newRawFacts_1094_);
lean_inc(v_nextIdx_1093_);
lean_inc(v_newFacts_1091_);
lean_inc(v_indicesFound_1090_);
lean_inc(v_appMap_1089_);
lean_inc(v_congrTable_1088_);
lean_inc(v_parents_1087_);
lean_inc(v_exprs_1086_);
lean_inc(v_enodeMap_1085_);
lean_inc(v_nextDeclIdx_1084_);
lean_dec(v_toGoalState_1078_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1229_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_num_1104_; lean_object* v_candidates_1105_; lean_object* v_added_1106_; lean_object* v_resolved_1107_; lean_object* v_trace_1108_; lean_object* v_argPosMap_1109_; lean_object* v_argsAt_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1227_; 
v_num_1104_ = lean_ctor_get(v_split_1079_, 0);
v_candidates_1105_ = lean_ctor_get(v_split_1079_, 1);
v_added_1106_ = lean_ctor_get(v_split_1079_, 2);
v_resolved_1107_ = lean_ctor_get(v_split_1079_, 3);
v_trace_1108_ = lean_ctor_get(v_split_1079_, 4);
v_argPosMap_1109_ = lean_ctor_get(v_split_1079_, 6);
v_argsAt_1110_ = lean_ctor_get(v_split_1079_, 7);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_split_1079_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v_split_1079_, 5);
lean_dec(v_unused_1228_);
v___x_1112_ = v_split_1079_;
v_isShared_1113_ = v_isSharedCheck_1227_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_argsAt_1110_);
lean_inc(v_argPosMap_1109_);
lean_inc(v_trace_1108_);
lean_inc(v_resolved_1107_);
lean_inc(v_added_1106_);
lean_inc(v_candidates_1105_);
lean_inc(v_num_1104_);
lean_dec(v_split_1079_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1227_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 5, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_num_1104_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_candidates_1105_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_added_1106_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_resolved_1107_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_trace_1108_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_argPosMap_1109_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_argsAt_1110_);
v___x_1116_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 14, v___x_1116_);
v___x_1118_ = v___x_1102_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_nextDeclIdx_1084_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_enodeMap_1085_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_exprs_1086_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_parents_1087_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_congrTable_1088_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v_appMap_1089_);
lean_ctor_set(v_reuseFailAlloc_1225_, 6, v_indicesFound_1090_);
lean_ctor_set(v_reuseFailAlloc_1225_, 7, v_newFacts_1091_);
lean_ctor_set(v_reuseFailAlloc_1225_, 8, v_nextIdx_1093_);
lean_ctor_set(v_reuseFailAlloc_1225_, 9, v_newRawFacts_1094_);
lean_ctor_set(v_reuseFailAlloc_1225_, 10, v_facts_1095_);
lean_ctor_set(v_reuseFailAlloc_1225_, 11, v_extThms_1096_);
lean_ctor_set(v_reuseFailAlloc_1225_, 12, v_ematch_1097_);
lean_ctor_set(v_reuseFailAlloc_1225_, 13, v_inj_1098_);
lean_ctor_set(v_reuseFailAlloc_1225_, 14, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1225_, 15, v_clean_1099_);
lean_ctor_set(v_reuseFailAlloc_1225_, 16, v_sstates_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*17, v_inconsistent_1092_);
v___x_1118_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1118_);
v___x_1120_ = v___x_1082_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_mvarId_1080_);
v___x_1120_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v_toGoalState_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1222_; 
v___x_1121_ = lean_st_ref_set(v_a_1047_, v___x_1120_);
v_toGoalState_1122_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1076_, 1);
lean_dec(v_unused_1223_);
v___x_1124_ = v___x_1076_;
v_isShared_1125_ = v_isSharedCheck_1222_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_toGoalState_1122_);
lean_dec(v___x_1076_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1222_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_split_1126_; lean_object* v_lookaheads_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v_split_1126_ = lean_ctor_get(v_toGoalState_1122_, 14);
lean_inc_ref(v_split_1126_);
lean_dec_ref(v_toGoalState_1122_);
v_lookaheads_1127_ = lean_ctor_get(v_split_1126_, 5);
lean_inc(v_lookaheads_1127_);
lean_dec_ref(v_split_1126_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_box(v___x_1075_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1129_);
lean_ctor_set(v___x_1124_, 0, v___x_1114_);
v___x_1131_ = v___x_1124_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1131_);
lean_ctor_set(v___x_1071_, 0, v___x_1128_);
v___x_1133_ = v___x_1071_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v_lookahead_1063_, v_lookaheads_1127_, v___x_1133_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_lookaheads_1127_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1211_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1211_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1211_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_fst_1139_; 
v_fst_1139_ = lean_ctor_get(v_a_1135_, 0);
if (lean_obj_tag(v_fst_1139_) == 0)
{
lean_object* v_snd_1140_; lean_object* v_snd_1141_; uint8_t v___x_1142_; 
v_snd_1140_ = lean_ctor_get(v_a_1135_, 1);
lean_inc(v_snd_1140_);
lean_dec(v_a_1135_);
v_snd_1141_ = lean_ctor_get(v_snd_1140_, 1);
v___x_1142_ = lean_unbox(v_snd_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_dec(v_snd_1140_);
v___x_1143_ = lean_box(v___x_1075_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1143_);
v___x_1145_ = v___x_1137_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v_fst_1147_; lean_object* v___x_1148_; lean_object* v_toGoalState_1149_; lean_object* v_split_1150_; lean_object* v_mvarId_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1205_; 
v_fst_1147_ = lean_ctor_get(v_snd_1140_, 0);
lean_inc(v_fst_1147_);
lean_dec(v_snd_1140_);
v___x_1148_ = lean_st_ref_take(v_a_1047_);
v_toGoalState_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_toGoalState_1149_);
v_split_1150_ = lean_ctor_get(v_toGoalState_1149_, 14);
lean_inc_ref(v_split_1150_);
v_mvarId_1151_ = lean_ctor_get(v___x_1148_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1148_, 0);
lean_dec(v_unused_1206_);
v___x_1153_ = v___x_1148_;
v_isShared_1154_ = v_isSharedCheck_1205_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_mvarId_1151_);
lean_dec(v___x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1205_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_nextDeclIdx_1155_; lean_object* v_enodeMap_1156_; lean_object* v_exprs_1157_; lean_object* v_parents_1158_; lean_object* v_congrTable_1159_; lean_object* v_appMap_1160_; lean_object* v_indicesFound_1161_; lean_object* v_newFacts_1162_; uint8_t v_inconsistent_1163_; lean_object* v_nextIdx_1164_; lean_object* v_newRawFacts_1165_; lean_object* v_facts_1166_; lean_object* v_extThms_1167_; lean_object* v_ematch_1168_; lean_object* v_inj_1169_; lean_object* v_clean_1170_; lean_object* v_sstates_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1203_; 
v_nextDeclIdx_1155_ = lean_ctor_get(v_toGoalState_1149_, 0);
v_enodeMap_1156_ = lean_ctor_get(v_toGoalState_1149_, 1);
v_exprs_1157_ = lean_ctor_get(v_toGoalState_1149_, 2);
v_parents_1158_ = lean_ctor_get(v_toGoalState_1149_, 3);
v_congrTable_1159_ = lean_ctor_get(v_toGoalState_1149_, 4);
v_appMap_1160_ = lean_ctor_get(v_toGoalState_1149_, 5);
v_indicesFound_1161_ = lean_ctor_get(v_toGoalState_1149_, 6);
v_newFacts_1162_ = lean_ctor_get(v_toGoalState_1149_, 7);
v_inconsistent_1163_ = lean_ctor_get_uint8(v_toGoalState_1149_, sizeof(void*)*17);
v_nextIdx_1164_ = lean_ctor_get(v_toGoalState_1149_, 8);
v_newRawFacts_1165_ = lean_ctor_get(v_toGoalState_1149_, 9);
v_facts_1166_ = lean_ctor_get(v_toGoalState_1149_, 10);
v_extThms_1167_ = lean_ctor_get(v_toGoalState_1149_, 11);
v_ematch_1168_ = lean_ctor_get(v_toGoalState_1149_, 12);
v_inj_1169_ = lean_ctor_get(v_toGoalState_1149_, 13);
v_clean_1170_ = lean_ctor_get(v_toGoalState_1149_, 15);
v_sstates_1171_ = lean_ctor_get(v_toGoalState_1149_, 16);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_toGoalState_1149_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_toGoalState_1149_, 14);
lean_dec(v_unused_1204_);
v___x_1173_ = v_toGoalState_1149_;
v_isShared_1174_ = v_isSharedCheck_1203_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_sstates_1171_);
lean_inc(v_clean_1170_);
lean_inc(v_inj_1169_);
lean_inc(v_ematch_1168_);
lean_inc(v_extThms_1167_);
lean_inc(v_facts_1166_);
lean_inc(v_newRawFacts_1165_);
lean_inc(v_nextIdx_1164_);
lean_inc(v_newFacts_1162_);
lean_inc(v_indicesFound_1161_);
lean_inc(v_appMap_1160_);
lean_inc(v_congrTable_1159_);
lean_inc(v_parents_1158_);
lean_inc(v_exprs_1157_);
lean_inc(v_enodeMap_1156_);
lean_inc(v_nextDeclIdx_1155_);
lean_dec(v_toGoalState_1149_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1203_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_num_1175_; lean_object* v_candidates_1176_; lean_object* v_added_1177_; lean_object* v_resolved_1178_; lean_object* v_trace_1179_; lean_object* v_lookaheads_1180_; lean_object* v_argPosMap_1181_; lean_object* v_argsAt_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1202_; 
v_num_1175_ = lean_ctor_get(v_split_1150_, 0);
v_candidates_1176_ = lean_ctor_get(v_split_1150_, 1);
v_added_1177_ = lean_ctor_get(v_split_1150_, 2);
v_resolved_1178_ = lean_ctor_get(v_split_1150_, 3);
v_trace_1179_ = lean_ctor_get(v_split_1150_, 4);
v_lookaheads_1180_ = lean_ctor_get(v_split_1150_, 5);
v_argPosMap_1181_ = lean_ctor_get(v_split_1150_, 6);
v_argsAt_1182_ = lean_ctor_get(v_split_1150_, 7);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_split_1150_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1184_ = v_split_1150_;
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_argsAt_1182_);
lean_inc(v_argPosMap_1181_);
lean_inc(v_lookaheads_1180_);
lean_inc(v_trace_1179_);
lean_inc(v_resolved_1178_);
lean_inc(v_added_1177_);
lean_inc(v_candidates_1176_);
lean_inc(v_num_1175_);
lean_dec(v_split_1150_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = l_List_reverse___redArg(v_fst_1147_);
v___x_1187_ = l_List_appendTR___redArg(v_lookaheads_1180_, v___x_1186_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 5, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_num_1175_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_candidates_1176_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_added_1177_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_resolved_1178_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_trace_1179_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1201_, 6, v_argPosMap_1181_);
lean_ctor_set(v_reuseFailAlloc_1201_, 7, v_argsAt_1182_);
v___x_1189_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 14, v___x_1189_);
v___x_1191_ = v___x_1173_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_nextDeclIdx_1155_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_enodeMap_1156_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_exprs_1157_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_parents_1158_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_congrTable_1159_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_appMap_1160_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_indicesFound_1161_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_newFacts_1162_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_nextIdx_1164_);
lean_ctor_set(v_reuseFailAlloc_1200_, 9, v_newRawFacts_1165_);
lean_ctor_set(v_reuseFailAlloc_1200_, 10, v_facts_1166_);
lean_ctor_set(v_reuseFailAlloc_1200_, 11, v_extThms_1167_);
lean_ctor_set(v_reuseFailAlloc_1200_, 12, v_ematch_1168_);
lean_ctor_set(v_reuseFailAlloc_1200_, 13, v_inj_1169_);
lean_ctor_set(v_reuseFailAlloc_1200_, 14, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 15, v_clean_1170_);
lean_ctor_set(v_reuseFailAlloc_1200_, 16, v_sstates_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*17, v_inconsistent_1163_);
v___x_1191_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1191_);
v___x_1193_ = v___x_1153_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_mvarId_1151_);
v___x_1193_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_st_ref_set(v_a_1047_, v___x_1193_);
v___x_1195_ = lean_box(v_lookahead_1063_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1195_);
v___x_1197_ = v___x_1137_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
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
lean_object* v_val_1207_; lean_object* v___x_1209_; 
lean_inc_ref(v_fst_1139_);
lean_dec(v_a_1135_);
v_val_1207_ = lean_ctor_get(v_fst_1139_, 0);
lean_inc(v_val_1207_);
lean_dec_ref(v_fst_1139_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_val_1207_);
v___x_1209_ = v___x_1137_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_val_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1134_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1134_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
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
}
}
}
}
else
{
uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_del_object(v___x_1071_);
v___x_1233_ = 0;
v___x_1234_ = lean_box(v___x_1233_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1234_);
v___x_1236_ = v___x_1061_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1058_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1058_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookahead___boxed(lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_Grind_lookahead(v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec(v_a_1249_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(uint8_t v___x_1261_, lean_object* v_as_1262_, lean_object* v_as_x27_1263_, lean_object* v_b_1264_, lean_object* v_a_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(v___x_1261_, v_as_x27_1263_, v_b_1264_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(lean_object* v___x_1278_, lean_object* v_as_1279_, lean_object* v_as_x27_1280_, lean_object* v_b_1281_, lean_object* v_a_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v___x_40668__boxed_1294_; lean_object* v_res_1295_; 
v___x_40668__boxed_1294_ = lean_unbox(v___x_1278_);
v_res_1295_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(v___x_40668__boxed_1294_, v_as_1279_, v_as_x27_1280_, v_b_1281_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v_as_x27_1280_);
lean_dec(v_as_1279_);
return v_res_1295_;
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
