// Lean compiler output
// Module: Lake.Util.EStateT
// Imports: public import Init.Control.State
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
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_state(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_state___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_setState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_setState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toProd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EResult_instFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_instFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_EResult_instFunctor___redArg___closed__0 = (const lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__0_value;
static const lean_closure_object l_Lake_EResult_instFunctor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_instFunctor___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__0_value)} };
static const lean_object* l_Lake_EResult_instFunctor___redArg___closed__1 = (const lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__1_value;
static const lean_ctor_object l_Lake_EResult_instFunctor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__0_value),((lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__1_value)}};
static const lean_object* l_Lake_EResult_instFunctor___redArg___closed__2 = (const lean_object*)&l_Lake_EResult_instFunctor___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg();
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_EResult_instFunctor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_EResult_instFunctor___closed__0;
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_mk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EStateT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toExcept___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_EStateT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_EStateT_run_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EStateT_toStateT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toProd, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_EStateT_toStateT___redArg___closed__0 = (const lean_object*)&l_Lake_EStateT_toStateT___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toProd_x3f, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_EStateT_toStateT_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_result_x3f___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_EStateT_run_x3f_x27___redArg___closed__0 = (const lean_object*)&l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_pure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_set___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_throw___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_throw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_EResult_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl(lean_object* v_00_u03b5_5_, lean_object* v_00_u03c3_6_, lean_object* v_00_u03b1_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_tag_nat(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___impl___boxed(lean_object* v_00_u03b5_10_, lean_object* v_00_u03c3_11_, lean_object* v_00_u03b1_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lake_EResult_ctorIdx___impl(v_00_u03b5_10_, v_00_u03c3_11_, v_00_u03b1_12_, v_x_13_);
lean_dec_ref(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_17_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_a_17_);
v_a_18_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_a_18_);
lean_dec_ref(v_t_15_);
v___x_19_ = lean_apply_2(v_k_16_, v_a_17_, v_a_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim(lean_object* v_00_u03b5_20_, lean_object* v_00_u03c3_21_, lean_object* v_00_u03b1_22_, lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lake_EResult_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___boxed(lean_object* v_00_u03b5_29_, lean_object* v_00_u03c3_30_, lean_object* v_00_u03b1_31_, lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_EResult_ctorElim(v_00_u03b5_29_, v_00_u03c3_30_, v_00_u03b1_31_, v_motive_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim___redArg(lean_object* v_t_38_, lean_object* v_ok_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lake_EResult_ctorElim___redArg(v_t_38_, v_ok_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim(lean_object* v_00_u03b5_41_, lean_object* v_00_u03c3_42_, lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_ok_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lake_EResult_ctorElim___redArg(v_t_45_, v_ok_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim___redArg(lean_object* v_t_49_, lean_object* v_error_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lake_EResult_ctorElim___redArg(v_t_49_, v_error_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim(lean_object* v_00_u03b5_52_, lean_object* v_00_u03c3_53_, lean_object* v_00_u03b1_54_, lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_error_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lake_EResult_ctorElim___redArg(v_t_56_, v_error_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_inst_60_);
lean_ctor_set(v___x_62_, 1, v_inst_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited(lean_object* v_00_u03b1_63_, lean_object* v_00_u03c3_64_, lean_object* v_00_u03b5_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_inst_66_);
lean_ctor_set(v___x_68_, 1, v_inst_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_71_, 0, v_inst_69_);
lean_ctor_set(v___x_71_, 1, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1(lean_object* v_00_u03b5_72_, lean_object* v_00_u03c3_73_, lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_inst_75_);
lean_ctor_set(v___x_77_, 1, v_inst_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg(lean_object* v_x_78_){
_start:
{
lean_object* v_a_79_; 
v_a_79_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_a_79_);
return v_a_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg___boxed(lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lake_EResult_state___redArg(v_x_80_);
lean_dec_ref(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state(lean_object* v_00_u03b5_82_, lean_object* v_00_u03c3_83_, lean_object* v_00_u03b1_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_a_86_; 
v_a_86_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_a_86_);
return v_a_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___boxed(lean_object* v_00_u03b5_87_, lean_object* v_00_u03c3_88_, lean_object* v_00_u03b1_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lake_EResult_state(v_00_u03b5_87_, v_00_u03c3_88_, v_00_u03b1_89_, v_x_90_);
lean_dec_ref(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState___redArg(lean_object* v_f_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
v_a_94_ = lean_ctor_get(v_x_93_, 0);
v_a_95_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v_x_93_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_inc(v_a_94_);
lean_dec(v_x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_apply_1(v_f_92_, v_a_95_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_99_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
v_a_104_ = lean_ctor_get(v_x_93_, 0);
v_a_105_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v_x_93_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_inc(v_a_104_);
lean_dec(v_x_93_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_apply_1(v_f_92_, v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_104_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState(lean_object* v_00_u03c3_114_, lean_object* v_00_u03c3_x27_115_, lean_object* v_00_u03b5_116_, lean_object* v_00_u03b1_117_, lean_object* v_f_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_a_120_ = lean_ctor_get(v_x_119_, 0);
v_a_121_ = lean_ctor_get(v_x_119_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v_x_119_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_inc(v_a_120_);
lean_dec(v_x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_apply_1(v_f_118_, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_120_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_a_130_ = lean_ctor_get(v_x_119_, 0);
v_a_131_ = lean_ctor_get(v_x_119_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v_x_119_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_inc(v_a_130_);
lean_dec(v_x_119_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_apply_1(v_f_118_, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_130_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_setState___redArg(lean_object* v_s_140_, lean_object* v_r_141_){
_start:
{
if (lean_obj_tag(v_r_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v_r_141_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_r_141_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_r_141_, 1);
lean_dec(v_unused_150_);
v___x_144_ = v_r_141_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v_r_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v_s_140_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_s_140_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v_r_141_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_r_141_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_r_141_, 1);
lean_dec(v_unused_159_);
v___x_153_ = v_r_141_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v_r_141_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_s_140_);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_s_140_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_setState(lean_object* v_00_u03c3_x27_160_, lean_object* v_00_u03b5_161_, lean_object* v_00_u03c3_162_, lean_object* v_00_u03b1_163_, lean_object* v_s_164_, lean_object* v_r_165_){
_start:
{
if (lean_obj_tag(v_r_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v_r_165_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_r_165_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_r_165_, 1);
lean_dec(v_unused_174_);
v___x_168_ = v_r_165_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v_r_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v_s_164_);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_s_164_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v_r_165_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_r_165_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_r_165_, 1);
lean_dec(v_unused_183_);
v___x_177_ = v_r_165_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v_r_165_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_s_164_);
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_s_164_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd___redArg(lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_a_185_ = lean_ctor_get(v_x_184_, 0);
v_a_186_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v_x_184_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_inc(v_a_185_);
lean_dec(v_x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_a_185_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_a_186_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_a_195_ = lean_ctor_get(v_x_184_, 0);
v_a_196_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v_x_184_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_inc(v_a_195_);
lean_dec(v_x_184_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v_a_195_);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 0);
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_a_196_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd(lean_object* v_00_u03b5_205_, lean_object* v_00_u03c3_206_, lean_object* v_00_u03b1_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_a_209_ = lean_ctor_get(v_x_208_, 0);
v_a_210_ = lean_ctor_get(v_x_208_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v_x_208_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_inc(v_a_209_);
lean_dec(v_x_208_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_a_209_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_a_210_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_a_219_ = lean_ctor_get(v_x_208_, 0);
v_a_220_ = lean_ctor_get(v_x_208_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v_x_208_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_inc(v_a_219_);
lean_dec(v_x_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_a_219_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 0);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_220_);
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
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f___redArg(lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_a_230_ = lean_ctor_get(v_x_229_, 0);
v_a_231_ = lean_ctor_get(v_x_229_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v_x_229_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_inc(v_a_230_);
lean_dec(v_x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_a_230_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_231_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_a_240_ = lean_ctor_get(v_x_229_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_x_229_, 0);
lean_dec(v_unused_249_);
v___x_242_ = v_x_229_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v_x_229_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_box(0);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_a_240_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f(lean_object* v_00_u03b5_250_, lean_object* v_00_u03c3_251_, lean_object* v_00_u03b1_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_a_254_ = lean_ctor_get(v_x_253_, 0);
v_a_255_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v_x_253_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_inc(v_a_254_);
lean_dec(v_x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_254_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_255_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_a_264_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_x_253_, 0);
lean_dec(v_unused_273_);
v___x_266_ = v_x_253_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v_x_253_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 0);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_a_264_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg(lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_ctor_get(v_x_274_, 0);
lean_inc(v_a_275_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_a_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg___boxed(lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lake_EResult_result_x3f___redArg(v_x_278_);
lean_dec_ref(v_x_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f(lean_object* v_00_u03b5_280_, lean_object* v_00_u03c3_281_, lean_object* v_00_u03b1_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_a_284_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_a_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___boxed(lean_object* v_00_u03b5_287_, lean_object* v_00_u03c3_288_, lean_object* v_00_u03b1_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lake_EResult_result_x3f(v_00_u03b5_287_, v_00_u03c3_288_, v_00_u03b1_289_, v_x_290_);
lean_dec_ref(v_x_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg(lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
return v___x_293_;
}
else
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_a_294_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_a_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lake_EResult_error_x3f___redArg(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f(lean_object* v_00_u03b5_298_, lean_object* v_00_u03c3_299_, lean_object* v_00_u03b1_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_a_303_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_a_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___boxed(lean_object* v_00_u03b5_305_, lean_object* v_00_u03c3_306_, lean_object* v_00_u03b1_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lake_EResult_error_x3f(v_00_u03b5_305_, v_00_u03c3_306_, v_00_u03b1_307_, v_x_308_);
lean_dec_ref(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg(lean_object* v_x_310_){
_start:
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_a_311_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_a_311_);
return v___x_312_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_314_; 
v_a_313_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_a_313_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_a_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg___boxed(lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lake_EResult_toExcept___redArg(v_x_315_);
lean_dec_ref(v_x_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept(lean_object* v_00_u03b5_317_, lean_object* v_00_u03c3_318_, lean_object* v_00_u03b1_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_a_321_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_a_321_);
return v___x_322_;
}
else
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_a_323_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_a_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___boxed(lean_object* v_00_u03b5_325_, lean_object* v_00_u03c3_326_, lean_object* v_00_u03b1_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lake_EResult_toExcept(v_00_u03b5_325_, v_00_u03c3_326_, v_00_u03b1_327_, v_x_328_);
lean_dec_ref(v_x_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_map___redArg(lean_object* v_f_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_a_332_ = lean_ctor_get(v_x_331_, 0);
v_a_333_ = lean_ctor_get(v_x_331_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v_x_331_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_inc(v_a_332_);
lean_dec(v_x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_apply_1(v_f_330_, v_a_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_333_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v_a_342_; lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_f_330_);
v_a_342_ = lean_ctor_get(v_x_331_, 0);
v_a_343_ = lean_ctor_get(v_x_331_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v_x_331_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_inc(v_a_342_);
lean_dec(v_x_331_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_342_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_map(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_00_u03b5_353_, lean_object* v_00_u03c3_354_, lean_object* v_f_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_a_357_ = lean_ctor_get(v_x_356_, 0);
v_a_358_ = lean_ctor_get(v_x_356_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v_x_356_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_inc(v_a_357_);
lean_dec(v_x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_apply_1(v_f_355_, v_a_357_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_358_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_f_355_);
v_a_367_ = lean_ctor_get(v_x_356_, 0);
v_a_368_ = lean_ctor_get(v_x_356_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v_x_356_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_inc(v_a_367_);
lean_dec(v_x_356_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__0(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
if (lean_obj_tag(v___y_379_) == 0)
{
lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_a_380_ = lean_ctor_get(v___y_379_, 0);
v_a_381_ = lean_ctor_get(v___y_379_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___y_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v___y_379_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___y_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_apply_1(v___y_378_, v_a_380_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_381_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v___y_378_);
v_a_390_ = lean_ctor_get(v___y_379_, 0);
v_a_391_ = lean_ctor_get(v___y_379_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___y_379_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___y_379_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v___y_379_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__1(lean_object* v___f_399_, lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_404_, 0, lean_box(0));
lean_closure_set(v___x_404_, 1, lean_box(0));
lean_closure_set(v___x_404_, 2, v___y_402_);
v___x_405_ = lean_apply_4(v___f_399_, lean_box(0), lean_box(0), v___x_404_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg(){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Lake_EResult_instFunctor___redArg___closed__2));
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___boxed(lean_object* v___dummy_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_EResult_instFunctor___redArg();
return v_res_415_;
}
}
static lean_object* _init_l_Lake_EResult_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lake_EResult_instFunctor___redArg();
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor(lean_object* v_00_u03b5_417_, lean_object* v_00_u03c3_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_obj_once(&l_Lake_EResult_instFunctor___closed__0, &l_Lake_EResult_instFunctor___closed__0_once, _init_l_Lake_EResult_instFunctor___closed__0);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult___redArg(lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v_x_420_, 0);
v_a_422_ = lean_ctor_get(v_x_420_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v_x_420_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v_x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_421_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_430_ = lean_ctor_get(v_x_420_, 0);
v_a_431_ = lean_ctor_get(v_x_420_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v_x_420_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_inc(v_a_430_);
lean_dec(v_x_420_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult(lean_object* v_00_u03b5_439_, lean_object* v_00_u03c3_440_, lean_object* v_00_u03b1_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lake_EResult_toEStateMResult___redArg(v_x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult___redArg(lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_445_ = lean_ctor_get(v_x_444_, 0);
v_a_446_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v_x_444_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_inc(v_a_445_);
lean_dec(v_x_444_);
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
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_445_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_454_ = lean_ctor_get(v_x_444_, 0);
v_a_455_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v_x_444_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_inc(v_a_454_);
lean_dec(v_x_444_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_454_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult(lean_object* v_00_u03b5_463_, lean_object* v_00_u03c3_464_, lean_object* v_00_u03b1_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk___redArg(lean_object* v_x_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_apply_1(v_x_468_, v_a_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk(lean_object* v_00_u03b5_471_, lean_object* v_00_u03c3_472_, lean_object* v_00_u03b1_473_, lean_object* v_m_474_, lean_object* v_x_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_apply_1(v_x_475_, v_a_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_s_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v_inst_478_);
lean_ctor_set(v___x_481_, 1, v_s_480_);
v___x_482_ = lean_apply_2(v_inst_479_, lean_box(0), v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(lean_object* v_inst_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v___f_485_; 
v___f_485_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_485_, 0, v_inst_483_);
lean_closure_set(v___f_485_, 1, v_inst_484_);
return v___f_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(lean_object* v_00_u03b5_486_, lean_object* v_00_u03c3_487_, lean_object* v_00_u03b1_488_, lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v___f_492_; 
v___f_492_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_492_, 0, v_inst_490_);
lean_closure_set(v___f_492_, 1, v_inst_491_);
return v___f_492_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run___redArg(lean_object* v_init_493_, lean_object* v_self_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_apply_1(v_self_494_, v_init_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run(lean_object* v_00_u03b5_496_, lean_object* v_00_u03c3_497_, lean_object* v_00_u03b1_498_, lean_object* v_m_499_, lean_object* v_init_500_, lean_object* v_self_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_apply_1(v_self_501_, v_init_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27___redArg(lean_object* v_inst_504_, lean_object* v_init_505_, lean_object* v_x_506_){
_start:
{
lean_object* v_map_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_map_507_ = lean_ctor_get(v_inst_504_, 0);
lean_inc(v_map_507_);
lean_dec_ref(v_inst_504_);
v___x_508_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_509_ = lean_apply_1(v_x_506_, v_init_505_);
v___x_510_ = lean_apply_4(v_map_507_, lean_box(0), lean_box(0), v___x_508_, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27(lean_object* v_00_u03b5_511_, lean_object* v_00_u03b1_512_, lean_object* v_m_513_, lean_object* v_00_u03c3_514_, lean_object* v_inst_515_, lean_object* v_init_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_map_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_map_518_ = lean_ctor_get(v_inst_515_, 0);
lean_inc(v_map_518_);
lean_dec_ref(v_inst_515_);
v___x_519_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_520_ = lean_apply_1(v_x_517_, v_init_516_);
v___x_521_ = lean_apply_4(v_map_518_, lean_box(0), lean_box(0), v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT___redArg(lean_object* v_inst_523_, lean_object* v_x_524_, lean_object* v_s_525_){
_start:
{
lean_object* v_map_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_map_526_ = lean_ctor_get(v_inst_523_, 0);
lean_inc(v_map_526_);
lean_dec_ref(v_inst_523_);
v___x_527_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_528_ = lean_apply_1(v_x_524_, v_s_525_);
v___x_529_ = lean_apply_4(v_map_526_, lean_box(0), lean_box(0), v___x_527_, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT(lean_object* v_m_530_, lean_object* v_00_u03b5_531_, lean_object* v_00_u03c3_532_, lean_object* v_00_u03b1_533_, lean_object* v_inst_534_, lean_object* v_x_535_, lean_object* v_s_536_){
_start:
{
lean_object* v_map_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_map_537_ = lean_ctor_get(v_inst_534_, 0);
lean_inc(v_map_537_);
lean_dec_ref(v_inst_534_);
v___x_538_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_539_ = lean_apply_1(v_x_535_, v_s_536_);
v___x_540_ = lean_apply_4(v_map_537_, lean_box(0), lean_box(0), v___x_538_, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f___redArg(lean_object* v_inst_542_, lean_object* v_x_543_, lean_object* v_s_544_){
_start:
{
lean_object* v_map_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_map_545_ = lean_ctor_get(v_inst_542_, 0);
lean_inc(v_map_545_);
lean_dec_ref(v_inst_542_);
v___x_546_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_547_ = lean_apply_1(v_x_543_, v_s_544_);
v___x_548_ = lean_apply_4(v_map_545_, lean_box(0), lean_box(0), v___x_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f(lean_object* v_m_549_, lean_object* v_00_u03b5_550_, lean_object* v_00_u03c3_551_, lean_object* v_00_u03b1_552_, lean_object* v_inst_553_, lean_object* v_x_554_, lean_object* v_s_555_){
_start:
{
lean_object* v_map_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_map_556_ = lean_ctor_get(v_inst_553_, 0);
lean_inc(v_map_556_);
lean_dec_ref(v_inst_553_);
v___x_557_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_558_ = lean_apply_1(v_x_554_, v_s_555_);
v___x_559_ = lean_apply_4(v_map_556_, lean_box(0), lean_box(0), v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f___redArg(lean_object* v_inst_560_, lean_object* v_init_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_map_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_map_563_ = lean_ctor_get(v_inst_560_, 0);
lean_inc(v_map_563_);
lean_dec_ref(v_inst_560_);
v___x_564_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_565_ = lean_apply_1(v_x_562_, v_init_561_);
v___x_566_ = lean_apply_4(v_map_563_, lean_box(0), lean_box(0), v___x_564_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f(lean_object* v_00_u03c3_567_, lean_object* v_00_u03b1_568_, lean_object* v_m_569_, lean_object* v_00_u03b5_570_, lean_object* v_inst_571_, lean_object* v_init_572_, lean_object* v_x_573_){
_start:
{
lean_object* v_map_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_map_574_ = lean_ctor_get(v_inst_571_, 0);
lean_inc(v_map_574_);
lean_dec_ref(v_inst_571_);
v___x_575_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_576_ = lean_apply_1(v_x_573_, v_init_572_);
v___x_577_ = lean_apply_4(v_map_574_, lean_box(0), lean_box(0), v___x_575_, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27___redArg(lean_object* v_inst_579_, lean_object* v_init_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_map_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_map_582_ = lean_ctor_get(v_inst_579_, 0);
lean_inc(v_map_582_);
lean_dec_ref(v_inst_579_);
v___x_583_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_584_ = lean_apply_1(v_x_581_, v_init_580_);
v___x_585_ = lean_apply_4(v_map_582_, lean_box(0), lean_box(0), v___x_583_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27(lean_object* v_m_586_, lean_object* v_00_u03b5_587_, lean_object* v_00_u03c3_588_, lean_object* v_00_u03b1_589_, lean_object* v_inst_590_, lean_object* v_init_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_map_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_map_593_ = lean_ctor_get(v_inst_590_, 0);
lean_inc(v_map_593_);
lean_dec_ref(v_inst_590_);
v___x_594_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_595_ = lean_apply_1(v_x_592_, v_init_591_);
v___x_596_ = lean_apply_4(v_map_593_, lean_box(0), lean_box(0), v___x_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg___lam__0(lean_object* v_toPure_597_, lean_object* v_h_598_, lean_object* v_____do__lift_599_){
_start:
{
if (lean_obj_tag(v_____do__lift_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_h_598_);
v_a_600_ = lean_ctor_get(v_____do__lift_599_, 0);
v_a_601_ = lean_ctor_get(v_____do__lift_599_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_____do__lift_599_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_____do__lift_599_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_inc(v_a_600_);
lean_dec(v_____do__lift_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_601_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_606_);
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_612_; 
lean_dec(v_toPure_597_);
v_a_610_ = lean_ctor_get(v_____do__lift_599_, 0);
lean_inc(v_a_610_);
v_a_611_ = lean_ctor_get(v_____do__lift_599_, 1);
lean_inc(v_a_611_);
lean_dec_ref_known(v_____do__lift_599_, 2);
v___x_612_ = lean_apply_2(v_h_598_, v_a_610_, v_a_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg(lean_object* v_inst_613_, lean_object* v_x_614_, lean_object* v_h_615_, lean_object* v_s_616_){
_start:
{
lean_object* v_toApplicative_617_; lean_object* v_toBind_618_; lean_object* v_toPure_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; 
v_toApplicative_617_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_ref(v_toApplicative_617_);
v_toBind_618_ = lean_ctor_get(v_inst_613_, 1);
lean_inc(v_toBind_618_);
lean_dec_ref(v_inst_613_);
v_toPure_619_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_inc(v_toPure_619_);
lean_dec_ref(v_toApplicative_617_);
v___x_620_ = lean_apply_1(v_x_614_, v_s_616_);
v___f_621_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_621_, 0, v_toPure_619_);
lean_closure_set(v___f_621_, 1, v_h_615_);
v___x_622_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_620_, v___f_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions(lean_object* v_m_623_, lean_object* v_00_u03b5_624_, lean_object* v_00_u03c3_625_, lean_object* v_00_u03b1_626_, lean_object* v_inst_627_, lean_object* v_x_628_, lean_object* v_h_629_, lean_object* v_s_630_){
_start:
{
lean_object* v_toApplicative_631_; lean_object* v_toBind_632_; lean_object* v_toPure_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v_toApplicative_631_ = lean_ctor_get(v_inst_627_, 0);
lean_inc_ref(v_toApplicative_631_);
v_toBind_632_ = lean_ctor_get(v_inst_627_, 1);
lean_inc(v_toBind_632_);
lean_dec_ref(v_inst_627_);
v_toPure_633_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_inc(v_toPure_633_);
lean_dec_ref(v_toApplicative_631_);
v___x_634_ = lean_apply_1(v_x_628_, v_s_630_);
v___f_635_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_635_, 0, v_toPure_633_);
lean_closure_set(v___f_635_, 1, v_h_629_);
v___x_636_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_634_, v___f_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg___lam__0(lean_object* v_s_637_, lean_object* v_toPure_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_a_639_);
lean_ctor_set(v___x_640_, 1, v_s_637_);
v___x_641_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg(lean_object* v_inst_642_, lean_object* v_x_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_toApplicative_645_; lean_object* v_toBind_646_; lean_object* v_toPure_647_; lean_object* v___f_648_; lean_object* v___x_649_; 
v_toApplicative_645_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_645_);
v_toBind_646_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_toBind_646_);
lean_dec_ref(v_inst_642_);
v_toPure_647_ = lean_ctor_get(v_toApplicative_645_, 1);
lean_inc(v_toPure_647_);
lean_dec_ref(v_toApplicative_645_);
v___f_648_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_648_, 0, v_s_644_);
lean_closure_set(v___f_648_, 1, v_toPure_647_);
v___x_649_ = lean_apply_4(v_toBind_646_, lean_box(0), lean_box(0), v_x_643_, v___f_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift(lean_object* v_m_650_, lean_object* v_00_u03b5_651_, lean_object* v_00_u03c3_652_, lean_object* v_00_u03b1_653_, lean_object* v_inst_654_, lean_object* v_x_655_, lean_object* v_s_656_){
_start:
{
lean_object* v_toApplicative_657_; lean_object* v_toBind_658_; lean_object* v_toPure_659_; lean_object* v___f_660_; lean_object* v___x_661_; 
v_toApplicative_657_ = lean_ctor_get(v_inst_654_, 0);
lean_inc_ref(v_toApplicative_657_);
v_toBind_658_ = lean_ctor_get(v_inst_654_, 1);
lean_inc(v_toBind_658_);
lean_dec_ref(v_inst_654_);
v_toPure_659_ = lean_ctor_get(v_toApplicative_657_, 1);
lean_inc(v_toPure_659_);
lean_dec_ref(v_toApplicative_657_);
v___f_660_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_660_, 0, v_s_656_);
lean_closure_set(v___f_660_, 1, v_toPure_659_);
v___x_661_ = lean_apply_4(v_toBind_658_, lean_box(0), lean_box(0), v_x_655_, v___f_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v___y_662_, lean_object* v_toPure_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_a_664_);
lean_ctor_set(v___x_665_, 1, v___y_662_);
v___x_666_ = lean_apply_2(v_toPure_663_, lean_box(0), v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object* v_inst_667_, lean_object* v_00_u03b1_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_toApplicative_671_; lean_object* v_toBind_672_; lean_object* v_toPure_673_; lean_object* v___f_674_; lean_object* v___x_675_; 
v_toApplicative_671_ = lean_ctor_get(v_inst_667_, 0);
lean_inc_ref(v_toApplicative_671_);
v_toBind_672_ = lean_ctor_get(v_inst_667_, 1);
lean_inc(v_toBind_672_);
lean_dec_ref(v_inst_667_);
v_toPure_673_ = lean_ctor_get(v_toApplicative_671_, 1);
lean_inc(v_toPure_673_);
lean_dec_ref(v_toApplicative_671_);
v___f_674_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_674_, 0, v___y_670_);
lean_closure_set(v___f_674_, 1, v_toPure_673_);
v___x_675_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___y_669_, v___f_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg(lean_object* v_inst_676_){
_start:
{
lean_object* v___f_677_; 
v___f_677_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_677_, 0, v_inst_676_);
return v___f_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad(lean_object* v_m_678_, lean_object* v_00_u03b5_679_, lean_object* v_00_u03c3_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v___f_682_; 
v___f_682_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_682_, 0, v_inst_681_);
return v___f_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure___redArg(lean_object* v_inst_683_, lean_object* v_a_684_, lean_object* v_s_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_a_684_);
lean_ctor_set(v___x_686_, 1, v_s_685_);
v___x_687_ = lean_apply_2(v_inst_683_, lean_box(0), v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure(lean_object* v_00_u03b5_688_, lean_object* v_00_u03c3_689_, lean_object* v_00_u03b1_690_, lean_object* v_m_691_, lean_object* v_inst_692_, lean_object* v_a_693_, lean_object* v_s_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_a_693_);
lean_ctor_set(v___x_695_, 1, v_s_694_);
v___x_696_ = lean_apply_2(v_inst_692_, lean_box(0), v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object* v_inst_697_, lean_object* v_00_u03b1_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___y_699_);
lean_ctor_set(v___x_701_, 1, v___y_700_);
v___x_702_ = lean_apply_2(v_inst_697_, lean_box(0), v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg(lean_object* v_inst_703_){
_start:
{
lean_object* v___f_704_; 
v___f_704_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_704_, 0, v_inst_703_);
return v___f_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure(lean_object* v_00_u03b5_705_, lean_object* v_00_u03c3_706_, lean_object* v_m_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v___f_709_; 
v___f_709_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_709_, 0, v_inst_708_);
return v___f_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg___lam__0(lean_object* v_f_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_a_712_ = lean_ctor_get(v_x_711_, 0);
v_a_713_ = lean_ctor_get(v_x_711_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v_x_711_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_inc(v_a_712_);
lean_dec(v_x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_apply_1(v_f_710_, v_a_712_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_a_713_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_f_710_);
v_a_722_ = lean_ctor_get(v_x_711_, 0);
v_a_723_ = lean_ctor_get(v_x_711_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v_x_711_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_inc(v_a_722_);
lean_dec(v_x_711_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg(lean_object* v_inst_731_, lean_object* v_f_732_, lean_object* v_x_733_, lean_object* v_s_734_){
_start:
{
lean_object* v_map_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_map_735_ = lean_ctor_get(v_inst_731_, 0);
lean_inc(v_map_735_);
lean_dec_ref(v_inst_731_);
v___f_736_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_736_, 0, v_f_732_);
v___x_737_ = lean_apply_1(v_x_733_, v_s_734_);
v___x_738_ = lean_apply_4(v_map_735_, lean_box(0), lean_box(0), v___f_736_, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map(lean_object* v_00_u03b5_739_, lean_object* v_00_u03c3_740_, lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_inst_744_, lean_object* v_f_745_, lean_object* v_x_746_, lean_object* v_s_747_){
_start:
{
lean_object* v_map_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_map_748_ = lean_ctor_get(v_inst_744_, 0);
lean_inc(v_map_748_);
lean_dec_ref(v_inst_744_);
v___f_749_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_749_, 0, v_f_745_);
v___x_750_ = lean_apply_1(v_x_746_, v_s_747_);
v___x_751_ = lean_apply_4(v_map_748_, lean_box(0), lean_box(0), v___f_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__0(lean_object* v___y_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_a_754_ = lean_ctor_get(v_x_753_, 0);
v_a_755_ = lean_ctor_get(v_x_753_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_x_753_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_inc(v_a_754_);
lean_dec(v_x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_apply_1(v___y_752_, v_a_754_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_755_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___y_752_);
v_a_764_ = lean_ctor_get(v_x_753_, 0);
v_a_765_ = lean_ctor_get(v_x_753_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v_x_753_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v_x_753_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__1(lean_object* v_inst_773_, lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_map_779_; lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_map_779_ = lean_ctor_get(v_inst_773_, 0);
lean_inc(v_map_779_);
lean_dec_ref(v_inst_773_);
v___f_780_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__0), 2, 1);
lean_closure_set(v___f_780_, 0, v___y_776_);
v___x_781_ = lean_apply_1(v___y_777_, v___y_778_);
v___x_782_ = lean_apply_4(v_map_779_, lean_box(0), lean_box(0), v___f_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__2(lean_object* v___f_783_, lean_object* v_00_u03b1_784_, lean_object* v_00_u03b2_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_789_, 0, lean_box(0));
lean_closure_set(v___x_789_, 1, lean_box(0));
lean_closure_set(v___x_789_, 2, v___y_786_);
v___x_790_ = lean_apply_5(v___f_783_, lean_box(0), lean_box(0), v___x_789_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object* v_inst_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_792_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__1), 6, 1);
lean_closure_set(v___f_792_, 0, v_inst_791_);
lean_inc_ref(v___f_792_);
v___f_793_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__2), 6, 1);
lean_closure_set(v___f_793_, 0, v___f_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___f_792_);
lean_ctor_set(v___x_794_, 1, v___f_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor(lean_object* v_00_u03b5_795_, lean_object* v_00_u03c3_796_, lean_object* v_m_797_, lean_object* v_inst_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lake_EStateT_instFunctor___redArg(v_inst_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg___lam__0(lean_object* v_f_800_, lean_object* v_toPure_801_, lean_object* v_____do__lift_802_){
_start:
{
if (lean_obj_tag(v_____do__lift_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_805_; 
lean_dec(v_toPure_801_);
v_a_803_ = lean_ctor_get(v_____do__lift_802_, 0);
lean_inc(v_a_803_);
v_a_804_ = lean_ctor_get(v_____do__lift_802_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v_____do__lift_802_, 2);
v___x_805_ = lean_apply_2(v_f_800_, v_a_803_, v_a_804_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_f_800_);
v_a_806_ = lean_ctor_get(v_____do__lift_802_, 0);
v_a_807_ = lean_ctor_get(v_____do__lift_802_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_____do__lift_802_);
if (v_isSharedCheck_815_ == 0)
{
v___x_809_ = v_____do__lift_802_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_inc(v_a_806_);
lean_dec(v_____do__lift_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_806_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_807_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_apply_2(v_toPure_801_, lean_box(0), v___x_812_);
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg(lean_object* v_inst_816_, lean_object* v_x_817_, lean_object* v_f_818_, lean_object* v_s_819_){
_start:
{
lean_object* v_toApplicative_820_; lean_object* v_toBind_821_; lean_object* v_toPure_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; 
v_toApplicative_820_ = lean_ctor_get(v_inst_816_, 0);
lean_inc_ref(v_toApplicative_820_);
v_toBind_821_ = lean_ctor_get(v_inst_816_, 1);
lean_inc(v_toBind_821_);
lean_dec_ref(v_inst_816_);
v_toPure_822_ = lean_ctor_get(v_toApplicative_820_, 1);
lean_inc(v_toPure_822_);
lean_dec_ref(v_toApplicative_820_);
v___x_823_ = lean_apply_1(v_x_817_, v_s_819_);
v___f_824_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_824_, 0, v_f_818_);
lean_closure_set(v___f_824_, 1, v_toPure_822_);
v___x_825_ = lean_apply_4(v_toBind_821_, lean_box(0), lean_box(0), v___x_823_, v___f_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind(lean_object* v_00_u03b5_826_, lean_object* v_00_u03c3_827_, lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_x_832_, lean_object* v_f_833_, lean_object* v_s_834_){
_start:
{
lean_object* v_toApplicative_835_; lean_object* v_toBind_836_; lean_object* v_toPure_837_; lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___x_840_; 
v_toApplicative_835_ = lean_ctor_get(v_inst_831_, 0);
lean_inc_ref(v_toApplicative_835_);
v_toBind_836_ = lean_ctor_get(v_inst_831_, 1);
lean_inc(v_toBind_836_);
lean_dec_ref(v_inst_831_);
v_toPure_837_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_inc(v_toPure_837_);
lean_dec_ref(v_toApplicative_835_);
v___x_838_ = lean_apply_1(v_x_832_, v_s_834_);
v___f_839_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_839_, 0, v_f_833_);
lean_closure_set(v___f_839_, 1, v_toPure_837_);
v___x_840_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_838_, v___f_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg___lam__0(lean_object* v_y_841_, lean_object* v_toPure_842_, lean_object* v_____do__lift_843_){
_start:
{
if (lean_obj_tag(v_____do__lift_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_toPure_842_);
v_a_844_ = lean_ctor_get(v_____do__lift_843_, 1);
lean_inc(v_a_844_);
lean_dec_ref_known(v_____do__lift_843_, 2);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_2(v_y_841_, v___x_845_, v_a_844_);
return v___x_846_;
}
else
{
lean_object* v_a_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_y_841_);
v_a_847_ = lean_ctor_get(v_____do__lift_843_, 0);
v_a_848_ = lean_ctor_get(v_____do__lift_843_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_____do__lift_843_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_____do__lift_843_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_inc(v_a_847_);
lean_dec(v_____do__lift_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_a_848_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = lean_apply_2(v_toPure_842_, lean_box(0), v___x_853_);
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg(lean_object* v_inst_857_, lean_object* v_x_858_, lean_object* v_y_859_, lean_object* v_s_860_){
_start:
{
lean_object* v_toApplicative_861_; lean_object* v_toBind_862_; lean_object* v_toPure_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; 
v_toApplicative_861_ = lean_ctor_get(v_inst_857_, 0);
lean_inc_ref(v_toApplicative_861_);
v_toBind_862_ = lean_ctor_get(v_inst_857_, 1);
lean_inc(v_toBind_862_);
lean_dec_ref(v_inst_857_);
v_toPure_863_ = lean_ctor_get(v_toApplicative_861_, 1);
lean_inc(v_toPure_863_);
lean_dec_ref(v_toApplicative_861_);
v___x_864_ = lean_apply_1(v_x_858_, v_s_860_);
v___f_865_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_865_, 0, v_y_859_);
lean_closure_set(v___f_865_, 1, v_toPure_863_);
v___x_866_ = lean_apply_4(v_toBind_862_, lean_box(0), lean_box(0), v___x_864_, v___f_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight(lean_object* v_00_u03b5_867_, lean_object* v_00_u03c3_868_, lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_m_871_, lean_object* v_inst_872_, lean_object* v_x_873_, lean_object* v_y_874_, lean_object* v_s_875_){
_start:
{
lean_object* v_toApplicative_876_; lean_object* v_toBind_877_; lean_object* v_toPure_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___x_881_; 
v_toApplicative_876_ = lean_ctor_get(v_inst_872_, 0);
lean_inc_ref(v_toApplicative_876_);
v_toBind_877_ = lean_ctor_get(v_inst_872_, 1);
lean_inc(v_toBind_877_);
lean_dec_ref(v_inst_872_);
v_toPure_878_ = lean_ctor_get(v_toApplicative_876_, 1);
lean_inc(v_toPure_878_);
lean_dec_ref(v_toApplicative_876_);
v___x_879_ = lean_apply_1(v_x_873_, v_s_875_);
v___f_880_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_880_, 0, v_y_874_);
lean_closure_set(v___f_880_, 1, v_toPure_878_);
v___x_881_ = lean_apply_4(v_toBind_877_, lean_box(0), lean_box(0), v___x_879_, v___f_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__0(lean_object* v___y_882_, lean_object* v_toPure_883_, lean_object* v_____do__lift_884_){
_start:
{
if (lean_obj_tag(v_____do__lift_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
lean_dec(v_toPure_883_);
v_a_885_ = lean_ctor_get(v_____do__lift_884_, 0);
lean_inc(v_a_885_);
v_a_886_ = lean_ctor_get(v_____do__lift_884_, 1);
lean_inc(v_a_886_);
lean_dec_ref_known(v_____do__lift_884_, 2);
v___x_887_ = lean_apply_2(v___y_882_, v_a_885_, v_a_886_);
return v___x_887_;
}
else
{
lean_object* v_a_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
lean_dec(v___y_882_);
v_a_888_ = lean_ctor_get(v_____do__lift_884_, 0);
v_a_889_ = lean_ctor_get(v_____do__lift_884_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_____do__lift_884_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v_____do__lift_884_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_inc(v_a_888_);
lean_dec(v_____do__lift_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_888_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_889_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_apply_2(v_toPure_883_, lean_box(0), v___x_894_);
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object* v_toPure_898_, lean_object* v_toBind_899_, lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; 
v___x_905_ = lean_apply_1(v___y_902_, v___y_904_);
v___f_906_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_906_, 0, v___y_903_);
lean_closure_set(v___f_906_, 1, v_toPure_898_);
v___x_907_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_905_, v___f_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__2(lean_object* v___y_908_, lean_object* v_toPure_909_, lean_object* v_____do__lift_910_){
_start:
{
if (lean_obj_tag(v_____do__lift_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_toPure_909_);
v_a_911_ = lean_ctor_get(v_____do__lift_910_, 1);
lean_inc(v_a_911_);
lean_dec_ref_known(v_____do__lift_910_, 2);
v___x_912_ = lean_box(0);
v___x_913_ = lean_apply_2(v___y_908_, v___x_912_, v_a_911_);
return v___x_913_;
}
else
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
lean_dec(v___y_908_);
v_a_914_ = lean_ctor_get(v_____do__lift_910_, 0);
v_a_915_ = lean_ctor_get(v_____do__lift_910_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_____do__lift_910_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v_____do__lift_910_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_inc(v_a_914_);
lean_dec(v_____do__lift_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_914_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_a_915_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_apply_2(v_toPure_909_, lean_box(0), v___x_920_);
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object* v_toPure_924_, lean_object* v_toBind_925_, lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___x_933_; 
v___x_931_ = lean_apply_1(v___y_928_, v___y_930_);
v___f_932_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_932_, 0, v___y_929_);
lean_closure_set(v___f_932_, 1, v_toPure_924_);
v___x_933_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_931_, v___f_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6(lean_object* v_a_934_, lean_object* v_toPure_935_, lean_object* v_x_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_934_);
lean_ctor_set(v___x_938_, 1, v___y_937_);
v___x_939_ = lean_apply_2(v_toPure_935_, lean_box(0), v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6___boxed(lean_object* v_a_940_, lean_object* v_toPure_941_, lean_object* v_x_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_EStateT_instMonad___redArg___lam__6(v_a_940_, v_toPure_941_, v_x_942_, v___y_943_);
lean_dec(v_x_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__4(lean_object* v_toPure_945_, lean_object* v_y_946_, lean_object* v___f_947_, lean_object* v_a_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___f_950_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_950_, 0, v_a_948_);
lean_closure_set(v___f_950_, 1, v_toPure_945_);
v___x_951_ = lean_box(0);
v___x_952_ = lean_apply_1(v_y_946_, v___x_951_);
v___x_953_ = lean_apply_5(v___f_947_, lean_box(0), lean_box(0), v___x_952_, v___f_950_, v___y_949_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object* v_toPure_954_, lean_object* v___f_955_, lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___f_961_; lean_object* v___x_962_; 
lean_inc(v___f_955_);
v___f_961_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__4), 5, 3);
lean_closure_set(v___f_961_, 0, v_toPure_954_);
lean_closure_set(v___f_961_, 1, v_y_959_);
lean_closure_set(v___f_961_, 2, v___f_955_);
v___x_962_ = lean_apply_5(v___f_955_, lean_box(0), lean_box(0), v_x_958_, v___f_961_, v___y_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__7(lean_object* v_a_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
v_a_965_ = lean_ctor_get(v_x_964_, 0);
v_a_966_ = lean_ctor_get(v_x_964_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v_x_964_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_inc(v_a_965_);
lean_dec(v_x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_apply_1(v_a_963_, v_a_965_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_966_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_963_);
v_a_975_ = lean_ctor_get(v_x_964_, 0);
v_a_976_ = lean_ctor_get(v_x_964_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v_x_964_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_inc(v_a_975_);
lean_dec(v_x_964_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_975_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__8(lean_object* v_toFunctor_984_, lean_object* v_x_985_, lean_object* v_toPure_986_, lean_object* v_____do__lift_987_){
_start:
{
if (lean_obj_tag(v_____do__lift_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v_map_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v_toPure_986_);
v_a_988_ = lean_ctor_get(v_____do__lift_987_, 0);
lean_inc(v_a_988_);
v_a_989_ = lean_ctor_get(v_____do__lift_987_, 1);
lean_inc(v_a_989_);
lean_dec_ref_known(v_____do__lift_987_, 2);
v_map_990_ = lean_ctor_get(v_toFunctor_984_, 0);
lean_inc(v_map_990_);
lean_dec_ref(v_toFunctor_984_);
v___f_991_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__7), 2, 1);
lean_closure_set(v___f_991_, 0, v_a_988_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_apply_2(v_x_985_, v___x_992_, v_a_989_);
v___x_994_ = lean_apply_4(v_map_990_, lean_box(0), lean_box(0), v___f_991_, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v_a_995_; lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_x_985_);
lean_dec_ref(v_toFunctor_984_);
v_a_995_ = lean_ctor_get(v_____do__lift_987_, 0);
v_a_996_ = lean_ctor_get(v_____do__lift_987_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_____do__lift_987_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_998_ = v_____do__lift_987_;
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_inc(v_a_995_);
lean_dec(v_____do__lift_987_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1004_;
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
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_995_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_apply_2(v_toPure_986_, lean_box(0), v___x_1001_);
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object* v_toFunctor_1005_, lean_object* v_toPure_1006_, lean_object* v_toBind_1007_, lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_f_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1013_, 0, v_toFunctor_1005_);
lean_closure_set(v___f_1013_, 1, v_x_1011_);
lean_closure_set(v___f_1013_, 2, v_toPure_1006_);
v___x_1014_ = lean_apply_1(v_f_1010_, v___y_1012_);
v___x_1015_ = lean_apply_4(v_toBind_1007_, lean_box(0), lean_box(0), v___x_1014_, v___f_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg(lean_object* v_inst_1016_){
_start:
{
lean_object* v_toApplicative_1017_; lean_object* v_toBind_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1043_; 
v_toApplicative_1017_ = lean_ctor_get(v_inst_1016_, 0);
v_toBind_1018_ = lean_ctor_get(v_inst_1016_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_inst_1016_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1020_ = v_inst_1016_;
v_isShared_1021_ = v_isSharedCheck_1043_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_toBind_1018_);
lean_inc(v_toApplicative_1017_);
lean_dec(v_inst_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1043_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_toFunctor_1022_; lean_object* v_toPure_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1039_; 
v_toFunctor_1022_ = lean_ctor_get(v_toApplicative_1017_, 0);
v_toPure_1023_ = lean_ctor_get(v_toApplicative_1017_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_toApplicative_1017_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; 
v_unused_1040_ = lean_ctor_get(v_toApplicative_1017_, 4);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_toApplicative_1017_, 3);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_toApplicative_1017_, 2);
lean_dec(v_unused_1042_);
v___x_1025_ = v_toApplicative_1017_;
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_toPure_1023_);
lean_inc(v_toFunctor_1022_);
lean_dec(v_toApplicative_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; lean_object* v___x_1034_; 
lean_inc_n(v_toBind_1018_, 2);
lean_inc_n(v_toPure_1023_, 4);
v___f_1027_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1027_, 0, v_toPure_1023_);
lean_closure_set(v___f_1027_, 1, v_toBind_1018_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1028_, 0, v_toPure_1023_);
lean_closure_set(v___f_1028_, 1, v_toBind_1018_);
lean_inc_ref(v___f_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1029_, 0, v_toPure_1023_);
lean_closure_set(v___f_1029_, 1, v___f_1027_);
lean_inc_ref(v_toFunctor_1022_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1030_, 0, v_toFunctor_1022_);
lean_closure_set(v___f_1030_, 1, v_toPure_1023_);
lean_closure_set(v___f_1030_, 2, v_toBind_1018_);
v___x_1031_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1022_);
v___f_1032_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1032_, 0, v_toPure_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v___f_1028_);
lean_ctor_set(v___x_1025_, 3, v___f_1029_);
lean_ctor_set(v___x_1025_, 2, v___f_1030_);
lean_ctor_set(v___x_1025_, 1, v___f_1032_);
lean_ctor_set(v___x_1025_, 0, v___x_1031_);
v___x_1034_ = v___x_1025_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___f_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___f_1029_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___f_1028_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___f_1027_);
lean_ctor_set(v___x_1020_, 0, v___x_1034_);
v___x_1036_ = v___x_1020_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___f_1027_);
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
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad(lean_object* v_00_u03b5_1044_, lean_object* v_00_u03c3_1045_, lean_object* v_m_1046_, lean_object* v_inst_1047_){
_start:
{
lean_object* v_toApplicative_1048_; lean_object* v_toBind_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1074_; 
v_toApplicative_1048_ = lean_ctor_get(v_inst_1047_, 0);
v_toBind_1049_ = lean_ctor_get(v_inst_1047_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_inst_1047_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1051_ = v_inst_1047_;
v_isShared_1052_ = v_isSharedCheck_1074_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_toBind_1049_);
lean_inc(v_toApplicative_1048_);
lean_dec(v_inst_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1074_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_toFunctor_1053_; lean_object* v_toPure_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1070_; 
v_toFunctor_1053_ = lean_ctor_get(v_toApplicative_1048_, 0);
v_toPure_1054_ = lean_ctor_get(v_toApplicative_1048_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_toApplicative_1048_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1071_ = lean_ctor_get(v_toApplicative_1048_, 4);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_toApplicative_1048_, 3);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_toApplicative_1048_, 2);
lean_dec(v_unused_1073_);
v___x_1056_ = v_toApplicative_1048_;
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_toPure_1054_);
lean_inc(v_toFunctor_1053_);
lean_dec(v_toApplicative_1048_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1065_; 
lean_inc_n(v_toBind_1049_, 2);
lean_inc_n(v_toPure_1054_, 4);
v___f_1058_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1058_, 0, v_toPure_1054_);
lean_closure_set(v___f_1058_, 1, v_toBind_1049_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1059_, 0, v_toPure_1054_);
lean_closure_set(v___f_1059_, 1, v_toBind_1049_);
lean_inc_ref(v___f_1058_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1060_, 0, v_toPure_1054_);
lean_closure_set(v___f_1060_, 1, v___f_1058_);
lean_inc_ref(v_toFunctor_1053_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1061_, 0, v_toFunctor_1053_);
lean_closure_set(v___f_1061_, 1, v_toPure_1054_);
lean_closure_set(v___f_1061_, 2, v_toBind_1049_);
v___x_1062_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1053_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1063_, 0, v_toPure_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___f_1059_);
lean_ctor_set(v___x_1056_, 3, v___f_1060_);
lean_ctor_set(v___x_1056_, 2, v___f_1061_);
lean_ctor_set(v___x_1056_, 1, v___f_1063_);
lean_ctor_set(v___x_1056_, 0, v___x_1062_);
v___x_1065_ = v___x_1056_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1063_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___f_1061_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___f_1059_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___f_1058_);
lean_ctor_set(v___x_1051_, 0, v___x_1065_);
v___x_1067_ = v___x_1051_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___f_1058_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___redArg(lean_object* v_inst_1075_, lean_object* v_s_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_s_1076_);
v___x_1079_ = lean_apply_2(v_inst_1075_, lean_box(0), v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set(lean_object* v_00_u03b5_1080_, lean_object* v_00_u03c3_1081_, lean_object* v_m_1082_, lean_object* v_inst_1083_, lean_object* v_s_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_s_1084_);
v___x_1088_ = lean_apply_2(v_inst_1083_, lean_box(0), v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___boxed(lean_object* v_00_u03b5_1089_, lean_object* v_00_u03c3_1090_, lean_object* v_m_1091_, lean_object* v_inst_1092_, lean_object* v_s_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_EStateT_set(v_00_u03b5_1089_, v_00_u03c3_1090_, v_m_1091_, v_inst_1092_, v_s_1093_, v_x_1094_);
lean_dec(v_x_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get___redArg(lean_object* v_inst_1096_, lean_object* v_s_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_s_1097_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_s_1097_);
lean_ctor_set(v___x_1098_, 1, v_s_1097_);
v___x_1099_ = lean_apply_2(v_inst_1096_, lean_box(0), v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get(lean_object* v_00_u03b5_1100_, lean_object* v_00_u03c3_1101_, lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_s_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_inc(v_s_1104_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_s_1104_);
lean_ctor_set(v___x_1105_, 1, v_s_1104_);
v___x_1106_ = lean_apply_2(v_inst_1103_, lean_box(0), v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet___redArg(lean_object* v_inst_1107_, lean_object* v_f_1108_, lean_object* v_s_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v___x_1110_ = lean_apply_1(v_f_1108_, v_s_1109_);
v_fst_1111_ = lean_ctor_get(v___x_1110_, 0);
v_snd_1112_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_snd_1112_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_apply_2(v_inst_1107_, lean_box(0), v___x_1117_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet(lean_object* v_00_u03b5_1121_, lean_object* v_00_u03c3_1122_, lean_object* v_00_u03b1_1123_, lean_object* v_m_1124_, lean_object* v_inst_1125_, lean_object* v_f_1126_, lean_object* v_s_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v___x_1128_ = lean_apply_1(v_f_1126_, v_s_1127_);
v_fst_1129_ = lean_ctor_get(v___x_1128_, 0);
v_snd_1130_ = lean_ctor_get(v___x_1128_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fst_1129_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_snd_1130_);
v___x_1135_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_apply_2(v_inst_1125_, lean_box(0), v___x_1135_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(lean_object* v_inst_1139_, lean_object* v_00_u03b1_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v___x_1143_ = lean_apply_1(v___y_1141_, v___y_1142_);
v_fst_1144_ = lean_ctor_get(v___x_1143_, 0);
v_snd_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_inc(v_fst_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_fst_1144_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_snd_1145_);
v___x_1150_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_apply_2(v_inst_1139_, lean_box(0), v___x_1150_);
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object* v_inst_1154_){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_inc_n(v_inst_1154_, 2);
v___f_1155_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1155_, 0, v_inst_1154_);
v___x_1156_ = lean_alloc_closure((void*)(l_Lake_EStateT_get), 5, 4);
lean_closure_set(v___x_1156_, 0, lean_box(0));
lean_closure_set(v___x_1156_, 1, lean_box(0));
lean_closure_set(v___x_1156_, 2, lean_box(0));
lean_closure_set(v___x_1156_, 3, v_inst_1154_);
v___x_1157_ = lean_alloc_closure((void*)(l_Lake_EStateT_set___boxed), 6, 4);
lean_closure_set(v___x_1157_, 0, lean_box(0));
lean_closure_set(v___x_1157_, 1, lean_box(0));
lean_closure_set(v___x_1157_, 2, lean_box(0));
lean_closure_set(v___x_1157_, 3, v_inst_1154_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
lean_ctor_set(v___x_1158_, 2, v___f_1155_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure(lean_object* v_00_u03b5_1159_, lean_object* v_00_u03c3_1160_, lean_object* v_m_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw___redArg(lean_object* v_inst_1164_, lean_object* v_e_1165_, lean_object* v_s_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_e_1165_);
lean_ctor_set(v___x_1167_, 1, v_s_1166_);
v___x_1168_ = lean_apply_2(v_inst_1164_, lean_box(0), v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw(lean_object* v_00_u03b5_1169_, lean_object* v_00_u03c3_1170_, lean_object* v_00_u03b1_1171_, lean_object* v_m_1172_, lean_object* v_inst_1173_, lean_object* v_e_1174_, lean_object* v_s_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_e_1174_);
lean_ctor_set(v___x_1176_, 1, v_s_1175_);
v___x_1177_ = lean_apply_2(v_inst_1173_, lean_box(0), v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg___lam__0(lean_object* v_toPure_1178_, lean_object* v_handle_1179_, lean_object* v_____do__lift_1180_){
_start:
{
if (lean_obj_tag(v_____do__lift_1180_) == 0)
{
lean_object* v___x_1181_; 
lean_dec(v_handle_1179_);
v___x_1181_ = lean_apply_2(v_toPure_1178_, lean_box(0), v_____do__lift_1180_);
return v___x_1181_;
}
else
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1184_; 
lean_dec(v_toPure_1178_);
v_a_1182_ = lean_ctor_get(v_____do__lift_1180_, 0);
lean_inc(v_a_1182_);
v_a_1183_ = lean_ctor_get(v_____do__lift_1180_, 1);
lean_inc(v_a_1183_);
lean_dec_ref_known(v_____do__lift_1180_, 2);
v___x_1184_ = lean_apply_2(v_handle_1179_, v_a_1182_, v_a_1183_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg(lean_object* v_inst_1185_, lean_object* v_x_1186_, lean_object* v_handle_1187_, lean_object* v_s_1188_){
_start:
{
lean_object* v_toApplicative_1189_; lean_object* v_toBind_1190_; lean_object* v_toPure_1191_; lean_object* v___x_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v_toApplicative_1189_ = lean_ctor_get(v_inst_1185_, 0);
lean_inc_ref(v_toApplicative_1189_);
v_toBind_1190_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc(v_toBind_1190_);
lean_dec_ref(v_inst_1185_);
v_toPure_1191_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_inc(v_toPure_1191_);
lean_dec_ref(v_toApplicative_1189_);
v___x_1192_ = lean_apply_1(v_x_1186_, v_s_1188_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1193_, 0, v_toPure_1191_);
lean_closure_set(v___f_1193_, 1, v_handle_1187_);
v___x_1194_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v___x_1192_, v___f_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch(lean_object* v_00_u03b5_1195_, lean_object* v_00_u03c3_1196_, lean_object* v_00_u03b1_1197_, lean_object* v_m_1198_, lean_object* v_inst_1199_, lean_object* v_x_1200_, lean_object* v_handle_1201_, lean_object* v_s_1202_){
_start:
{
lean_object* v_toApplicative_1203_; lean_object* v_toBind_1204_; lean_object* v_toPure_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; 
v_toApplicative_1203_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc_ref(v_toApplicative_1203_);
v_toBind_1204_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc(v_toBind_1204_);
lean_dec_ref(v_inst_1199_);
v_toPure_1205_ = lean_ctor_get(v_toApplicative_1203_, 1);
lean_inc(v_toPure_1205_);
lean_dec_ref(v_toApplicative_1203_);
v___x_1206_ = lean_apply_1(v_x_1200_, v_s_1202_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1207_, 0, v_toPure_1205_);
lean_closure_set(v___f_1207_, 1, v_handle_1201_);
v___x_1208_ = lean_apply_4(v_toBind_1204_, lean_box(0), lean_box(0), v___x_1206_, v___f_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(lean_object* v_toPure_1209_, lean_object* v___y_1210_, lean_object* v_____do__lift_1211_){
_start:
{
if (lean_obj_tag(v_____do__lift_1211_) == 0)
{
lean_object* v___x_1212_; 
lean_dec(v___y_1210_);
v___x_1212_ = lean_apply_2(v_toPure_1209_, lean_box(0), v_____do__lift_1211_);
return v___x_1212_;
}
else
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1215_; 
lean_dec(v_toPure_1209_);
v_a_1213_ = lean_ctor_get(v_____do__lift_1211_, 0);
lean_inc(v_a_1213_);
v_a_1214_ = lean_ctor_get(v_____do__lift_1211_, 1);
lean_inc(v_a_1214_);
lean_dec_ref_known(v_____do__lift_1211_, 2);
v___x_1215_ = lean_apply_2(v___y_1210_, v_a_1213_, v_a_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(lean_object* v_toPure_1216_, lean_object* v_toBind_1217_, lean_object* v_00_u03b1_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_apply_1(v___y_1219_, v___y_1221_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1223_, 0, v_toPure_1216_);
lean_closure_set(v___f_1223_, 1, v___y_1220_);
v___x_1224_ = lean_apply_4(v_toBind_1217_, lean_box(0), lean_box(0), v___x_1222_, v___f_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(lean_object* v_toPure_1225_, lean_object* v_00_u03b1_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___y_1227_);
lean_ctor_set(v___x_1229_, 1, v___y_1228_);
v___x_1230_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(lean_object* v_inst_1231_){
_start:
{
lean_object* v_toApplicative_1232_; lean_object* v_toBind_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1243_; 
v_toApplicative_1232_ = lean_ctor_get(v_inst_1231_, 0);
v_toBind_1233_ = lean_ctor_get(v_inst_1231_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_inst_1231_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1235_ = v_inst_1231_;
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_toBind_1233_);
lean_inc(v_toApplicative_1232_);
lean_dec(v_inst_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_toPure_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1241_; 
v_toPure_1237_ = lean_ctor_get(v_toApplicative_1232_, 1);
lean_inc_n(v_toPure_1237_, 2);
lean_dec_ref(v_toApplicative_1232_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1), 6, 2);
lean_closure_set(v___f_1238_, 0, v_toPure_1237_);
lean_closure_set(v___f_1238_, 1, v_toBind_1233_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2), 4, 1);
lean_closure_set(v___f_1239_, 0, v_toPure_1237_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___f_1238_);
lean_ctor_set(v___x_1235_, 0, v___f_1239_);
v___x_1241_ = v___x_1235_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___f_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___f_1238_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad(lean_object* v_00_u03b5_1244_, lean_object* v_00_u03c3_1245_, lean_object* v_m_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg___lam__0(lean_object* v_toPure_1249_, lean_object* v_x_u2082_1250_, lean_object* v_____do__lift_1251_){
_start:
{
if (lean_obj_tag(v_____do__lift_1251_) == 0)
{
lean_object* v___x_1252_; 
lean_dec(v_x_u2082_1250_);
v___x_1252_ = lean_apply_2(v_toPure_1249_, lean_box(0), v_____do__lift_1251_);
return v___x_1252_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v_toPure_1249_);
v_a_1253_ = lean_ctor_get(v_____do__lift_1251_, 1);
lean_inc(v_a_1253_);
lean_dec_ref_known(v_____do__lift_1251_, 2);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_apply_2(v_x_u2082_1250_, v___x_1254_, v_a_1253_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg(lean_object* v_inst_1256_, lean_object* v_x_u2081_1257_, lean_object* v_x_u2082_1258_, lean_object* v_s_1259_){
_start:
{
lean_object* v_toApplicative_1260_; lean_object* v_toBind_1261_; lean_object* v_toPure_1262_; lean_object* v___x_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; 
v_toApplicative_1260_ = lean_ctor_get(v_inst_1256_, 0);
lean_inc_ref(v_toApplicative_1260_);
v_toBind_1261_ = lean_ctor_get(v_inst_1256_, 1);
lean_inc(v_toBind_1261_);
lean_dec_ref(v_inst_1256_);
v_toPure_1262_ = lean_ctor_get(v_toApplicative_1260_, 1);
lean_inc(v_toPure_1262_);
lean_dec_ref(v_toApplicative_1260_);
v___x_1263_ = lean_apply_1(v_x_u2081_1257_, v_s_1259_);
v___f_1264_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1264_, 0, v_toPure_1262_);
lean_closure_set(v___f_1264_, 1, v_x_u2082_1258_);
v___x_1265_ = lean_apply_4(v_toBind_1261_, lean_box(0), lean_box(0), v___x_1263_, v___f_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse(lean_object* v_00_u03b5_1266_, lean_object* v_00_u03c3_1267_, lean_object* v_00_u03b1_1268_, lean_object* v_m_1269_, lean_object* v_inst_1270_, lean_object* v_x_u2081_1271_, lean_object* v_x_u2082_1272_, lean_object* v_s_1273_){
_start:
{
lean_object* v_toApplicative_1274_; lean_object* v_toBind_1275_; lean_object* v_toPure_1276_; lean_object* v___x_1277_; lean_object* v___f_1278_; lean_object* v___x_1279_; 
v_toApplicative_1274_ = lean_ctor_get(v_inst_1270_, 0);
lean_inc_ref(v_toApplicative_1274_);
v_toBind_1275_ = lean_ctor_get(v_inst_1270_, 1);
lean_inc(v_toBind_1275_);
lean_dec_ref(v_inst_1270_);
v_toPure_1276_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1276_);
lean_dec_ref(v_toApplicative_1274_);
v___x_1277_ = lean_apply_1(v_x_u2081_1271_, v_s_1273_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1278_, 0, v_toPure_1276_);
lean_closure_set(v___f_1278_, 1, v_x_u2082_1272_);
v___x_1279_ = lean_apply_4(v_toBind_1275_, lean_box(0), lean_box(0), v___x_1277_, v___f_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad___redArg(lean_object* v_inst_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1281_, 0, lean_box(0));
lean_closure_set(v___x_1281_, 1, lean_box(0));
lean_closure_set(v___x_1281_, 2, lean_box(0));
lean_closure_set(v___x_1281_, 3, lean_box(0));
lean_closure_set(v___x_1281_, 4, v_inst_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad(lean_object* v_00_u03b5_1282_, lean_object* v_00_u03c3_1283_, lean_object* v_00_u03b1_1284_, lean_object* v_m_1285_, lean_object* v_inst_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1287_, 0, lean_box(0));
lean_closure_set(v___x_1287_, 1, lean_box(0));
lean_closure_set(v___x_1287_, 2, lean_box(0));
lean_closure_set(v___x_1287_, 3, lean_box(0));
lean_closure_set(v___x_1287_, 4, v_inst_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg___lam__0(lean_object* v_f_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_f_1288_);
v_a_1290_ = lean_ctor_get(v_x_1289_, 0);
v_a_1291_ = lean_ctor_get(v_x_1289_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v_x_1289_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_inc(v_a_1290_);
lean_dec(v_x_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_a_1299_ = lean_ctor_get(v_x_1289_, 0);
v_a_1300_ = lean_ctor_get(v_x_1289_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v_x_1289_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_inc(v_a_1299_);
lean_dec(v_x_1289_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_apply_1(v_f_1288_, v_a_1299_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_a_1300_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg(lean_object* v_inst_1309_, lean_object* v_f_1310_, lean_object* v_x_1311_, lean_object* v_s_1312_){
_start:
{
lean_object* v_map_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_map_1313_ = lean_ctor_get(v_inst_1309_, 0);
lean_inc(v_map_1313_);
lean_dec_ref(v_inst_1309_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1314_, 0, v_f_1310_);
v___x_1315_ = lean_apply_1(v_x_1311_, v_s_1312_);
v___x_1316_ = lean_apply_4(v_map_1313_, lean_box(0), lean_box(0), v___f_1314_, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept(lean_object* v_00_u03b5_1317_, lean_object* v_00_u03b5_x27_1318_, lean_object* v_00_u03c3_1319_, lean_object* v_00_u03b1_1320_, lean_object* v_m_1321_, lean_object* v_inst_1322_, lean_object* v_f_1323_, lean_object* v_x_1324_, lean_object* v_s_1325_){
_start:
{
lean_object* v_map_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_map_1326_ = lean_ctor_get(v_inst_1322_, 0);
lean_inc(v_map_1326_);
lean_dec_ref(v_inst_1322_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1327_, 0, v_f_1323_);
v___x_1328_ = lean_apply_1(v_x_1324_, v_s_1325_);
v___x_1329_ = lean_apply_4(v_map_1326_, lean_box(0), lean_box(0), v___f_1327_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__0(lean_object* v_a_1330_, lean_object* v_toPure_1331_, lean_object* v_____do__lift_1332_){
_start:
{
if (lean_obj_tag(v_____do__lift_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_a_1333_ = lean_ctor_get(v_____do__lift_1332_, 0);
v_a_1334_ = lean_ctor_get(v_____do__lift_1332_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_____do__lift_1332_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1336_ = v_____do__lift_1332_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_inc(v_a_1333_);
lean_dec(v_____do__lift_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1330_);
lean_ctor_set(v___x_1338_, 1, v_a_1333_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1334_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_apply_2(v_toPure_1331_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1330_);
v_a_1344_ = lean_ctor_get(v_____do__lift_1332_, 0);
v_a_1345_ = lean_ctor_get(v_____do__lift_1332_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_____do__lift_1332_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v_____do__lift_1332_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_inc(v_a_1344_);
lean_dec(v_____do__lift_1332_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
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
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1344_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_apply_2(v_toPure_1331_, lean_box(0), v___x_1350_);
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__1(lean_object* v_a_1354_, lean_object* v_toPure_1355_, lean_object* v_____do__lift_1356_){
_start:
{
if (lean_obj_tag(v_____do__lift_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_a_1357_ = lean_ctor_get(v_____do__lift_1356_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_____do__lift_1356_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_____do__lift_1356_, 0);
lean_dec(v_unused_1366_);
v___x_1359_ = v_____do__lift_1356_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v_____do__lift_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 0, v_a_1354_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1362_);
return v___x_1363_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1354_);
v_a_1367_ = lean_ctor_get(v_____do__lift_1356_, 0);
v_a_1368_ = lean_ctor_get(v_____do__lift_1356_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_____do__lift_1356_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v_____do__lift_1356_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v_____do__lift_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
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
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1367_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1373_);
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__2(lean_object* v_toPure_1377_, lean_object* v_f_1378_, lean_object* v_toBind_1379_, lean_object* v_r_1380_){
_start:
{
if (lean_obj_tag(v_r_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_a_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1381_ = lean_ctor_get(v_r_1380_, 0);
lean_inc_n(v_a_1381_, 2);
v_a_1382_ = lean_ctor_get(v_r_1380_, 1);
lean_inc(v_a_1382_);
lean_dec_ref_known(v_r_1380_, 2);
v___f_1383_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1383_, 0, v_a_1381_);
lean_closure_set(v___f_1383_, 1, v_toPure_1377_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1381_);
v___x_1385_ = lean_apply_2(v_f_1378_, v___x_1384_, v_a_1382_);
v___x_1386_ = lean_apply_4(v_toBind_1379_, lean_box(0), lean_box(0), v___x_1385_, v___f_1383_);
return v___x_1386_;
}
else
{
lean_object* v_a_1387_; lean_object* v_a_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_a_1387_ = lean_ctor_get(v_r_1380_, 0);
lean_inc(v_a_1387_);
v_a_1388_ = lean_ctor_get(v_r_1380_, 1);
lean_inc(v_a_1388_);
lean_dec_ref_known(v_r_1380_, 2);
v___f_1389_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1389_, 0, v_a_1387_);
lean_closure_set(v___f_1389_, 1, v_toPure_1377_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_apply_2(v_f_1378_, v___x_1390_, v_a_1388_);
v___x_1392_ = lean_apply_4(v_toBind_1379_, lean_box(0), lean_box(0), v___x_1391_, v___f_1389_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg(lean_object* v_inst_1393_, lean_object* v_x_1394_, lean_object* v_f_1395_, lean_object* v_s_1396_){
_start:
{
lean_object* v_toApplicative_1397_; lean_object* v_toBind_1398_; lean_object* v_toPure_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; 
v_toApplicative_1397_ = lean_ctor_get(v_inst_1393_, 0);
lean_inc_ref(v_toApplicative_1397_);
v_toBind_1398_ = lean_ctor_get(v_inst_1393_, 1);
lean_inc_n(v_toBind_1398_, 2);
lean_dec_ref(v_inst_1393_);
v_toPure_1399_ = lean_ctor_get(v_toApplicative_1397_, 1);
lean_inc(v_toPure_1399_);
lean_dec_ref(v_toApplicative_1397_);
v___x_1400_ = lean_apply_1(v_x_1394_, v_s_1396_);
v___f_1401_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1401_, 0, v_toPure_1399_);
lean_closure_set(v___f_1401_, 1, v_f_1395_);
lean_closure_set(v___f_1401_, 2, v_toBind_1398_);
v___x_1402_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1400_, v___f_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27(lean_object* v_00_u03b5_1403_, lean_object* v_00_u03c3_1404_, lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_m_1407_, lean_object* v_inst_1408_, lean_object* v_x_1409_, lean_object* v_f_1410_, lean_object* v_s_1411_){
_start:
{
lean_object* v_toApplicative_1412_; lean_object* v_toBind_1413_; lean_object* v_toPure_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v_toApplicative_1412_ = lean_ctor_get(v_inst_1408_, 0);
lean_inc_ref(v_toApplicative_1412_);
v_toBind_1413_ = lean_ctor_get(v_inst_1408_, 1);
lean_inc_n(v_toBind_1413_, 2);
lean_dec_ref(v_inst_1408_);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1412_, 1);
lean_inc(v_toPure_1414_);
lean_dec_ref(v_toApplicative_1412_);
v___x_1415_ = lean_apply_1(v_x_1409_, v_s_1411_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1416_, 0, v_toPure_1414_);
lean_closure_set(v___f_1416_, 1, v_f_1410_);
lean_closure_set(v___f_1416_, 2, v_toBind_1413_);
v___x_1417_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v___x_1415_, v___f_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(lean_object* v_toPure_1418_, lean_object* v___y_1419_, lean_object* v_toBind_1420_, lean_object* v_r_1421_){
_start:
{
if (lean_obj_tag(v_r_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1422_ = lean_ctor_get(v_r_1421_, 0);
lean_inc_n(v_a_1422_, 2);
v_a_1423_ = lean_ctor_get(v_r_1421_, 1);
lean_inc(v_a_1423_);
lean_dec_ref_known(v_r_1421_, 2);
v___f_1424_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1424_, 0, v_a_1422_);
lean_closure_set(v___f_1424_, 1, v_toPure_1418_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1422_);
v___x_1426_ = lean_apply_2(v___y_1419_, v___x_1425_, v_a_1423_);
v___x_1427_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1426_, v___f_1424_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_a_1428_ = lean_ctor_get(v_r_1421_, 0);
lean_inc(v_a_1428_);
v_a_1429_ = lean_ctor_get(v_r_1421_, 1);
lean_inc(v_a_1429_);
lean_dec_ref_known(v_r_1421_, 2);
v___f_1430_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1430_, 0, v_a_1428_);
lean_closure_set(v___f_1430_, 1, v_toPure_1418_);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_apply_2(v___y_1419_, v___x_1431_, v_a_1429_);
v___x_1433_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1432_, v___f_1430_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(lean_object* v_inst_1434_, lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_toApplicative_1440_; lean_object* v_toBind_1441_; lean_object* v_toPure_1442_; lean_object* v___x_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; 
v_toApplicative_1440_ = lean_ctor_get(v_inst_1434_, 0);
lean_inc_ref(v_toApplicative_1440_);
v_toBind_1441_ = lean_ctor_get(v_inst_1434_, 1);
lean_inc_n(v_toBind_1441_, 2);
lean_dec_ref(v_inst_1434_);
v_toPure_1442_ = lean_ctor_get(v_toApplicative_1440_, 1);
lean_inc(v_toPure_1442_);
lean_dec_ref(v_toApplicative_1440_);
v___x_1443_ = lean_apply_1(v___y_1437_, v___y_1439_);
v___f_1444_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1444_, 0, v_toPure_1442_);
lean_closure_set(v___f_1444_, 1, v___y_1438_);
lean_closure_set(v___f_1444_, 2, v_toBind_1441_);
v___x_1445_ = lean_apply_4(v_toBind_1441_, lean_box(0), lean_box(0), v___x_1443_, v___f_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg(lean_object* v_inst_1446_){
_start:
{
lean_object* v___f_1447_; 
v___f_1447_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1447_, 0, v_inst_1446_);
return v___f_1447_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad(lean_object* v_00_u03b5_1448_, lean_object* v_00_u03c3_1449_, lean_object* v_m_1450_, lean_object* v_inst_1451_){
_start:
{
lean_object* v___f_1452_; 
v___f_1452_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1452_, 0, v_inst_1451_);
return v___f_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM___redArg(lean_object* v_f_1453_, lean_object* v_s_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_apply_1(v_f_1453_, v_s_1454_);
v___x_1456_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM(lean_object* v_00_u03b5_1457_, lean_object* v_00_u03c3_1458_, lean_object* v_00_u03b1_1459_, lean_object* v_f_1460_, lean_object* v_s_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lake_EStateT_ofEStateM___redArg(v_f_1460_, v_s_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM___redArg(lean_object* v_f_1463_, lean_object* v_s_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_apply_1(v_f_1463_, v_s_1464_);
v___x_1466_ = l_Lake_EResult_toEStateMResult___redArg(v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM(lean_object* v_00_u03b5_1467_, lean_object* v_00_u03c3_1468_, lean_object* v_00_u03b1_1469_, lean_object* v_f_1470_, lean_object* v_s_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lake_EStateT_toEStateM___redArg(v_f_1470_, v_s_1471_);
return v___x_1472_;
}
}
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_EStateT(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_EStateT(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_EStateT(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_EStateT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_EStateT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_EStateT(builtin);
}
#ifdef __cplusplus
}
#endif
