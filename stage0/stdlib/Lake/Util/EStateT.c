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
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lake_EResult_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx(lean_object* v_00_u03b5_6_, lean_object* v_00_u03c3_7_, lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lake_EResult_ctorIdx___redArg(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorIdx___boxed(lean_object* v_00_u03b5_11_, lean_object* v_00_u03c3_12_, lean_object* v_00_u03b1_13_, lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_EResult_ctorIdx(v_00_u03b5_11_, v_00_u03c3_12_, v_00_u03b1_13_, v_x_14_);
lean_dec_ref(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___redArg(lean_object* v_t_16_, lean_object* v_k_17_){
_start:
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v_t_16_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v_t_16_, 1);
lean_inc(v_a_19_);
lean_dec_ref(v_t_16_);
v___x_20_ = lean_apply_2(v_k_17_, v_a_18_, v_a_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim(lean_object* v_00_u03b5_21_, lean_object* v_00_u03c3_22_, lean_object* v_00_u03b1_23_, lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lake_EResult_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ctorElim___boxed(lean_object* v_00_u03b5_30_, lean_object* v_00_u03c3_31_, lean_object* v_00_u03b1_32_, lean_object* v_motive_33_, lean_object* v_ctorIdx_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_k_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_EResult_ctorElim(v_00_u03b5_30_, v_00_u03c3_31_, v_00_u03b1_32_, v_motive_33_, v_ctorIdx_34_, v_t_35_, v_h_36_, v_k_37_);
lean_dec(v_ctorIdx_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim___redArg(lean_object* v_t_39_, lean_object* v_ok_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_EResult_ctorElim___redArg(v_t_39_, v_ok_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ok_elim(lean_object* v_00_u03b5_42_, lean_object* v_00_u03c3_43_, lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_ok_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_EResult_ctorElim___redArg(v_t_46_, v_ok_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim___redArg(lean_object* v_t_50_, lean_object* v_error_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lake_EResult_ctorElim___redArg(v_t_50_, v_error_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_elim(lean_object* v_00_u03b5_53_, lean_object* v_00_u03c3_54_, lean_object* v_00_u03b1_55_, lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_error_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lake_EResult_ctorElim___redArg(v_t_57_, v_error_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited___redArg(lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v_inst_61_);
lean_ctor_set(v___x_63_, 1, v_inst_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited(lean_object* v_00_u03b1_64_, lean_object* v_00_u03c3_65_, lean_object* v_00_u03b5_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_inst_67_);
lean_ctor_set(v___x_69_, 1, v_inst_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v_inst_70_);
lean_ctor_set(v___x_72_, 1, v_inst_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instInhabited__1(lean_object* v_00_u03b5_73_, lean_object* v_00_u03c3_74_, lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v_inst_76_);
lean_ctor_set(v___x_78_, 1, v_inst_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg(lean_object* v_x_79_){
_start:
{
lean_object* v_a_80_; 
v_a_80_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_a_80_);
return v_a_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___redArg___boxed(lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lake_EResult_state___redArg(v_x_81_);
lean_dec_ref(v_x_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state(lean_object* v_00_u03b5_83_, lean_object* v_00_u03c3_84_, lean_object* v_00_u03b1_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_a_87_; 
v_a_87_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_a_87_);
return v_a_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_state___boxed(lean_object* v_00_u03b5_88_, lean_object* v_00_u03c3_89_, lean_object* v_00_u03b1_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_EResult_state(v_00_u03b5_88_, v_00_u03c3_89_, v_00_u03b1_90_, v_x_91_);
lean_dec_ref(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState___redArg(lean_object* v_f_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_95_ = lean_ctor_get(v_x_94_, 0);
v_a_96_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v_x_94_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v_x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_apply_1(v_f_93_, v_a_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
v_a_105_ = lean_ctor_get(v_x_94_, 0);
v_a_106_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v_x_94_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_inc(v_a_105_);
lean_dec(v_x_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_apply_1(v_f_93_, v_a_106_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_105_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_modifyState(lean_object* v_00_u03c3_115_, lean_object* v_00_u03c3_x27_116_, lean_object* v_00_u03b5_117_, lean_object* v_00_u03b1_118_, lean_object* v_f_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_a_121_ = lean_ctor_get(v_x_120_, 0);
v_a_122_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v_x_120_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v_x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_apply_1(v_f_119_, v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_a_131_ = lean_ctor_get(v_x_120_, 0);
v_a_132_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v_x_120_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_inc(v_a_131_);
lean_dec(v_x_120_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_apply_1(v_f_119_, v_a_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_131_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_setState___redArg(lean_object* v_s_141_, lean_object* v_r_142_){
_start:
{
if (lean_obj_tag(v_r_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v_r_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_r_142_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v_r_142_, 1);
lean_dec(v_unused_151_);
v___x_145_ = v_r_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v_r_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_s_141_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_s_141_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v_r_142_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_r_142_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_r_142_, 1);
lean_dec(v_unused_160_);
v___x_154_ = v_r_142_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v_r_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_s_141_);
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_s_141_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_setState(lean_object* v_00_u03c3_x27_161_, lean_object* v_00_u03b5_162_, lean_object* v_00_u03c3_163_, lean_object* v_00_u03b1_164_, lean_object* v_s_165_, lean_object* v_r_166_){
_start:
{
if (lean_obj_tag(v_r_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v_r_166_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_r_166_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_r_166_, 1);
lean_dec(v_unused_175_);
v___x_169_ = v_r_166_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v_r_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v_s_165_);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_s_165_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v_r_166_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_r_166_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_r_166_, 1);
lean_dec(v_unused_184_);
v___x_178_ = v_r_166_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v_r_166_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_s_165_);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_s_165_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd___redArg(lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_a_186_ = lean_ctor_get(v_x_185_, 0);
v_a_187_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v_x_185_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_inc(v_a_186_);
lean_dec(v_x_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_a_186_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_a_187_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_205_; 
v_a_196_ = lean_ctor_get(v_x_185_, 0);
v_a_197_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_205_ == 0)
{
v___x_199_ = v_x_185_;
v_isShared_200_ = v_isSharedCheck_205_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_inc(v_a_196_);
lean_dec(v_x_185_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_205_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_a_196_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 0);
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_197_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd(lean_object* v_00_u03b5_206_, lean_object* v_00_u03c3_207_, lean_object* v_00_u03b1_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v_a_210_ = lean_ctor_get(v_x_209_, 0);
v_a_211_ = lean_ctor_get(v_x_209_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v_x_209_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_inc(v_a_210_);
lean_dec(v_x_209_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_210_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_a_211_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_a_220_ = lean_ctor_get(v_x_209_, 0);
v_a_221_ = lean_ctor_get(v_x_209_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_x_209_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v_x_209_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_a_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 0);
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_a_221_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f___redArg(lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_240_; 
v_a_231_ = lean_ctor_get(v_x_230_, 0);
v_a_232_ = lean_ctor_get(v_x_230_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_240_ == 0)
{
v___x_234_ = v_x_230_;
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_inc(v_a_231_);
lean_dec(v_x_230_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_a_231_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_236_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_a_232_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_a_241_ = lean_ctor_get(v_x_230_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_x_230_, 0);
lean_dec(v_unused_250_);
v___x_243_ = v_x_230_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v_x_230_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 0);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_a_241_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toProd_x3f(lean_object* v_00_u03b5_251_, lean_object* v_00_u03c3_252_, lean_object* v_00_u03b1_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_a_255_ = lean_ctor_get(v_x_254_, 0);
v_a_256_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_264_ == 0)
{
v___x_258_ = v_x_254_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_inc(v_a_255_);
lean_dec(v_x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_255_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_a_256_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_a_265_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_254_, 0);
lean_dec(v_unused_274_);
v___x_267_ = v_x_254_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v_x_254_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 0);
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_a_265_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg(lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v_x_275_, 0);
lean_inc(v_a_276_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_a_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___redArg___boxed(lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lake_EResult_result_x3f___redArg(v_x_279_);
lean_dec_ref(v_x_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f(lean_object* v_00_u03b5_281_, lean_object* v_00_u03c3_282_, lean_object* v_00_u03b1_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; 
v_a_285_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_a_285_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_a_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_result_x3f___boxed(lean_object* v_00_u03b5_288_, lean_object* v_00_u03c3_289_, lean_object* v_00_u03b1_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_EResult_result_x3f(v_00_u03b5_288_, v_00_u03c3_289_, v_00_u03b1_290_, v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_296_; 
v_a_295_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_a_295_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v_a_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___redArg___boxed(lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_EResult_error_x3f___redArg(v_x_297_);
lean_dec_ref(v_x_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f(lean_object* v_00_u03b5_299_, lean_object* v_00_u03c3_300_, lean_object* v_00_u03b1_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_a_304_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_a_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_error_x3f___boxed(lean_object* v_00_u03b5_306_, lean_object* v_00_u03c3_307_, lean_object* v_00_u03b1_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lake_EResult_error_x3f(v_00_u03b5_306_, v_00_u03c3_307_, v_00_u03b1_308_, v_x_309_);
lean_dec_ref(v_x_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg(lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_312_ = lean_ctor_get(v_x_311_, 0);
lean_inc(v_a_312_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_a_312_);
return v___x_313_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v_x_311_, 0);
lean_inc(v_a_314_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_a_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___redArg___boxed(lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lake_EResult_toExcept___redArg(v_x_316_);
lean_dec_ref(v_x_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept(lean_object* v_00_u03b5_318_, lean_object* v_00_u03c3_319_, lean_object* v_00_u03b1_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; 
v_a_322_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_a_322_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_a_322_);
return v___x_323_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_324_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_a_324_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toExcept___boxed(lean_object* v_00_u03b5_326_, lean_object* v_00_u03c3_327_, lean_object* v_00_u03b1_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lake_EResult_toExcept(v_00_u03b5_326_, v_00_u03c3_327_, v_00_u03b1_328_, v_x_329_);
lean_dec_ref(v_x_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_map___redArg(lean_object* v_f_331_, lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_333_ = lean_ctor_get(v_x_332_, 0);
v_a_334_ = lean_ctor_get(v_x_332_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v_x_332_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_inc(v_a_333_);
lean_dec(v_x_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_apply_1(v_f_331_, v_a_333_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_a_334_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_f_331_);
v_a_343_ = lean_ctor_get(v_x_332_, 0);
v_a_344_ = lean_ctor_get(v_x_332_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v_x_332_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_inc(v_a_343_);
lean_dec(v_x_332_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_343_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_map(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_00_u03b5_354_, lean_object* v_00_u03c3_355_, lean_object* v_f_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_a_358_ = lean_ctor_get(v_x_357_, 0);
v_a_359_ = lean_ctor_get(v_x_357_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v_x_357_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_inc(v_a_358_);
lean_dec(v_x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_apply_1(v_f_356_, v_a_358_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_a_359_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_f_356_);
v_a_368_ = lean_ctor_get(v_x_357_, 0);
v_a_369_ = lean_ctor_get(v_x_357_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v_x_357_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_inc(v_a_368_);
lean_dec(v_x_357_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_368_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__0(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
if (lean_obj_tag(v___y_380_) == 0)
{
lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_381_ = lean_ctor_get(v___y_380_, 0);
v_a_382_ = lean_ctor_get(v___y_380_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___y_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___y_380_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_inc(v_a_381_);
lean_dec(v___y_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_apply_1(v___y_379_, v_a_381_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_a_382_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v___y_379_);
v_a_391_ = lean_ctor_get(v___y_380_, 0);
v_a_392_ = lean_ctor_get(v___y_380_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___y_380_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___y_380_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___y_380_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___lam__1(lean_object* v___f_400_, lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_405_, 0, lean_box(0));
lean_closure_set(v___x_405_, 1, lean_box(0));
lean_closure_set(v___x_405_, 2, v___y_403_);
v___x_406_ = lean_apply_4(v___f_400_, lean_box(0), lean_box(0), v___x_405_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg(){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_Lake_EResult_instFunctor___redArg___closed__2));
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___redArg___boxed(lean_object* v___dummy_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_EResult_instFunctor___redArg();
return v_res_416_;
}
}
static lean_object* _init_l_Lake_EResult_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lake_EResult_instFunctor___redArg();
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor(lean_object* v_00_u03b5_418_, lean_object* v_00_u03c3_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_Lake_EResult_instFunctor___closed__0, &l_Lake_EResult_instFunctor___closed__0_once, _init_l_Lake_EResult_instFunctor___closed__0);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult___redArg(lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_422_ = lean_ctor_get(v_x_421_, 0);
v_a_423_ = lean_ctor_get(v_x_421_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v_x_421_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_inc(v_a_422_);
lean_dec(v_x_421_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_431_ = lean_ctor_get(v_x_421_, 0);
v_a_432_ = lean_ctor_get(v_x_421_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_421_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_x_421_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_inc(v_a_431_);
lean_dec(v_x_421_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult(lean_object* v_00_u03b5_440_, lean_object* v_00_u03c3_441_, lean_object* v_00_u03b1_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lake_EResult_toEStateMResult___redArg(v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult___redArg(lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_446_ = lean_ctor_get(v_x_445_, 0);
v_a_447_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_445_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v_x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_455_ = lean_ctor_get(v_x_445_, 0);
v_a_456_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v_x_445_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_inc(v_a_455_);
lean_dec(v_x_445_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_455_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult(lean_object* v_00_u03b5_464_, lean_object* v_00_u03c3_465_, lean_object* v_00_u03b1_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk___redArg(lean_object* v_x_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_apply_1(v_x_469_, v_a_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk(lean_object* v_00_u03b5_472_, lean_object* v_00_u03c3_473_, lean_object* v_00_u03b1_474_, lean_object* v_m_475_, lean_object* v_x_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_apply_1(v_x_476_, v_a_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_s_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v_inst_479_);
lean_ctor_set(v___x_482_, 1, v_s_481_);
v___x_483_ = lean_apply_2(v_inst_480_, lean_box(0), v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(lean_object* v_inst_484_, lean_object* v_inst_485_){
_start:
{
lean_object* v___f_486_; 
v___f_486_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_486_, 0, v_inst_484_);
lean_closure_set(v___f_486_, 1, v_inst_485_);
return v___f_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(lean_object* v_00_u03b5_487_, lean_object* v_00_u03c3_488_, lean_object* v_00_u03b1_489_, lean_object* v_m_490_, lean_object* v_inst_491_, lean_object* v_inst_492_){
_start:
{
lean_object* v___f_493_; 
v___f_493_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_493_, 0, v_inst_491_);
lean_closure_set(v___f_493_, 1, v_inst_492_);
return v___f_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run___redArg(lean_object* v_init_494_, lean_object* v_self_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_apply_1(v_self_495_, v_init_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run(lean_object* v_00_u03b5_497_, lean_object* v_00_u03c3_498_, lean_object* v_00_u03b1_499_, lean_object* v_m_500_, lean_object* v_init_501_, lean_object* v_self_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_apply_1(v_self_502_, v_init_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27___redArg(lean_object* v_inst_505_, lean_object* v_init_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_map_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_map_508_ = lean_ctor_get(v_inst_505_, 0);
lean_inc(v_map_508_);
lean_dec_ref(v_inst_505_);
v___x_509_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_510_ = lean_apply_1(v_x_507_, v_init_506_);
v___x_511_ = lean_apply_4(v_map_508_, lean_box(0), lean_box(0), v___x_509_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27(lean_object* v_00_u03b5_512_, lean_object* v_00_u03b1_513_, lean_object* v_m_514_, lean_object* v_00_u03c3_515_, lean_object* v_inst_516_, lean_object* v_init_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_map_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_map_519_ = lean_ctor_get(v_inst_516_, 0);
lean_inc(v_map_519_);
lean_dec_ref(v_inst_516_);
v___x_520_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_521_ = lean_apply_1(v_x_518_, v_init_517_);
v___x_522_ = lean_apply_4(v_map_519_, lean_box(0), lean_box(0), v___x_520_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT___redArg(lean_object* v_inst_524_, lean_object* v_x_525_, lean_object* v_s_526_){
_start:
{
lean_object* v_map_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_map_527_ = lean_ctor_get(v_inst_524_, 0);
lean_inc(v_map_527_);
lean_dec_ref(v_inst_524_);
v___x_528_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_529_ = lean_apply_1(v_x_525_, v_s_526_);
v___x_530_ = lean_apply_4(v_map_527_, lean_box(0), lean_box(0), v___x_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT(lean_object* v_m_531_, lean_object* v_00_u03b5_532_, lean_object* v_00_u03c3_533_, lean_object* v_00_u03b1_534_, lean_object* v_inst_535_, lean_object* v_x_536_, lean_object* v_s_537_){
_start:
{
lean_object* v_map_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_map_538_ = lean_ctor_get(v_inst_535_, 0);
lean_inc(v_map_538_);
lean_dec_ref(v_inst_535_);
v___x_539_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_540_ = lean_apply_1(v_x_536_, v_s_537_);
v___x_541_ = lean_apply_4(v_map_538_, lean_box(0), lean_box(0), v___x_539_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f___redArg(lean_object* v_inst_543_, lean_object* v_x_544_, lean_object* v_s_545_){
_start:
{
lean_object* v_map_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_map_546_ = lean_ctor_get(v_inst_543_, 0);
lean_inc(v_map_546_);
lean_dec_ref(v_inst_543_);
v___x_547_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_548_ = lean_apply_1(v_x_544_, v_s_545_);
v___x_549_ = lean_apply_4(v_map_546_, lean_box(0), lean_box(0), v___x_547_, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f(lean_object* v_m_550_, lean_object* v_00_u03b5_551_, lean_object* v_00_u03c3_552_, lean_object* v_00_u03b1_553_, lean_object* v_inst_554_, lean_object* v_x_555_, lean_object* v_s_556_){
_start:
{
lean_object* v_map_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_map_557_ = lean_ctor_get(v_inst_554_, 0);
lean_inc(v_map_557_);
lean_dec_ref(v_inst_554_);
v___x_558_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_559_ = lean_apply_1(v_x_555_, v_s_556_);
v___x_560_ = lean_apply_4(v_map_557_, lean_box(0), lean_box(0), v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f___redArg(lean_object* v_inst_561_, lean_object* v_init_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_map_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_map_564_ = lean_ctor_get(v_inst_561_, 0);
lean_inc(v_map_564_);
lean_dec_ref(v_inst_561_);
v___x_565_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_566_ = lean_apply_1(v_x_563_, v_init_562_);
v___x_567_ = lean_apply_4(v_map_564_, lean_box(0), lean_box(0), v___x_565_, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f(lean_object* v_00_u03c3_568_, lean_object* v_00_u03b1_569_, lean_object* v_m_570_, lean_object* v_00_u03b5_571_, lean_object* v_inst_572_, lean_object* v_init_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_map_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_map_575_ = lean_ctor_get(v_inst_572_, 0);
lean_inc(v_map_575_);
lean_dec_ref(v_inst_572_);
v___x_576_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_577_ = lean_apply_1(v_x_574_, v_init_573_);
v___x_578_ = lean_apply_4(v_map_575_, lean_box(0), lean_box(0), v___x_576_, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27___redArg(lean_object* v_inst_580_, lean_object* v_init_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_map_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_map_583_ = lean_ctor_get(v_inst_580_, 0);
lean_inc(v_map_583_);
lean_dec_ref(v_inst_580_);
v___x_584_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_585_ = lean_apply_1(v_x_582_, v_init_581_);
v___x_586_ = lean_apply_4(v_map_583_, lean_box(0), lean_box(0), v___x_584_, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27(lean_object* v_m_587_, lean_object* v_00_u03b5_588_, lean_object* v_00_u03c3_589_, lean_object* v_00_u03b1_590_, lean_object* v_inst_591_, lean_object* v_init_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_map_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_map_594_ = lean_ctor_get(v_inst_591_, 0);
lean_inc(v_map_594_);
lean_dec_ref(v_inst_591_);
v___x_595_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_596_ = lean_apply_1(v_x_593_, v_init_592_);
v___x_597_ = lean_apply_4(v_map_594_, lean_box(0), lean_box(0), v___x_595_, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg___lam__0(lean_object* v_toPure_598_, lean_object* v_h_599_, lean_object* v_____do__lift_600_){
_start:
{
if (lean_obj_tag(v_____do__lift_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_h_599_);
v_a_601_ = lean_ctor_get(v_____do__lift_600_, 0);
v_a_602_ = lean_ctor_get(v_____do__lift_600_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_____do__lift_600_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_____do__lift_600_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v_____do__lift_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_602_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_apply_2(v_toPure_598_, lean_box(0), v___x_607_);
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___x_613_; 
lean_dec(v_toPure_598_);
v_a_611_ = lean_ctor_get(v_____do__lift_600_, 0);
lean_inc(v_a_611_);
v_a_612_ = lean_ctor_get(v_____do__lift_600_, 1);
lean_inc(v_a_612_);
lean_dec_ref_known(v_____do__lift_600_, 2);
v___x_613_ = lean_apply_2(v_h_599_, v_a_611_, v_a_612_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg(lean_object* v_inst_614_, lean_object* v_x_615_, lean_object* v_h_616_, lean_object* v_s_617_){
_start:
{
lean_object* v_toApplicative_618_; lean_object* v_toBind_619_; lean_object* v_toPure_620_; lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_623_; 
v_toApplicative_618_ = lean_ctor_get(v_inst_614_, 0);
lean_inc_ref(v_toApplicative_618_);
v_toBind_619_ = lean_ctor_get(v_inst_614_, 1);
lean_inc(v_toBind_619_);
lean_dec_ref(v_inst_614_);
v_toPure_620_ = lean_ctor_get(v_toApplicative_618_, 1);
lean_inc(v_toPure_620_);
lean_dec_ref(v_toApplicative_618_);
v___x_621_ = lean_apply_1(v_x_615_, v_s_617_);
v___f_622_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_622_, 0, v_toPure_620_);
lean_closure_set(v___f_622_, 1, v_h_616_);
v___x_623_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_621_, v___f_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions(lean_object* v_m_624_, lean_object* v_00_u03b5_625_, lean_object* v_00_u03c3_626_, lean_object* v_00_u03b1_627_, lean_object* v_inst_628_, lean_object* v_x_629_, lean_object* v_h_630_, lean_object* v_s_631_){
_start:
{
lean_object* v_toApplicative_632_; lean_object* v_toBind_633_; lean_object* v_toPure_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; 
v_toApplicative_632_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toApplicative_632_);
v_toBind_633_ = lean_ctor_get(v_inst_628_, 1);
lean_inc(v_toBind_633_);
lean_dec_ref(v_inst_628_);
v_toPure_634_ = lean_ctor_get(v_toApplicative_632_, 1);
lean_inc(v_toPure_634_);
lean_dec_ref(v_toApplicative_632_);
v___x_635_ = lean_apply_1(v_x_629_, v_s_631_);
v___f_636_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_636_, 0, v_toPure_634_);
lean_closure_set(v___f_636_, 1, v_h_630_);
v___x_637_ = lean_apply_4(v_toBind_633_, lean_box(0), lean_box(0), v___x_635_, v___f_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg___lam__0(lean_object* v_s_638_, lean_object* v_toPure_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_a_640_);
lean_ctor_set(v___x_641_, 1, v_s_638_);
v___x_642_ = lean_apply_2(v_toPure_639_, lean_box(0), v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg(lean_object* v_inst_643_, lean_object* v_x_644_, lean_object* v_s_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v_toPure_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_643_, 0);
lean_inc_ref(v_toApplicative_646_);
v_toBind_647_ = lean_ctor_get(v_inst_643_, 1);
lean_inc(v_toBind_647_);
lean_dec_ref(v_inst_643_);
v_toPure_648_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_648_);
lean_dec_ref(v_toApplicative_646_);
v___f_649_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_649_, 0, v_s_645_);
lean_closure_set(v___f_649_, 1, v_toPure_648_);
v___x_650_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v_x_644_, v___f_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift(lean_object* v_m_651_, lean_object* v_00_u03b5_652_, lean_object* v_00_u03c3_653_, lean_object* v_00_u03b1_654_, lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v_s_657_){
_start:
{
lean_object* v_toApplicative_658_; lean_object* v_toBind_659_; lean_object* v_toPure_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v_toApplicative_658_ = lean_ctor_get(v_inst_655_, 0);
lean_inc_ref(v_toApplicative_658_);
v_toBind_659_ = lean_ctor_get(v_inst_655_, 1);
lean_inc(v_toBind_659_);
lean_dec_ref(v_inst_655_);
v_toPure_660_ = lean_ctor_get(v_toApplicative_658_, 1);
lean_inc(v_toPure_660_);
lean_dec_ref(v_toApplicative_658_);
v___f_661_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_661_, 0, v_s_657_);
lean_closure_set(v___f_661_, 1, v_toPure_660_);
v___x_662_ = lean_apply_4(v_toBind_659_, lean_box(0), lean_box(0), v_x_656_, v___f_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v___y_663_, lean_object* v_toPure_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_665_);
lean_ctor_set(v___x_666_, 1, v___y_663_);
v___x_667_ = lean_apply_2(v_toPure_664_, lean_box(0), v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object* v_inst_668_, lean_object* v_00_u03b1_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_toApplicative_672_; lean_object* v_toBind_673_; lean_object* v_toPure_674_; lean_object* v___f_675_; lean_object* v___x_676_; 
v_toApplicative_672_ = lean_ctor_get(v_inst_668_, 0);
lean_inc_ref(v_toApplicative_672_);
v_toBind_673_ = lean_ctor_get(v_inst_668_, 1);
lean_inc(v_toBind_673_);
lean_dec_ref(v_inst_668_);
v_toPure_674_ = lean_ctor_get(v_toApplicative_672_, 1);
lean_inc(v_toPure_674_);
lean_dec_ref(v_toApplicative_672_);
v___f_675_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_675_, 0, v___y_671_);
lean_closure_set(v___f_675_, 1, v_toPure_674_);
v___x_676_ = lean_apply_4(v_toBind_673_, lean_box(0), lean_box(0), v___y_670_, v___f_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg(lean_object* v_inst_677_){
_start:
{
lean_object* v___f_678_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_678_, 0, v_inst_677_);
return v___f_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad(lean_object* v_m_679_, lean_object* v_00_u03b5_680_, lean_object* v_00_u03c3_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v___f_683_; 
v___f_683_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_683_, 0, v_inst_682_);
return v___f_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure___redArg(lean_object* v_inst_684_, lean_object* v_a_685_, lean_object* v_s_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_a_685_);
lean_ctor_set(v___x_687_, 1, v_s_686_);
v___x_688_ = lean_apply_2(v_inst_684_, lean_box(0), v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure(lean_object* v_00_u03b5_689_, lean_object* v_00_u03c3_690_, lean_object* v_00_u03b1_691_, lean_object* v_m_692_, lean_object* v_inst_693_, lean_object* v_a_694_, lean_object* v_s_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_a_694_);
lean_ctor_set(v___x_696_, 1, v_s_695_);
v___x_697_ = lean_apply_2(v_inst_693_, lean_box(0), v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object* v_inst_698_, lean_object* v_00_u03b1_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___y_700_);
lean_ctor_set(v___x_702_, 1, v___y_701_);
v___x_703_ = lean_apply_2(v_inst_698_, lean_box(0), v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg(lean_object* v_inst_704_){
_start:
{
lean_object* v___f_705_; 
v___f_705_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_705_, 0, v_inst_704_);
return v___f_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure(lean_object* v_00_u03b5_706_, lean_object* v_00_u03c3_707_, lean_object* v_m_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___f_710_; 
v___f_710_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_710_, 0, v_inst_709_);
return v___f_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg___lam__0(lean_object* v_f_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_a_713_ = lean_ctor_get(v_x_712_, 0);
v_a_714_ = lean_ctor_get(v_x_712_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v_x_712_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_inc(v_a_713_);
lean_dec(v_x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_apply_1(v_f_711_, v_a_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_a_714_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_f_711_);
v_a_723_ = lean_ctor_get(v_x_712_, 0);
v_a_724_ = lean_ctor_get(v_x_712_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v_x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_inc(v_a_723_);
lean_dec(v_x_712_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_723_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg(lean_object* v_inst_732_, lean_object* v_f_733_, lean_object* v_x_734_, lean_object* v_s_735_){
_start:
{
lean_object* v_map_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_map_736_ = lean_ctor_get(v_inst_732_, 0);
lean_inc(v_map_736_);
lean_dec_ref(v_inst_732_);
v___f_737_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_737_, 0, v_f_733_);
v___x_738_ = lean_apply_1(v_x_734_, v_s_735_);
v___x_739_ = lean_apply_4(v_map_736_, lean_box(0), lean_box(0), v___f_737_, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map(lean_object* v_00_u03b5_740_, lean_object* v_00_u03c3_741_, lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_m_744_, lean_object* v_inst_745_, lean_object* v_f_746_, lean_object* v_x_747_, lean_object* v_s_748_){
_start:
{
lean_object* v_map_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_map_749_ = lean_ctor_get(v_inst_745_, 0);
lean_inc(v_map_749_);
lean_dec_ref(v_inst_745_);
v___f_750_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_750_, 0, v_f_746_);
v___x_751_ = lean_apply_1(v_x_747_, v_s_748_);
v___x_752_ = lean_apply_4(v_map_749_, lean_box(0), lean_box(0), v___f_750_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__0(lean_object* v___y_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_a_755_ = lean_ctor_get(v_x_754_, 0);
v_a_756_ = lean_ctor_get(v_x_754_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_754_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v_x_754_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_inc(v_a_755_);
lean_dec(v_x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_apply_1(v___y_753_, v_a_755_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_756_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___y_753_);
v_a_765_ = lean_ctor_get(v_x_754_, 0);
v_a_766_ = lean_ctor_get(v_x_754_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_754_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v_x_754_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v_x_754_);
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
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
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
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__1(lean_object* v_inst_774_, lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_map_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_map_780_ = lean_ctor_get(v_inst_774_, 0);
lean_inc(v_map_780_);
lean_dec_ref(v_inst_774_);
v___f_781_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__0), 2, 1);
lean_closure_set(v___f_781_, 0, v___y_777_);
v___x_782_ = lean_apply_1(v___y_778_, v___y_779_);
v___x_783_ = lean_apply_4(v_map_780_, lean_box(0), lean_box(0), v___f_781_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__2(lean_object* v___f_784_, lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_790_, 0, lean_box(0));
lean_closure_set(v___x_790_, 1, lean_box(0));
lean_closure_set(v___x_790_, 2, v___y_787_);
v___x_791_ = lean_apply_5(v___f_784_, lean_box(0), lean_box(0), v___x_790_, v___y_788_, v___y_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object* v_inst_792_){
_start:
{
lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; 
v___f_793_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__1), 6, 1);
lean_closure_set(v___f_793_, 0, v_inst_792_);
lean_inc_ref(v___f_793_);
v___f_794_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__2), 6, 1);
lean_closure_set(v___f_794_, 0, v___f_793_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___f_793_);
lean_ctor_set(v___x_795_, 1, v___f_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor(lean_object* v_00_u03b5_796_, lean_object* v_00_u03c3_797_, lean_object* v_m_798_, lean_object* v_inst_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lake_EStateT_instFunctor___redArg(v_inst_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg___lam__0(lean_object* v_f_801_, lean_object* v_toPure_802_, lean_object* v_____do__lift_803_){
_start:
{
if (lean_obj_tag(v_____do__lift_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v___x_806_; 
lean_dec(v_toPure_802_);
v_a_804_ = lean_ctor_get(v_____do__lift_803_, 0);
lean_inc(v_a_804_);
v_a_805_ = lean_ctor_get(v_____do__lift_803_, 1);
lean_inc(v_a_805_);
lean_dec_ref_known(v_____do__lift_803_, 2);
v___x_806_ = lean_apply_2(v_f_801_, v_a_804_, v_a_805_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_f_801_);
v_a_807_ = lean_ctor_get(v_____do__lift_803_, 0);
v_a_808_ = lean_ctor_get(v_____do__lift_803_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_____do__lift_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_810_ = v_____do__lift_803_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_inc(v_a_807_);
lean_dec(v_____do__lift_803_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_807_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_808_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = lean_apply_2(v_toPure_802_, lean_box(0), v___x_813_);
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg(lean_object* v_inst_817_, lean_object* v_x_818_, lean_object* v_f_819_, lean_object* v_s_820_){
_start:
{
lean_object* v_toApplicative_821_; lean_object* v_toBind_822_; lean_object* v_toPure_823_; lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v_toApplicative_821_ = lean_ctor_get(v_inst_817_, 0);
lean_inc_ref(v_toApplicative_821_);
v_toBind_822_ = lean_ctor_get(v_inst_817_, 1);
lean_inc(v_toBind_822_);
lean_dec_ref(v_inst_817_);
v_toPure_823_ = lean_ctor_get(v_toApplicative_821_, 1);
lean_inc(v_toPure_823_);
lean_dec_ref(v_toApplicative_821_);
v___x_824_ = lean_apply_1(v_x_818_, v_s_820_);
v___f_825_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_825_, 0, v_f_819_);
lean_closure_set(v___f_825_, 1, v_toPure_823_);
v___x_826_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v___x_824_, v___f_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind(lean_object* v_00_u03b5_827_, lean_object* v_00_u03c3_828_, lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_m_831_, lean_object* v_inst_832_, lean_object* v_x_833_, lean_object* v_f_834_, lean_object* v_s_835_){
_start:
{
lean_object* v_toApplicative_836_; lean_object* v_toBind_837_; lean_object* v_toPure_838_; lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v___x_841_; 
v_toApplicative_836_ = lean_ctor_get(v_inst_832_, 0);
lean_inc_ref(v_toApplicative_836_);
v_toBind_837_ = lean_ctor_get(v_inst_832_, 1);
lean_inc(v_toBind_837_);
lean_dec_ref(v_inst_832_);
v_toPure_838_ = lean_ctor_get(v_toApplicative_836_, 1);
lean_inc(v_toPure_838_);
lean_dec_ref(v_toApplicative_836_);
v___x_839_ = lean_apply_1(v_x_833_, v_s_835_);
v___f_840_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_840_, 0, v_f_834_);
lean_closure_set(v___f_840_, 1, v_toPure_838_);
v___x_841_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_839_, v___f_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg___lam__0(lean_object* v_y_842_, lean_object* v_toPure_843_, lean_object* v_____do__lift_844_){
_start:
{
if (lean_obj_tag(v_____do__lift_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_toPure_843_);
v_a_845_ = lean_ctor_get(v_____do__lift_844_, 1);
lean_inc(v_a_845_);
lean_dec_ref_known(v_____do__lift_844_, 2);
v___x_846_ = lean_box(0);
v___x_847_ = lean_apply_2(v_y_842_, v___x_846_, v_a_845_);
return v___x_847_;
}
else
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_y_842_);
v_a_848_ = lean_ctor_get(v_____do__lift_844_, 0);
v_a_849_ = lean_ctor_get(v_____do__lift_844_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_____do__lift_844_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v_____do__lift_844_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_inc(v_a_848_);
lean_dec(v_____do__lift_844_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
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
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_848_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_a_849_);
v___x_854_ = v_reuseFailAlloc_856_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; 
v___x_855_ = lean_apply_2(v_toPure_843_, lean_box(0), v___x_854_);
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg(lean_object* v_inst_858_, lean_object* v_x_859_, lean_object* v_y_860_, lean_object* v_s_861_){
_start:
{
lean_object* v_toApplicative_862_; lean_object* v_toBind_863_; lean_object* v_toPure_864_; lean_object* v___x_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_858_, 0);
lean_inc_ref(v_toApplicative_862_);
v_toBind_863_ = lean_ctor_get(v_inst_858_, 1);
lean_inc(v_toBind_863_);
lean_dec_ref(v_inst_858_);
v_toPure_864_ = lean_ctor_get(v_toApplicative_862_, 1);
lean_inc(v_toPure_864_);
lean_dec_ref(v_toApplicative_862_);
v___x_865_ = lean_apply_1(v_x_859_, v_s_861_);
v___f_866_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_866_, 0, v_y_860_);
lean_closure_set(v___f_866_, 1, v_toPure_864_);
v___x_867_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v___x_865_, v___f_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight(lean_object* v_00_u03b5_868_, lean_object* v_00_u03c3_869_, lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_m_872_, lean_object* v_inst_873_, lean_object* v_x_874_, lean_object* v_y_875_, lean_object* v_s_876_){
_start:
{
lean_object* v_toApplicative_877_; lean_object* v_toBind_878_; lean_object* v_toPure_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___x_882_; 
v_toApplicative_877_ = lean_ctor_get(v_inst_873_, 0);
lean_inc_ref(v_toApplicative_877_);
v_toBind_878_ = lean_ctor_get(v_inst_873_, 1);
lean_inc(v_toBind_878_);
lean_dec_ref(v_inst_873_);
v_toPure_879_ = lean_ctor_get(v_toApplicative_877_, 1);
lean_inc(v_toPure_879_);
lean_dec_ref(v_toApplicative_877_);
v___x_880_ = lean_apply_1(v_x_874_, v_s_876_);
v___f_881_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_881_, 0, v_y_875_);
lean_closure_set(v___f_881_, 1, v_toPure_879_);
v___x_882_ = lean_apply_4(v_toBind_878_, lean_box(0), lean_box(0), v___x_880_, v___f_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__0(lean_object* v___y_883_, lean_object* v_toPure_884_, lean_object* v_____do__lift_885_){
_start:
{
if (lean_obj_tag(v_____do__lift_885_) == 0)
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v___x_888_; 
lean_dec(v_toPure_884_);
v_a_886_ = lean_ctor_get(v_____do__lift_885_, 0);
lean_inc(v_a_886_);
v_a_887_ = lean_ctor_get(v_____do__lift_885_, 1);
lean_inc(v_a_887_);
lean_dec_ref_known(v_____do__lift_885_, 2);
v___x_888_ = lean_apply_2(v___y_883_, v_a_886_, v_a_887_);
return v___x_888_;
}
else
{
lean_object* v_a_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
lean_dec(v___y_883_);
v_a_889_ = lean_ctor_get(v_____do__lift_885_, 0);
v_a_890_ = lean_ctor_get(v_____do__lift_885_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_____do__lift_885_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v_____do__lift_885_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_inc(v_a_889_);
lean_dec(v_____do__lift_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_890_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = lean_apply_2(v_toPure_884_, lean_box(0), v___x_895_);
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object* v_toPure_899_, lean_object* v_toBind_900_, lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
v___x_906_ = lean_apply_1(v___y_903_, v___y_905_);
v___f_907_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_907_, 0, v___y_904_);
lean_closure_set(v___f_907_, 1, v_toPure_899_);
v___x_908_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_906_, v___f_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__2(lean_object* v___y_909_, lean_object* v_toPure_910_, lean_object* v_____do__lift_911_){
_start:
{
if (lean_obj_tag(v_____do__lift_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_toPure_910_);
v_a_912_ = lean_ctor_get(v_____do__lift_911_, 1);
lean_inc(v_a_912_);
lean_dec_ref_known(v_____do__lift_911_, 2);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_2(v___y_909_, v___x_913_, v_a_912_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___y_909_);
v_a_915_ = lean_ctor_get(v_____do__lift_911_, 0);
v_a_916_ = lean_ctor_get(v_____do__lift_911_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_____do__lift_911_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v_____do__lift_911_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_inc(v_a_915_);
lean_dec(v_____do__lift_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_915_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_a_916_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_apply_2(v_toPure_910_, lean_box(0), v___x_921_);
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object* v_toPure_925_, lean_object* v_toBind_926_, lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___x_934_; 
v___x_932_ = lean_apply_1(v___y_929_, v___y_931_);
v___f_933_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_933_, 0, v___y_930_);
lean_closure_set(v___f_933_, 1, v_toPure_925_);
v___x_934_ = lean_apply_4(v_toBind_926_, lean_box(0), lean_box(0), v___x_932_, v___f_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6(lean_object* v_a_935_, lean_object* v_toPure_936_, lean_object* v_x_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_a_935_);
lean_ctor_set(v___x_939_, 1, v___y_938_);
v___x_940_ = lean_apply_2(v_toPure_936_, lean_box(0), v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6___boxed(lean_object* v_a_941_, lean_object* v_toPure_942_, lean_object* v_x_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lake_EStateT_instMonad___redArg___lam__6(v_a_941_, v_toPure_942_, v_x_943_, v___y_944_);
lean_dec(v_x_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__4(lean_object* v_toPure_946_, lean_object* v_y_947_, lean_object* v___f_948_, lean_object* v_a_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___f_951_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_951_, 0, v_a_949_);
lean_closure_set(v___f_951_, 1, v_toPure_946_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_apply_1(v_y_947_, v___x_952_);
v___x_954_ = lean_apply_5(v___f_948_, lean_box(0), lean_box(0), v___x_953_, v___f_951_, v___y_950_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object* v_toPure_955_, lean_object* v___f_956_, lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___f_962_; lean_object* v___x_963_; 
lean_inc(v___f_956_);
v___f_962_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__4), 5, 3);
lean_closure_set(v___f_962_, 0, v_toPure_955_);
lean_closure_set(v___f_962_, 1, v_y_960_);
lean_closure_set(v___f_962_, 2, v___f_956_);
v___x_963_ = lean_apply_5(v___f_956_, lean_box(0), lean_box(0), v_x_959_, v___f_962_, v___y_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__7(lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_a_966_ = lean_ctor_get(v_x_965_, 0);
v_a_967_ = lean_ctor_get(v_x_965_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_inc(v_a_966_);
lean_dec(v_x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_apply_1(v_a_964_, v_a_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_a_964_);
v_a_976_ = lean_ctor_get(v_x_965_, 0);
v_a_977_ = lean_ctor_get(v_x_965_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v_x_965_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_inc(v_a_976_);
lean_dec(v_x_965_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_976_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__8(lean_object* v_toFunctor_985_, lean_object* v_x_986_, lean_object* v_toPure_987_, lean_object* v_____do__lift_988_){
_start:
{
if (lean_obj_tag(v_____do__lift_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v_map_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_toPure_987_);
v_a_989_ = lean_ctor_get(v_____do__lift_988_, 0);
lean_inc(v_a_989_);
v_a_990_ = lean_ctor_get(v_____do__lift_988_, 1);
lean_inc(v_a_990_);
lean_dec_ref_known(v_____do__lift_988_, 2);
v_map_991_ = lean_ctor_get(v_toFunctor_985_, 0);
lean_inc(v_map_991_);
lean_dec_ref(v_toFunctor_985_);
v___f_992_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__7), 2, 1);
lean_closure_set(v___f_992_, 0, v_a_989_);
v___x_993_ = lean_box(0);
v___x_994_ = lean_apply_2(v_x_986_, v___x_993_, v_a_990_);
v___x_995_ = lean_apply_4(v_map_991_, lean_box(0), lean_box(0), v___f_992_, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_x_986_);
lean_dec_ref(v_toFunctor_985_);
v_a_996_ = lean_ctor_get(v_____do__lift_988_, 0);
v_a_997_ = lean_ctor_get(v_____do__lift_988_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_____do__lift_988_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v_____do__lift_988_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_inc(v_a_996_);
lean_dec(v_____do__lift_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_apply_2(v_toPure_987_, lean_box(0), v___x_1002_);
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object* v_toFunctor_1006_, lean_object* v_toPure_1007_, lean_object* v_toBind_1008_, lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_f_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1006_);
lean_closure_set(v___f_1014_, 1, v_x_1012_);
lean_closure_set(v___f_1014_, 2, v_toPure_1007_);
v___x_1015_ = lean_apply_1(v_f_1011_, v___y_1013_);
v___x_1016_ = lean_apply_4(v_toBind_1008_, lean_box(0), lean_box(0), v___x_1015_, v___f_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg(lean_object* v_inst_1017_){
_start:
{
lean_object* v_toApplicative_1018_; lean_object* v_toBind_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1044_; 
v_toApplicative_1018_ = lean_ctor_get(v_inst_1017_, 0);
v_toBind_1019_ = lean_ctor_get(v_inst_1017_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_inst_1017_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1021_ = v_inst_1017_;
v_isShared_1022_ = v_isSharedCheck_1044_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toBind_1019_);
lean_inc(v_toApplicative_1018_);
lean_dec(v_inst_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1044_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_toFunctor_1023_; lean_object* v_toPure_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1040_; 
v_toFunctor_1023_ = lean_ctor_get(v_toApplicative_1018_, 0);
v_toPure_1024_ = lean_ctor_get(v_toApplicative_1018_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_toApplicative_1018_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1041_ = lean_ctor_get(v_toApplicative_1018_, 4);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_toApplicative_1018_, 3);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_toApplicative_1018_, 2);
lean_dec(v_unused_1043_);
v___x_1026_ = v_toApplicative_1018_;
v_isShared_1027_ = v_isSharedCheck_1040_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_toPure_1024_);
lean_inc(v_toFunctor_1023_);
lean_dec(v_toApplicative_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1040_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___x_1035_; 
lean_inc_n(v_toBind_1019_, 2);
lean_inc_n(v_toPure_1024_, 4);
v___f_1028_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1028_, 0, v_toPure_1024_);
lean_closure_set(v___f_1028_, 1, v_toBind_1019_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1029_, 0, v_toPure_1024_);
lean_closure_set(v___f_1029_, 1, v_toBind_1019_);
lean_inc_ref(v___f_1028_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1030_, 0, v_toPure_1024_);
lean_closure_set(v___f_1030_, 1, v___f_1028_);
lean_inc_ref(v_toFunctor_1023_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1031_, 0, v_toFunctor_1023_);
lean_closure_set(v___f_1031_, 1, v_toPure_1024_);
lean_closure_set(v___f_1031_, 2, v_toBind_1019_);
v___x_1032_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1023_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1033_, 0, v_toPure_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 4, v___f_1029_);
lean_ctor_set(v___x_1026_, 3, v___f_1030_);
lean_ctor_set(v___x_1026_, 2, v___f_1031_);
lean_ctor_set(v___x_1026_, 1, v___f_1033_);
lean_ctor_set(v___x_1026_, 0, v___x_1032_);
v___x_1035_ = v___x_1026_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___f_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___f_1031_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___f_1029_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___f_1028_);
lean_ctor_set(v___x_1021_, 0, v___x_1035_);
v___x_1037_ = v___x_1021_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___f_1028_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad(lean_object* v_00_u03b5_1045_, lean_object* v_00_u03c3_1046_, lean_object* v_m_1047_, lean_object* v_inst_1048_){
_start:
{
lean_object* v_toApplicative_1049_; lean_object* v_toBind_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1075_; 
v_toApplicative_1049_ = lean_ctor_get(v_inst_1048_, 0);
v_toBind_1050_ = lean_ctor_get(v_inst_1048_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_inst_1048_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1052_ = v_inst_1048_;
v_isShared_1053_ = v_isSharedCheck_1075_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_toBind_1050_);
lean_inc(v_toApplicative_1049_);
lean_dec(v_inst_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1075_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_toFunctor_1054_; lean_object* v_toPure_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1071_; 
v_toFunctor_1054_ = lean_ctor_get(v_toApplicative_1049_, 0);
v_toPure_1055_ = lean_ctor_get(v_toApplicative_1049_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_toApplicative_1049_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; 
v_unused_1072_ = lean_ctor_get(v_toApplicative_1049_, 4);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_toApplicative_1049_, 3);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_toApplicative_1049_, 2);
lean_dec(v_unused_1074_);
v___x_1057_ = v_toApplicative_1049_;
v_isShared_1058_ = v_isSharedCheck_1071_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_toPure_1055_);
lean_inc(v_toFunctor_1054_);
lean_dec(v_toApplicative_1049_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1071_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___x_1066_; 
lean_inc_n(v_toBind_1050_, 2);
lean_inc_n(v_toPure_1055_, 4);
v___f_1059_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1059_, 0, v_toPure_1055_);
lean_closure_set(v___f_1059_, 1, v_toBind_1050_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1060_, 0, v_toPure_1055_);
lean_closure_set(v___f_1060_, 1, v_toBind_1050_);
lean_inc_ref(v___f_1059_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1061_, 0, v_toPure_1055_);
lean_closure_set(v___f_1061_, 1, v___f_1059_);
lean_inc_ref(v_toFunctor_1054_);
v___f_1062_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1062_, 0, v_toFunctor_1054_);
lean_closure_set(v___f_1062_, 1, v_toPure_1055_);
lean_closure_set(v___f_1062_, 2, v_toBind_1050_);
v___x_1063_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1054_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1064_, 0, v_toPure_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 4, v___f_1060_);
lean_ctor_set(v___x_1057_, 3, v___f_1061_);
lean_ctor_set(v___x_1057_, 2, v___f_1062_);
lean_ctor_set(v___x_1057_, 1, v___f_1064_);
lean_ctor_set(v___x_1057_, 0, v___x_1063_);
v___x_1066_ = v___x_1057_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___f_1062_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___f_1061_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___f_1060_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___f_1059_);
lean_ctor_set(v___x_1052_, 0, v___x_1066_);
v___x_1068_ = v___x_1052_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1059_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___redArg(lean_object* v_inst_1076_, lean_object* v_s_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_s_1077_);
v___x_1080_ = lean_apply_2(v_inst_1076_, lean_box(0), v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set(lean_object* v_00_u03b5_1081_, lean_object* v_00_u03c3_1082_, lean_object* v_m_1083_, lean_object* v_inst_1084_, lean_object* v_s_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_s_1085_);
v___x_1089_ = lean_apply_2(v_inst_1084_, lean_box(0), v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___boxed(lean_object* v_00_u03b5_1090_, lean_object* v_00_u03c3_1091_, lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_s_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lake_EStateT_set(v_00_u03b5_1090_, v_00_u03c3_1091_, v_m_1092_, v_inst_1093_, v_s_1094_, v_x_1095_);
lean_dec(v_x_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get___redArg(lean_object* v_inst_1097_, lean_object* v_s_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_inc(v_s_1098_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_s_1098_);
lean_ctor_set(v___x_1099_, 1, v_s_1098_);
v___x_1100_ = lean_apply_2(v_inst_1097_, lean_box(0), v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get(lean_object* v_00_u03b5_1101_, lean_object* v_00_u03c3_1102_, lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_s_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc(v_s_1105_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_s_1105_);
lean_ctor_set(v___x_1106_, 1, v_s_1105_);
v___x_1107_ = lean_apply_2(v_inst_1104_, lean_box(0), v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet___redArg(lean_object* v_inst_1108_, lean_object* v_f_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v___x_1111_ = lean_apply_1(v_f_1109_, v_s_1110_);
v_fst_1112_ = lean_ctor_get(v___x_1111_, 0);
v_snd_1113_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v___x_1111_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_inc(v_fst_1112_);
lean_dec(v___x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_fst_1112_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_snd_1113_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_apply_2(v_inst_1108_, lean_box(0), v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet(lean_object* v_00_u03b5_1122_, lean_object* v_00_u03c3_1123_, lean_object* v_00_u03b1_1124_, lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_f_1127_, lean_object* v_s_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v___x_1129_ = lean_apply_1(v_f_1127_, v_s_1128_);
v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
v_snd_1131_ = lean_ctor_get(v___x_1129_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
lean_dec(v___x_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_fst_1130_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_snd_1131_);
v___x_1136_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_apply_2(v_inst_1126_, lean_box(0), v___x_1136_);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(lean_object* v_inst_1140_, lean_object* v_00_u03b1_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v___x_1144_ = lean_apply_1(v___y_1142_, v___y_1143_);
v_fst_1145_ = lean_ctor_get(v___x_1144_, 0);
v_snd_1146_ = lean_ctor_get(v___x_1144_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___x_1144_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1145_);
lean_dec(v___x_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_fst_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_snd_1146_);
v___x_1151_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_apply_2(v_inst_1140_, lean_box(0), v___x_1151_);
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object* v_inst_1155_){
_start:
{
lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_n(v_inst_1155_, 2);
v___f_1156_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1156_, 0, v_inst_1155_);
v___x_1157_ = lean_alloc_closure((void*)(l_Lake_EStateT_get), 5, 4);
lean_closure_set(v___x_1157_, 0, lean_box(0));
lean_closure_set(v___x_1157_, 1, lean_box(0));
lean_closure_set(v___x_1157_, 2, lean_box(0));
lean_closure_set(v___x_1157_, 3, v_inst_1155_);
v___x_1158_ = lean_alloc_closure((void*)(l_Lake_EStateT_set___boxed), 6, 4);
lean_closure_set(v___x_1158_, 0, lean_box(0));
lean_closure_set(v___x_1158_, 1, lean_box(0));
lean_closure_set(v___x_1158_, 2, lean_box(0));
lean_closure_set(v___x_1158_, 3, v_inst_1155_);
v___x_1159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
lean_ctor_set(v___x_1159_, 2, v___f_1156_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure(lean_object* v_00_u03b5_1160_, lean_object* v_00_u03c3_1161_, lean_object* v_m_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw___redArg(lean_object* v_inst_1165_, lean_object* v_e_1166_, lean_object* v_s_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_e_1166_);
lean_ctor_set(v___x_1168_, 1, v_s_1167_);
v___x_1169_ = lean_apply_2(v_inst_1165_, lean_box(0), v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw(lean_object* v_00_u03b5_1170_, lean_object* v_00_u03c3_1171_, lean_object* v_00_u03b1_1172_, lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_e_1175_, lean_object* v_s_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_e_1175_);
lean_ctor_set(v___x_1177_, 1, v_s_1176_);
v___x_1178_ = lean_apply_2(v_inst_1174_, lean_box(0), v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg___lam__0(lean_object* v_toPure_1179_, lean_object* v_handle_1180_, lean_object* v_____do__lift_1181_){
_start:
{
if (lean_obj_tag(v_____do__lift_1181_) == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_handle_1180_);
v___x_1182_ = lean_apply_2(v_toPure_1179_, lean_box(0), v_____do__lift_1181_);
return v___x_1182_;
}
else
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v___x_1185_; 
lean_dec(v_toPure_1179_);
v_a_1183_ = lean_ctor_get(v_____do__lift_1181_, 0);
lean_inc(v_a_1183_);
v_a_1184_ = lean_ctor_get(v_____do__lift_1181_, 1);
lean_inc(v_a_1184_);
lean_dec_ref_known(v_____do__lift_1181_, 2);
v___x_1185_ = lean_apply_2(v_handle_1180_, v_a_1183_, v_a_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg(lean_object* v_inst_1186_, lean_object* v_x_1187_, lean_object* v_handle_1188_, lean_object* v_s_1189_){
_start:
{
lean_object* v_toApplicative_1190_; lean_object* v_toBind_1191_; lean_object* v_toPure_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v_toApplicative_1190_ = lean_ctor_get(v_inst_1186_, 0);
lean_inc_ref(v_toApplicative_1190_);
v_toBind_1191_ = lean_ctor_get(v_inst_1186_, 1);
lean_inc(v_toBind_1191_);
lean_dec_ref(v_inst_1186_);
v_toPure_1192_ = lean_ctor_get(v_toApplicative_1190_, 1);
lean_inc(v_toPure_1192_);
lean_dec_ref(v_toApplicative_1190_);
v___x_1193_ = lean_apply_1(v_x_1187_, v_s_1189_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1194_, 0, v_toPure_1192_);
lean_closure_set(v___f_1194_, 1, v_handle_1188_);
v___x_1195_ = lean_apply_4(v_toBind_1191_, lean_box(0), lean_box(0), v___x_1193_, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch(lean_object* v_00_u03b5_1196_, lean_object* v_00_u03c3_1197_, lean_object* v_00_u03b1_1198_, lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_x_1201_, lean_object* v_handle_1202_, lean_object* v_s_1203_){
_start:
{
lean_object* v_toApplicative_1204_; lean_object* v_toBind_1205_; lean_object* v_toPure_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v_toApplicative_1204_ = lean_ctor_get(v_inst_1200_, 0);
lean_inc_ref(v_toApplicative_1204_);
v_toBind_1205_ = lean_ctor_get(v_inst_1200_, 1);
lean_inc(v_toBind_1205_);
lean_dec_ref(v_inst_1200_);
v_toPure_1206_ = lean_ctor_get(v_toApplicative_1204_, 1);
lean_inc(v_toPure_1206_);
lean_dec_ref(v_toApplicative_1204_);
v___x_1207_ = lean_apply_1(v_x_1201_, v_s_1203_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1208_, 0, v_toPure_1206_);
lean_closure_set(v___f_1208_, 1, v_handle_1202_);
v___x_1209_ = lean_apply_4(v_toBind_1205_, lean_box(0), lean_box(0), v___x_1207_, v___f_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(lean_object* v_toPure_1210_, lean_object* v___y_1211_, lean_object* v_____do__lift_1212_){
_start:
{
if (lean_obj_tag(v_____do__lift_1212_) == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___y_1211_);
v___x_1213_ = lean_apply_2(v_toPure_1210_, lean_box(0), v_____do__lift_1212_);
return v___x_1213_;
}
else
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v___x_1216_; 
lean_dec(v_toPure_1210_);
v_a_1214_ = lean_ctor_get(v_____do__lift_1212_, 0);
lean_inc(v_a_1214_);
v_a_1215_ = lean_ctor_get(v_____do__lift_1212_, 1);
lean_inc(v_a_1215_);
lean_dec_ref_known(v_____do__lift_1212_, 2);
v___x_1216_ = lean_apply_2(v___y_1211_, v_a_1214_, v_a_1215_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(lean_object* v_toPure_1217_, lean_object* v_toBind_1218_, lean_object* v_00_u03b1_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_apply_1(v___y_1220_, v___y_1222_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1224_, 0, v_toPure_1217_);
lean_closure_set(v___f_1224_, 1, v___y_1221_);
v___x_1225_ = lean_apply_4(v_toBind_1218_, lean_box(0), lean_box(0), v___x_1223_, v___f_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(lean_object* v_toPure_1226_, lean_object* v_00_u03b1_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1228_);
lean_ctor_set(v___x_1230_, 1, v___y_1229_);
v___x_1231_ = lean_apply_2(v_toPure_1226_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(lean_object* v_inst_1232_){
_start:
{
lean_object* v_toApplicative_1233_; lean_object* v_toBind_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1244_; 
v_toApplicative_1233_ = lean_ctor_get(v_inst_1232_, 0);
v_toBind_1234_ = lean_ctor_get(v_inst_1232_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_inst_1232_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1236_ = v_inst_1232_;
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_toBind_1234_);
lean_inc(v_toApplicative_1233_);
lean_dec(v_inst_1232_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_toPure_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1242_; 
v_toPure_1238_ = lean_ctor_get(v_toApplicative_1233_, 1);
lean_inc_n(v_toPure_1238_, 2);
lean_dec_ref(v_toApplicative_1233_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1), 6, 2);
lean_closure_set(v___f_1239_, 0, v_toPure_1238_);
lean_closure_set(v___f_1239_, 1, v_toBind_1234_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2), 4, 1);
lean_closure_set(v___f_1240_, 0, v_toPure_1238_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___f_1239_);
lean_ctor_set(v___x_1236_, 0, v___f_1240_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___f_1240_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1239_);
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
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad(lean_object* v_00_u03b5_1245_, lean_object* v_00_u03c3_1246_, lean_object* v_m_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg___lam__0(lean_object* v_toPure_1250_, lean_object* v_x_u2082_1251_, lean_object* v_____do__lift_1252_){
_start:
{
if (lean_obj_tag(v_____do__lift_1252_) == 0)
{
lean_object* v___x_1253_; 
lean_dec(v_x_u2082_1251_);
v___x_1253_ = lean_apply_2(v_toPure_1250_, lean_box(0), v_____do__lift_1252_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_toPure_1250_);
v_a_1254_ = lean_ctor_get(v_____do__lift_1252_, 1);
lean_inc(v_a_1254_);
lean_dec_ref_known(v_____do__lift_1252_, 2);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_apply_2(v_x_u2082_1251_, v___x_1255_, v_a_1254_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg(lean_object* v_inst_1257_, lean_object* v_x_u2081_1258_, lean_object* v_x_u2082_1259_, lean_object* v_s_1260_){
_start:
{
lean_object* v_toApplicative_1261_; lean_object* v_toBind_1262_; lean_object* v_toPure_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
v_toApplicative_1261_ = lean_ctor_get(v_inst_1257_, 0);
lean_inc_ref(v_toApplicative_1261_);
v_toBind_1262_ = lean_ctor_get(v_inst_1257_, 1);
lean_inc(v_toBind_1262_);
lean_dec_ref(v_inst_1257_);
v_toPure_1263_ = lean_ctor_get(v_toApplicative_1261_, 1);
lean_inc(v_toPure_1263_);
lean_dec_ref(v_toApplicative_1261_);
v___x_1264_ = lean_apply_1(v_x_u2081_1258_, v_s_1260_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1265_, 0, v_toPure_1263_);
lean_closure_set(v___f_1265_, 1, v_x_u2082_1259_);
v___x_1266_ = lean_apply_4(v_toBind_1262_, lean_box(0), lean_box(0), v___x_1264_, v___f_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse(lean_object* v_00_u03b5_1267_, lean_object* v_00_u03c3_1268_, lean_object* v_00_u03b1_1269_, lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_x_u2081_1272_, lean_object* v_x_u2082_1273_, lean_object* v_s_1274_){
_start:
{
lean_object* v_toApplicative_1275_; lean_object* v_toBind_1276_; lean_object* v_toPure_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_ref(v_toApplicative_1275_);
v_toBind_1276_ = lean_ctor_get(v_inst_1271_, 1);
lean_inc(v_toBind_1276_);
lean_dec_ref(v_inst_1271_);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1275_, 1);
lean_inc(v_toPure_1277_);
lean_dec_ref(v_toApplicative_1275_);
v___x_1278_ = lean_apply_1(v_x_u2081_1272_, v_s_1274_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1279_, 0, v_toPure_1277_);
lean_closure_set(v___f_1279_, 1, v_x_u2082_1273_);
v___x_1280_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v___x_1278_, v___f_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad___redArg(lean_object* v_inst_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1282_, 0, lean_box(0));
lean_closure_set(v___x_1282_, 1, lean_box(0));
lean_closure_set(v___x_1282_, 2, lean_box(0));
lean_closure_set(v___x_1282_, 3, lean_box(0));
lean_closure_set(v___x_1282_, 4, v_inst_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad(lean_object* v_00_u03b5_1283_, lean_object* v_00_u03c3_1284_, lean_object* v_00_u03b1_1285_, lean_object* v_m_1286_, lean_object* v_inst_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1288_, 0, lean_box(0));
lean_closure_set(v___x_1288_, 1, lean_box(0));
lean_closure_set(v___x_1288_, 2, lean_box(0));
lean_closure_set(v___x_1288_, 3, lean_box(0));
lean_closure_set(v___x_1288_, 4, v_inst_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg___lam__0(lean_object* v_f_1289_, lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_f_1289_);
v_a_1291_ = lean_ctor_get(v_x_1290_, 0);
v_a_1292_ = lean_ctor_get(v_x_1290_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v_x_1290_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_inc(v_a_1291_);
lean_dec(v_x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1291_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_a_1300_ = lean_ctor_get(v_x_1290_, 0);
v_a_1301_ = lean_ctor_get(v_x_1290_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1290_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1303_ = v_x_1290_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_inc(v_a_1300_);
lean_dec(v_x_1290_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_apply_1(v_f_1289_, v_a_1300_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_a_1301_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg(lean_object* v_inst_1310_, lean_object* v_f_1311_, lean_object* v_x_1312_, lean_object* v_s_1313_){
_start:
{
lean_object* v_map_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_map_1314_ = lean_ctor_get(v_inst_1310_, 0);
lean_inc(v_map_1314_);
lean_dec_ref(v_inst_1310_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1315_, 0, v_f_1311_);
v___x_1316_ = lean_apply_1(v_x_1312_, v_s_1313_);
v___x_1317_ = lean_apply_4(v_map_1314_, lean_box(0), lean_box(0), v___f_1315_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept(lean_object* v_00_u03b5_1318_, lean_object* v_00_u03b5_x27_1319_, lean_object* v_00_u03c3_1320_, lean_object* v_00_u03b1_1321_, lean_object* v_m_1322_, lean_object* v_inst_1323_, lean_object* v_f_1324_, lean_object* v_x_1325_, lean_object* v_s_1326_){
_start:
{
lean_object* v_map_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_map_1327_ = lean_ctor_get(v_inst_1323_, 0);
lean_inc(v_map_1327_);
lean_dec_ref(v_inst_1323_);
v___f_1328_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1328_, 0, v_f_1324_);
v___x_1329_ = lean_apply_1(v_x_1325_, v_s_1326_);
v___x_1330_ = lean_apply_4(v_map_1327_, lean_box(0), lean_box(0), v___f_1328_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__0(lean_object* v_a_1331_, lean_object* v_toPure_1332_, lean_object* v_____do__lift_1333_){
_start:
{
if (lean_obj_tag(v_____do__lift_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v_a_1334_ = lean_ctor_get(v_____do__lift_1333_, 0);
v_a_1335_ = lean_ctor_get(v_____do__lift_1333_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_____do__lift_1333_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1337_ = v_____do__lift_1333_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_inc(v_a_1334_);
lean_dec(v_____do__lift_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_a_1331_);
lean_ctor_set(v___x_1339_, 1, v_a_1334_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_a_1335_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_apply_2(v_toPure_1332_, lean_box(0), v___x_1341_);
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1331_);
v_a_1345_ = lean_ctor_get(v_____do__lift_1333_, 0);
v_a_1346_ = lean_ctor_get(v_____do__lift_1333_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_____do__lift_1333_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v_____do__lift_1333_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_inc(v_a_1345_);
lean_dec(v_____do__lift_1333_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_apply_2(v_toPure_1332_, lean_box(0), v___x_1351_);
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__1(lean_object* v_a_1355_, lean_object* v_toPure_1356_, lean_object* v_____do__lift_1357_){
_start:
{
if (lean_obj_tag(v_____do__lift_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_a_1358_ = lean_ctor_get(v_____do__lift_1357_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_____do__lift_1357_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_____do__lift_1357_, 0);
lean_dec(v_unused_1367_);
v___x_1360_ = v_____do__lift_1357_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v_____do__lift_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 1);
lean_ctor_set(v___x_1360_, 0, v_a_1355_);
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1355_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_apply_2(v_toPure_1356_, lean_box(0), v___x_1363_);
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1355_);
v_a_1368_ = lean_ctor_get(v_____do__lift_1357_, 0);
v_a_1369_ = lean_ctor_get(v_____do__lift_1357_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_____do__lift_1357_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v_____do__lift_1357_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_inc(v_a_1368_);
lean_dec(v_____do__lift_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
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
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1368_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_apply_2(v_toPure_1356_, lean_box(0), v___x_1374_);
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__2(lean_object* v_toPure_1378_, lean_object* v_f_1379_, lean_object* v_toBind_1380_, lean_object* v_r_1381_){
_start:
{
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1382_ = lean_ctor_get(v_r_1381_, 0);
lean_inc_n(v_a_1382_, 2);
v_a_1383_ = lean_ctor_get(v_r_1381_, 1);
lean_inc(v_a_1383_);
lean_dec_ref_known(v_r_1381_, 2);
v___f_1384_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1384_, 0, v_a_1382_);
lean_closure_set(v___f_1384_, 1, v_toPure_1378_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_a_1382_);
v___x_1386_ = lean_apply_2(v_f_1379_, v___x_1385_, v_a_1383_);
v___x_1387_ = lean_apply_4(v_toBind_1380_, lean_box(0), lean_box(0), v___x_1386_, v___f_1384_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_a_1388_ = lean_ctor_get(v_r_1381_, 0);
lean_inc(v_a_1388_);
v_a_1389_ = lean_ctor_get(v_r_1381_, 1);
lean_inc(v_a_1389_);
lean_dec_ref_known(v_r_1381_, 2);
v___f_1390_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1390_, 0, v_a_1388_);
lean_closure_set(v___f_1390_, 1, v_toPure_1378_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_apply_2(v_f_1379_, v___x_1391_, v_a_1389_);
v___x_1393_ = lean_apply_4(v_toBind_1380_, lean_box(0), lean_box(0), v___x_1392_, v___f_1390_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg(lean_object* v_inst_1394_, lean_object* v_x_1395_, lean_object* v_f_1396_, lean_object* v_s_1397_){
_start:
{
lean_object* v_toApplicative_1398_; lean_object* v_toBind_1399_; lean_object* v_toPure_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
v_toApplicative_1398_ = lean_ctor_get(v_inst_1394_, 0);
lean_inc_ref(v_toApplicative_1398_);
v_toBind_1399_ = lean_ctor_get(v_inst_1394_, 1);
lean_inc_n(v_toBind_1399_, 2);
lean_dec_ref(v_inst_1394_);
v_toPure_1400_ = lean_ctor_get(v_toApplicative_1398_, 1);
lean_inc(v_toPure_1400_);
lean_dec_ref(v_toApplicative_1398_);
v___x_1401_ = lean_apply_1(v_x_1395_, v_s_1397_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1402_, 0, v_toPure_1400_);
lean_closure_set(v___f_1402_, 1, v_f_1396_);
lean_closure_set(v___f_1402_, 2, v_toBind_1399_);
v___x_1403_ = lean_apply_4(v_toBind_1399_, lean_box(0), lean_box(0), v___x_1401_, v___f_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27(lean_object* v_00_u03b5_1404_, lean_object* v_00_u03c3_1405_, lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_m_1408_, lean_object* v_inst_1409_, lean_object* v_x_1410_, lean_object* v_f_1411_, lean_object* v_s_1412_){
_start:
{
lean_object* v_toApplicative_1413_; lean_object* v_toBind_1414_; lean_object* v_toPure_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; 
v_toApplicative_1413_ = lean_ctor_get(v_inst_1409_, 0);
lean_inc_ref(v_toApplicative_1413_);
v_toBind_1414_ = lean_ctor_get(v_inst_1409_, 1);
lean_inc_n(v_toBind_1414_, 2);
lean_dec_ref(v_inst_1409_);
v_toPure_1415_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_inc(v_toPure_1415_);
lean_dec_ref(v_toApplicative_1413_);
v___x_1416_ = lean_apply_1(v_x_1410_, v_s_1412_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1417_, 0, v_toPure_1415_);
lean_closure_set(v___f_1417_, 1, v_f_1411_);
lean_closure_set(v___f_1417_, 2, v_toBind_1414_);
v___x_1418_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v___x_1416_, v___f_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(lean_object* v_toPure_1419_, lean_object* v___y_1420_, lean_object* v_toBind_1421_, lean_object* v_r_1422_){
_start:
{
if (lean_obj_tag(v_r_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_a_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_a_1423_ = lean_ctor_get(v_r_1422_, 0);
lean_inc_n(v_a_1423_, 2);
v_a_1424_ = lean_ctor_get(v_r_1422_, 1);
lean_inc(v_a_1424_);
lean_dec_ref_known(v_r_1422_, 2);
v___f_1425_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1425_, 0, v_a_1423_);
lean_closure_set(v___f_1425_, 1, v_toPure_1419_);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1423_);
v___x_1427_ = lean_apply_2(v___y_1420_, v___x_1426_, v_a_1424_);
v___x_1428_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v___x_1427_, v___f_1425_);
return v___x_1428_;
}
else
{
lean_object* v_a_1429_; lean_object* v_a_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1429_ = lean_ctor_get(v_r_1422_, 0);
lean_inc(v_a_1429_);
v_a_1430_ = lean_ctor_get(v_r_1422_, 1);
lean_inc(v_a_1430_);
lean_dec_ref_known(v_r_1422_, 2);
v___f_1431_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1431_, 0, v_a_1429_);
lean_closure_set(v___f_1431_, 1, v_toPure_1419_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_apply_2(v___y_1420_, v___x_1432_, v_a_1430_);
v___x_1434_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v___x_1433_, v___f_1431_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(lean_object* v_inst_1435_, lean_object* v_00_u03b1_1436_, lean_object* v_00_u03b2_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_toApplicative_1441_; lean_object* v_toBind_1442_; lean_object* v_toPure_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; 
v_toApplicative_1441_ = lean_ctor_get(v_inst_1435_, 0);
lean_inc_ref(v_toApplicative_1441_);
v_toBind_1442_ = lean_ctor_get(v_inst_1435_, 1);
lean_inc_n(v_toBind_1442_, 2);
lean_dec_ref(v_inst_1435_);
v_toPure_1443_ = lean_ctor_get(v_toApplicative_1441_, 1);
lean_inc(v_toPure_1443_);
lean_dec_ref(v_toApplicative_1441_);
v___x_1444_ = lean_apply_1(v___y_1438_, v___y_1440_);
v___f_1445_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1445_, 0, v_toPure_1443_);
lean_closure_set(v___f_1445_, 1, v___y_1439_);
lean_closure_set(v___f_1445_, 2, v_toBind_1442_);
v___x_1446_ = lean_apply_4(v_toBind_1442_, lean_box(0), lean_box(0), v___x_1444_, v___f_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg(lean_object* v_inst_1447_){
_start:
{
lean_object* v___f_1448_; 
v___f_1448_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1448_, 0, v_inst_1447_);
return v___f_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad(lean_object* v_00_u03b5_1449_, lean_object* v_00_u03c3_1450_, lean_object* v_m_1451_, lean_object* v_inst_1452_){
_start:
{
lean_object* v___f_1453_; 
v___f_1453_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1453_, 0, v_inst_1452_);
return v___f_1453_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM___redArg(lean_object* v_f_1454_, lean_object* v_s_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_apply_1(v_f_1454_, v_s_1455_);
v___x_1457_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM(lean_object* v_00_u03b5_1458_, lean_object* v_00_u03c3_1459_, lean_object* v_00_u03b1_1460_, lean_object* v_f_1461_, lean_object* v_s_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lake_EStateT_ofEStateM___redArg(v_f_1461_, v_s_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM___redArg(lean_object* v_f_1464_, lean_object* v_s_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_apply_1(v_f_1464_, v_s_1465_);
v___x_1467_ = l_Lake_EResult_toEStateMResult___redArg(v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM(lean_object* v_00_u03b5_1468_, lean_object* v_00_u03c3_1469_, lean_object* v_00_u03b1_1470_, lean_object* v_f_1471_, lean_object* v_s_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lake_EStateT_toEStateM___redArg(v_f_1471_, v_s_1472_);
return v___x_1473_;
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
