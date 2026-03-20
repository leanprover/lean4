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
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_EResult_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_instFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_EResult_instFunctor___closed__0 = (const lean_object*)&l_Lake_EResult_instFunctor___closed__0_value;
static const lean_closure_object l_Lake_EResult_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_instFunctor___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_EResult_instFunctor___closed__0_value)} };
static const lean_object* l_Lake_EResult_instFunctor___closed__1 = (const lean_object*)&l_Lake_EResult_instFunctor___closed__1_value;
static const lean_ctor_object l_Lake_EResult_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_EResult_instFunctor___closed__0_value),((lean_object*)&l_Lake_EResult_instFunctor___closed__1_value)}};
static const lean_object* l_Lake_EResult_instFunctor___closed__2 = (const lean_object*)&l_Lake_EResult_instFunctor___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___lam__0(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v___y_379_, lean_object* v___y_380_){
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
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor___lam__1(lean_object* v___f_400_, lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v___y_403_, lean_object* v___y_404_){
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
LEAN_EXPORT lean_object* l_Lake_EResult_instFunctor(lean_object* v_00_u03b5_413_, lean_object* v_00_u03c3_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Lake_EResult_instFunctor___closed__2));
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult___redArg(lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v_x_416_, 0);
v_a_418_ = lean_ctor_get(v_x_416_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v_x_416_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_inc(v_a_417_);
lean_dec(v_x_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_426_ = lean_ctor_get(v_x_416_, 0);
v_a_427_ = lean_ctor_get(v_x_416_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v_x_416_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_inc(v_a_426_);
lean_dec(v_x_416_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_toEStateMResult(lean_object* v_00_u03b5_435_, lean_object* v_00_u03c3_436_, lean_object* v_00_u03b1_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lake_EResult_toEStateMResult___redArg(v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult___redArg(lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_441_ = lean_ctor_get(v_x_440_, 0);
v_a_442_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_x_440_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_inc(v_a_441_);
lean_dec(v_x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_441_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_450_ = lean_ctor_get(v_x_440_, 0);
v_a_451_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v_x_440_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v_x_440_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EResult_ofEStateMResult(lean_object* v_00_u03b5_459_, lean_object* v_00_u03c3_460_, lean_object* v_00_u03b1_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk___redArg(lean_object* v_x_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_apply_1(v_x_464_, v_a_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_mk(lean_object* v_00_u03b5_467_, lean_object* v_00_u03c3_468_, lean_object* v_00_u03b1_469_, lean_object* v_m_470_, lean_object* v_x_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_apply_1(v_x_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_s_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_inst_474_);
lean_ctor_set(v___x_477_, 1, v_s_476_);
v___x_478_ = lean_apply_2(v_inst_475_, lean_box(0), v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(lean_object* v_inst_479_, lean_object* v_inst_480_){
_start:
{
lean_object* v___f_481_; 
v___f_481_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_481_, 0, v_inst_479_);
lean_closure_set(v___f_481_, 1, v_inst_480_);
return v___f_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(lean_object* v_00_u03b5_482_, lean_object* v_00_u03c3_483_, lean_object* v_00_u03b1_484_, lean_object* v_m_485_, lean_object* v_inst_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v___f_488_; 
v___f_488_ = lean_alloc_closure((void*)(l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0), 3, 2);
lean_closure_set(v___f_488_, 0, v_inst_486_);
lean_closure_set(v___f_488_, 1, v_inst_487_);
return v___f_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run___redArg(lean_object* v_init_489_, lean_object* v_self_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_apply_1(v_self_490_, v_init_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run(lean_object* v_00_u03b5_492_, lean_object* v_00_u03c3_493_, lean_object* v_00_u03b1_494_, lean_object* v_m_495_, lean_object* v_init_496_, lean_object* v_self_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_apply_1(v_self_497_, v_init_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27___redArg(lean_object* v_inst_500_, lean_object* v_init_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_map_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_map_503_ = lean_ctor_get(v_inst_500_, 0);
lean_inc(v_map_503_);
lean_dec_ref(v_inst_500_);
v___x_504_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_505_ = lean_apply_1(v_x_502_, v_init_501_);
v___x_506_ = lean_apply_4(v_map_503_, lean_box(0), lean_box(0), v___x_504_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x27(lean_object* v_00_u03b5_507_, lean_object* v_00_u03b1_508_, lean_object* v_m_509_, lean_object* v_00_u03c3_510_, lean_object* v_inst_511_, lean_object* v_init_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_map_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_map_514_ = lean_ctor_get(v_inst_511_, 0);
lean_inc(v_map_514_);
lean_dec_ref(v_inst_511_);
v___x_515_ = ((lean_object*)(l_Lake_EStateT_run_x27___redArg___closed__0));
v___x_516_ = lean_apply_1(v_x_513_, v_init_512_);
v___x_517_ = lean_apply_4(v_map_514_, lean_box(0), lean_box(0), v___x_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT___redArg(lean_object* v_inst_519_, lean_object* v_x_520_, lean_object* v_s_521_){
_start:
{
lean_object* v_map_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_map_522_ = lean_ctor_get(v_inst_519_, 0);
lean_inc(v_map_522_);
lean_dec_ref(v_inst_519_);
v___x_523_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_524_ = lean_apply_1(v_x_520_, v_s_521_);
v___x_525_ = lean_apply_4(v_map_522_, lean_box(0), lean_box(0), v___x_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT(lean_object* v_m_526_, lean_object* v_00_u03b5_527_, lean_object* v_00_u03c3_528_, lean_object* v_00_u03b1_529_, lean_object* v_inst_530_, lean_object* v_x_531_, lean_object* v_s_532_){
_start:
{
lean_object* v_map_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_map_533_ = lean_ctor_get(v_inst_530_, 0);
lean_inc(v_map_533_);
lean_dec_ref(v_inst_530_);
v___x_534_ = ((lean_object*)(l_Lake_EStateT_toStateT___redArg___closed__0));
v___x_535_ = lean_apply_1(v_x_531_, v_s_532_);
v___x_536_ = lean_apply_4(v_map_533_, lean_box(0), lean_box(0), v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f___redArg(lean_object* v_inst_538_, lean_object* v_x_539_, lean_object* v_s_540_){
_start:
{
lean_object* v_map_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_map_541_ = lean_ctor_get(v_inst_538_, 0);
lean_inc(v_map_541_);
lean_dec_ref(v_inst_538_);
v___x_542_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_543_ = lean_apply_1(v_x_539_, v_s_540_);
v___x_544_ = lean_apply_4(v_map_541_, lean_box(0), lean_box(0), v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toStateT_x3f(lean_object* v_m_545_, lean_object* v_00_u03b5_546_, lean_object* v_00_u03c3_547_, lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_x_550_, lean_object* v_s_551_){
_start:
{
lean_object* v_map_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_map_552_ = lean_ctor_get(v_inst_549_, 0);
lean_inc(v_map_552_);
lean_dec_ref(v_inst_549_);
v___x_553_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_554_ = lean_apply_1(v_x_550_, v_s_551_);
v___x_555_ = lean_apply_4(v_map_552_, lean_box(0), lean_box(0), v___x_553_, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f___redArg(lean_object* v_inst_556_, lean_object* v_init_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_map_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_map_559_ = lean_ctor_get(v_inst_556_, 0);
lean_inc(v_map_559_);
lean_dec_ref(v_inst_556_);
v___x_560_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_561_ = lean_apply_1(v_x_558_, v_init_557_);
v___x_562_ = lean_apply_4(v_map_559_, lean_box(0), lean_box(0), v___x_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f(lean_object* v_00_u03c3_563_, lean_object* v_00_u03b1_564_, lean_object* v_m_565_, lean_object* v_00_u03b5_566_, lean_object* v_inst_567_, lean_object* v_init_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_map_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_map_570_ = lean_ctor_get(v_inst_567_, 0);
lean_inc(v_map_570_);
lean_dec_ref(v_inst_567_);
v___x_571_ = ((lean_object*)(l_Lake_EStateT_toStateT_x3f___redArg___closed__0));
v___x_572_ = lean_apply_1(v_x_569_, v_init_568_);
v___x_573_ = lean_apply_4(v_map_570_, lean_box(0), lean_box(0), v___x_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27___redArg(lean_object* v_inst_575_, lean_object* v_init_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_map_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_map_578_ = lean_ctor_get(v_inst_575_, 0);
lean_inc(v_map_578_);
lean_dec_ref(v_inst_575_);
v___x_579_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_580_ = lean_apply_1(v_x_577_, v_init_576_);
v___x_581_ = lean_apply_4(v_map_578_, lean_box(0), lean_box(0), v___x_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_run_x3f_x27(lean_object* v_m_582_, lean_object* v_00_u03b5_583_, lean_object* v_00_u03c3_584_, lean_object* v_00_u03b1_585_, lean_object* v_inst_586_, lean_object* v_init_587_, lean_object* v_x_588_){
_start:
{
lean_object* v_map_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_map_589_ = lean_ctor_get(v_inst_586_, 0);
lean_inc(v_map_589_);
lean_dec_ref(v_inst_586_);
v___x_590_ = ((lean_object*)(l_Lake_EStateT_run_x3f_x27___redArg___closed__0));
v___x_591_ = lean_apply_1(v_x_588_, v_init_587_);
v___x_592_ = lean_apply_4(v_map_589_, lean_box(0), lean_box(0), v___x_590_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg___lam__0(lean_object* v_toPure_593_, lean_object* v_h_594_, lean_object* v_____do__lift_595_){
_start:
{
if (lean_obj_tag(v_____do__lift_595_) == 0)
{
lean_object* v_a_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_h_594_);
v_a_596_ = lean_ctor_get(v_____do__lift_595_, 0);
v_a_597_ = lean_ctor_get(v_____do__lift_595_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_____do__lift_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v_____do__lift_595_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_inc(v_a_596_);
lean_dec(v_____do__lift_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_597_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = lean_apply_2(v_toPure_593_, lean_box(0), v___x_602_);
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_608_; 
lean_dec(v_toPure_593_);
v_a_606_ = lean_ctor_get(v_____do__lift_595_, 0);
lean_inc(v_a_606_);
v_a_607_ = lean_ctor_get(v_____do__lift_595_, 1);
lean_inc(v_a_607_);
lean_dec_ref(v_____do__lift_595_);
v___x_608_ = lean_apply_2(v_h_594_, v_a_606_, v_a_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions___redArg(lean_object* v_inst_609_, lean_object* v_x_610_, lean_object* v_h_611_, lean_object* v_s_612_){
_start:
{
lean_object* v_toApplicative_613_; lean_object* v_toBind_614_; lean_object* v_toPure_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; 
v_toApplicative_613_ = lean_ctor_get(v_inst_609_, 0);
lean_inc_ref(v_toApplicative_613_);
v_toBind_614_ = lean_ctor_get(v_inst_609_, 1);
lean_inc(v_toBind_614_);
lean_dec_ref(v_inst_609_);
v_toPure_615_ = lean_ctor_get(v_toApplicative_613_, 1);
lean_inc(v_toPure_615_);
lean_dec_ref(v_toApplicative_613_);
v___x_616_ = lean_apply_1(v_x_610_, v_s_612_);
v___f_617_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_617_, 0, v_toPure_615_);
lean_closure_set(v___f_617_, 1, v_h_611_);
v___x_618_ = lean_apply_4(v_toBind_614_, lean_box(0), lean_box(0), v___x_616_, v___f_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_catchExceptions(lean_object* v_m_619_, lean_object* v_00_u03b5_620_, lean_object* v_00_u03c3_621_, lean_object* v_00_u03b1_622_, lean_object* v_inst_623_, lean_object* v_x_624_, lean_object* v_h_625_, lean_object* v_s_626_){
_start:
{
lean_object* v_toApplicative_627_; lean_object* v_toBind_628_; lean_object* v_toPure_629_; lean_object* v___x_630_; lean_object* v___f_631_; lean_object* v___x_632_; 
v_toApplicative_627_ = lean_ctor_get(v_inst_623_, 0);
lean_inc_ref(v_toApplicative_627_);
v_toBind_628_ = lean_ctor_get(v_inst_623_, 1);
lean_inc(v_toBind_628_);
lean_dec_ref(v_inst_623_);
v_toPure_629_ = lean_ctor_get(v_toApplicative_627_, 1);
lean_inc(v_toPure_629_);
lean_dec_ref(v_toApplicative_627_);
v___x_630_ = lean_apply_1(v_x_624_, v_s_626_);
v___f_631_ = lean_alloc_closure((void*)(l_Lake_EStateT_catchExceptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_631_, 0, v_toPure_629_);
lean_closure_set(v___f_631_, 1, v_h_625_);
v___x_632_ = lean_apply_4(v_toBind_628_, lean_box(0), lean_box(0), v___x_630_, v___f_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg___lam__0(lean_object* v_s_633_, lean_object* v_toPure_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_a_635_);
lean_ctor_set(v___x_636_, 1, v_s_633_);
v___x_637_ = lean_apply_2(v_toPure_634_, lean_box(0), v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift___redArg(lean_object* v_inst_638_, lean_object* v_x_639_, lean_object* v_s_640_){
_start:
{
lean_object* v_toApplicative_641_; lean_object* v_toBind_642_; lean_object* v_toPure_643_; lean_object* v___f_644_; lean_object* v___x_645_; 
v_toApplicative_641_ = lean_ctor_get(v_inst_638_, 0);
lean_inc_ref(v_toApplicative_641_);
v_toBind_642_ = lean_ctor_get(v_inst_638_, 1);
lean_inc(v_toBind_642_);
lean_dec_ref(v_inst_638_);
v_toPure_643_ = lean_ctor_get(v_toApplicative_641_, 1);
lean_inc(v_toPure_643_);
lean_dec_ref(v_toApplicative_641_);
v___f_644_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_644_, 0, v_s_640_);
lean_closure_set(v___f_644_, 1, v_toPure_643_);
v___x_645_ = lean_apply_4(v_toBind_642_, lean_box(0), lean_box(0), v_x_639_, v___f_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_lift(lean_object* v_m_646_, lean_object* v_00_u03b5_647_, lean_object* v_00_u03c3_648_, lean_object* v_00_u03b1_649_, lean_object* v_inst_650_, lean_object* v_x_651_, lean_object* v_s_652_){
_start:
{
lean_object* v_toApplicative_653_; lean_object* v_toBind_654_; lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___x_657_; 
v_toApplicative_653_ = lean_ctor_get(v_inst_650_, 0);
lean_inc_ref(v_toApplicative_653_);
v_toBind_654_ = lean_ctor_get(v_inst_650_, 1);
lean_inc(v_toBind_654_);
lean_dec_ref(v_inst_650_);
v_toPure_655_ = lean_ctor_get(v_toApplicative_653_, 1);
lean_inc(v_toPure_655_);
lean_dec_ref(v_toApplicative_653_);
v___f_656_ = lean_alloc_closure((void*)(l_Lake_EStateT_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_656_, 0, v_s_652_);
lean_closure_set(v___f_656_, 1, v_toPure_655_);
v___x_657_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v_x_651_, v___f_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(lean_object* v___y_658_, lean_object* v_toPure_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_a_660_);
lean_ctor_set(v___x_661_, 1, v___y_658_);
v___x_662_ = lean_apply_2(v_toPure_659_, lean_box(0), v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object* v_inst_663_, lean_object* v_00_u03b1_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_toApplicative_667_; lean_object* v_toBind_668_; lean_object* v_toPure_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
v_toApplicative_667_ = lean_ctor_get(v_inst_663_, 0);
lean_inc_ref(v_toApplicative_667_);
v_toBind_668_ = lean_ctor_get(v_inst_663_, 1);
lean_inc(v_toBind_668_);
lean_dec_ref(v_inst_663_);
v_toPure_669_ = lean_ctor_get(v_toApplicative_667_, 1);
lean_inc(v_toPure_669_);
lean_dec_ref(v_toApplicative_667_);
v___f_670_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_670_, 0, v___y_666_);
lean_closure_set(v___f_670_, 1, v_toPure_669_);
v___x_671_ = lean_apply_4(v_toBind_668_, lean_box(0), lean_box(0), v___y_665_, v___f_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg(lean_object* v_inst_672_){
_start:
{
lean_object* v___f_673_; 
v___f_673_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_673_, 0, v_inst_672_);
return v___f_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadLiftOfMonad(lean_object* v_m_674_, lean_object* v_00_u03b5_675_, lean_object* v_00_u03c3_676_, lean_object* v_inst_677_){
_start:
{
lean_object* v___f_678_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_678_, 0, v_inst_677_);
return v___f_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure___redArg(lean_object* v_inst_679_, lean_object* v_a_680_, lean_object* v_s_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_a_680_);
lean_ctor_set(v___x_682_, 1, v_s_681_);
v___x_683_ = lean_apply_2(v_inst_679_, lean_box(0), v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_pure(lean_object* v_00_u03b5_684_, lean_object* v_00_u03c3_685_, lean_object* v_00_u03b1_686_, lean_object* v_m_687_, lean_object* v_inst_688_, lean_object* v_a_689_, lean_object* v_s_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_a_689_);
lean_ctor_set(v___x_691_, 1, v_s_690_);
v___x_692_ = lean_apply_2(v_inst_688_, lean_box(0), v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object* v_inst_693_, lean_object* v_00_u03b1_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___y_695_);
lean_ctor_set(v___x_697_, 1, v___y_696_);
v___x_698_ = lean_apply_2(v_inst_693_, lean_box(0), v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure___redArg(lean_object* v_inst_699_){
_start:
{
lean_object* v___f_700_; 
v___f_700_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_700_, 0, v_inst_699_);
return v___f_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instPure(lean_object* v_00_u03b5_701_, lean_object* v_00_u03c3_702_, lean_object* v_m_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v___f_705_; 
v___f_705_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_705_, 0, v_inst_704_);
return v___f_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg___lam__0(lean_object* v_f_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_a_708_ = lean_ctor_get(v_x_707_, 0);
v_a_709_ = lean_ctor_get(v_x_707_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_x_707_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_inc(v_a_708_);
lean_dec(v_x_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_apply_1(v_f_706_, v_a_708_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_a_709_);
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
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_f_706_);
v_a_718_ = lean_ctor_get(v_x_707_, 0);
v_a_719_ = lean_ctor_get(v_x_707_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v_x_707_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_inc(v_a_718_);
lean_dec(v_x_707_);
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
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_718_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_719_);
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
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map___redArg(lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_x_729_, lean_object* v_s_730_){
_start:
{
lean_object* v_map_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_map_731_ = lean_ctor_get(v_inst_727_, 0);
lean_inc(v_map_731_);
lean_dec_ref(v_inst_727_);
v___f_732_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_732_, 0, v_f_728_);
v___x_733_ = lean_apply_1(v_x_729_, v_s_730_);
v___x_734_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_map(lean_object* v_00_u03b5_735_, lean_object* v_00_u03c3_736_, lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_inst_740_, lean_object* v_f_741_, lean_object* v_x_742_, lean_object* v_s_743_){
_start:
{
lean_object* v_map_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_map_744_ = lean_ctor_get(v_inst_740_, 0);
lean_inc(v_map_744_);
lean_dec_ref(v_inst_740_);
v___f_745_ = lean_alloc_closure((void*)(l_Lake_EStateT_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_745_, 0, v_f_741_);
v___x_746_ = lean_apply_1(v_x_742_, v_s_743_);
v___x_747_ = lean_apply_4(v_map_744_, lean_box(0), lean_box(0), v___f_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__0(lean_object* v___y_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_759_; 
v_a_750_ = lean_ctor_get(v_x_749_, 0);
v_a_751_ = lean_ctor_get(v_x_749_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_759_ == 0)
{
v___x_753_ = v_x_749_;
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_inc(v_a_750_);
lean_dec(v_x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_apply_1(v___y_748_, v_a_750_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_a_751_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v___y_748_);
v_a_760_ = lean_ctor_get(v_x_749_, 0);
v_a_761_ = lean_ctor_get(v_x_749_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v_x_749_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_inc(v_a_760_);
lean_dec(v_x_749_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__1(lean_object* v_inst_769_, lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_map_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_map_775_ = lean_ctor_get(v_inst_769_, 0);
lean_inc(v_map_775_);
lean_dec_ref(v_inst_769_);
v___f_776_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__0), 2, 1);
lean_closure_set(v___f_776_, 0, v___y_772_);
v___x_777_ = lean_apply_1(v___y_773_, v___y_774_);
v___x_778_ = lean_apply_4(v_map_775_, lean_box(0), lean_box(0), v___f_776_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg___lam__2(lean_object* v___f_779_, lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_785_, 0, lean_box(0));
lean_closure_set(v___x_785_, 1, lean_box(0));
lean_closure_set(v___x_785_, 2, v___y_782_);
v___x_786_ = lean_apply_5(v___f_779_, lean_box(0), lean_box(0), v___x_785_, v___y_783_, v___y_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object* v_inst_787_){
_start:
{
lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_790_; 
v___f_788_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__1), 6, 1);
lean_closure_set(v___f_788_, 0, v_inst_787_);
lean_inc_ref(v___f_788_);
v___f_789_ = lean_alloc_closure((void*)(l_Lake_EStateT_instFunctor___redArg___lam__2), 6, 1);
lean_closure_set(v___f_789_, 0, v___f_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___f_788_);
lean_ctor_set(v___x_790_, 1, v___f_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instFunctor(lean_object* v_00_u03b5_791_, lean_object* v_00_u03c3_792_, lean_object* v_m_793_, lean_object* v_inst_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lake_EStateT_instFunctor___redArg(v_inst_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg___lam__0(lean_object* v_f_796_, lean_object* v_toPure_797_, lean_object* v_____do__lift_798_){
_start:
{
if (lean_obj_tag(v_____do__lift_798_) == 0)
{
lean_object* v_a_799_; lean_object* v_a_800_; lean_object* v___x_801_; 
lean_dec(v_toPure_797_);
v_a_799_ = lean_ctor_get(v_____do__lift_798_, 0);
lean_inc(v_a_799_);
v_a_800_ = lean_ctor_get(v_____do__lift_798_, 1);
lean_inc(v_a_800_);
lean_dec_ref(v_____do__lift_798_);
v___x_801_ = lean_apply_2(v_f_796_, v_a_799_, v_a_800_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_f_796_);
v_a_802_ = lean_ctor_get(v_____do__lift_798_, 0);
v_a_803_ = lean_ctor_get(v_____do__lift_798_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_____do__lift_798_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v_____do__lift_798_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_inc(v_a_802_);
lean_dec(v_____do__lift_798_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_803_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_808_);
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind___redArg(lean_object* v_inst_812_, lean_object* v_x_813_, lean_object* v_f_814_, lean_object* v_s_815_){
_start:
{
lean_object* v_toApplicative_816_; lean_object* v_toBind_817_; lean_object* v_toPure_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v_toApplicative_816_ = lean_ctor_get(v_inst_812_, 0);
lean_inc_ref(v_toApplicative_816_);
v_toBind_817_ = lean_ctor_get(v_inst_812_, 1);
lean_inc(v_toBind_817_);
lean_dec_ref(v_inst_812_);
v_toPure_818_ = lean_ctor_get(v_toApplicative_816_, 1);
lean_inc(v_toPure_818_);
lean_dec_ref(v_toApplicative_816_);
v___x_819_ = lean_apply_1(v_x_813_, v_s_815_);
v___f_820_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_820_, 0, v_f_814_);
lean_closure_set(v___f_820_, 1, v_toPure_818_);
v___x_821_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v___x_819_, v___f_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_bind(lean_object* v_00_u03b5_822_, lean_object* v_00_u03c3_823_, lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_m_826_, lean_object* v_inst_827_, lean_object* v_x_828_, lean_object* v_f_829_, lean_object* v_s_830_){
_start:
{
lean_object* v_toApplicative_831_; lean_object* v_toBind_832_; lean_object* v_toPure_833_; lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
v_toApplicative_831_ = lean_ctor_get(v_inst_827_, 0);
lean_inc_ref(v_toApplicative_831_);
v_toBind_832_ = lean_ctor_get(v_inst_827_, 1);
lean_inc(v_toBind_832_);
lean_dec_ref(v_inst_827_);
v_toPure_833_ = lean_ctor_get(v_toApplicative_831_, 1);
lean_inc(v_toPure_833_);
lean_dec_ref(v_toApplicative_831_);
v___x_834_ = lean_apply_1(v_x_828_, v_s_830_);
v___f_835_ = lean_alloc_closure((void*)(l_Lake_EStateT_bind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_835_, 0, v_f_829_);
lean_closure_set(v___f_835_, 1, v_toPure_833_);
v___x_836_ = lean_apply_4(v_toBind_832_, lean_box(0), lean_box(0), v___x_834_, v___f_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg___lam__0(lean_object* v_y_837_, lean_object* v_toPure_838_, lean_object* v_____do__lift_839_){
_start:
{
if (lean_obj_tag(v_____do__lift_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_toPure_838_);
v_a_840_ = lean_ctor_get(v_____do__lift_839_, 1);
lean_inc(v_a_840_);
lean_dec_ref(v_____do__lift_839_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_apply_2(v_y_837_, v___x_841_, v_a_840_);
return v___x_842_;
}
else
{
lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_y_837_);
v_a_843_ = lean_ctor_get(v_____do__lift_839_, 0);
v_a_844_ = lean_ctor_get(v_____do__lift_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_____do__lift_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v_____do__lift_839_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_inc(v_a_843_);
lean_dec(v_____do__lift_839_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
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
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_843_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_844_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_apply_2(v_toPure_838_, lean_box(0), v___x_849_);
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight___redArg(lean_object* v_inst_853_, lean_object* v_x_854_, lean_object* v_y_855_, lean_object* v_s_856_){
_start:
{
lean_object* v_toApplicative_857_; lean_object* v_toBind_858_; lean_object* v_toPure_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___x_862_; 
v_toApplicative_857_ = lean_ctor_get(v_inst_853_, 0);
lean_inc_ref(v_toApplicative_857_);
v_toBind_858_ = lean_ctor_get(v_inst_853_, 1);
lean_inc(v_toBind_858_);
lean_dec_ref(v_inst_853_);
v_toPure_859_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc(v_toPure_859_);
lean_dec_ref(v_toApplicative_857_);
v___x_860_ = lean_apply_1(v_x_854_, v_s_856_);
v___f_861_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_861_, 0, v_y_855_);
lean_closure_set(v___f_861_, 1, v_toPure_859_);
v___x_862_ = lean_apply_4(v_toBind_858_, lean_box(0), lean_box(0), v___x_860_, v___f_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_seqRight(lean_object* v_00_u03b5_863_, lean_object* v_00_u03c3_864_, lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_x_869_, lean_object* v_y_870_, lean_object* v_s_871_){
_start:
{
lean_object* v_toApplicative_872_; lean_object* v_toBind_873_; lean_object* v_toPure_874_; lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; 
v_toApplicative_872_ = lean_ctor_get(v_inst_868_, 0);
lean_inc_ref(v_toApplicative_872_);
v_toBind_873_ = lean_ctor_get(v_inst_868_, 1);
lean_inc(v_toBind_873_);
lean_dec_ref(v_inst_868_);
v_toPure_874_ = lean_ctor_get(v_toApplicative_872_, 1);
lean_inc(v_toPure_874_);
lean_dec_ref(v_toApplicative_872_);
v___x_875_ = lean_apply_1(v_x_869_, v_s_871_);
v___f_876_ = lean_alloc_closure((void*)(l_Lake_EStateT_seqRight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_876_, 0, v_y_870_);
lean_closure_set(v___f_876_, 1, v_toPure_874_);
v___x_877_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v___x_875_, v___f_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__0(lean_object* v___y_878_, lean_object* v_toPure_879_, lean_object* v_____do__lift_880_){
_start:
{
if (lean_obj_tag(v_____do__lift_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_a_882_; lean_object* v___x_883_; 
lean_dec(v_toPure_879_);
v_a_881_ = lean_ctor_get(v_____do__lift_880_, 0);
lean_inc(v_a_881_);
v_a_882_ = lean_ctor_get(v_____do__lift_880_, 1);
lean_inc(v_a_882_);
lean_dec_ref(v_____do__lift_880_);
v___x_883_ = lean_apply_2(v___y_878_, v_a_881_, v_a_882_);
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
lean_dec(v___y_878_);
v_a_884_ = lean_ctor_get(v_____do__lift_880_, 0);
v_a_885_ = lean_ctor_get(v_____do__lift_880_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_____do__lift_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_____do__lift_880_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_inc(v_a_884_);
lean_dec(v_____do__lift_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
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
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_885_);
v___x_890_ = v_reuseFailAlloc_892_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
v___x_891_ = lean_apply_2(v_toPure_879_, lean_box(0), v___x_890_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object* v_toPure_894_, lean_object* v_toBind_895_, lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v___x_901_ = lean_apply_1(v___y_898_, v___y_900_);
v___f_902_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_902_, 0, v___y_899_);
lean_closure_set(v___f_902_, 1, v_toPure_894_);
v___x_903_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_901_, v___f_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__2(lean_object* v___y_904_, lean_object* v_toPure_905_, lean_object* v_____do__lift_906_){
_start:
{
if (lean_obj_tag(v_____do__lift_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_toPure_905_);
v_a_907_ = lean_ctor_get(v_____do__lift_906_, 1);
lean_inc(v_a_907_);
lean_dec_ref(v_____do__lift_906_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_apply_2(v___y_904_, v___x_908_, v_a_907_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
lean_dec(v___y_904_);
v_a_910_ = lean_ctor_get(v_____do__lift_906_, 0);
v_a_911_ = lean_ctor_get(v_____do__lift_906_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_____do__lift_906_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v_____do__lift_906_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_inc(v_a_910_);
lean_dec(v_____do__lift_906_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_910_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_911_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; 
v___x_917_ = lean_apply_2(v_toPure_905_, lean_box(0), v___x_916_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object* v_toPure_920_, lean_object* v_toBind_921_, lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___x_929_; 
v___x_927_ = lean_apply_1(v___y_924_, v___y_926_);
v___f_928_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_928_, 0, v___y_925_);
lean_closure_set(v___f_928_, 1, v_toPure_920_);
v___x_929_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v___x_927_, v___f_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6(lean_object* v_a_930_, lean_object* v_toPure_931_, lean_object* v_x_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_a_930_);
lean_ctor_set(v___x_934_, 1, v___y_933_);
v___x_935_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__6___boxed(lean_object* v_a_936_, lean_object* v_toPure_937_, lean_object* v_x_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lake_EStateT_instMonad___redArg___lam__6(v_a_936_, v_toPure_937_, v_x_938_, v___y_939_);
lean_dec(v_x_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__4(lean_object* v_toPure_941_, lean_object* v_y_942_, lean_object* v___f_943_, lean_object* v_a_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___f_946_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_946_, 0, v_a_944_);
lean_closure_set(v___f_946_, 1, v_toPure_941_);
v___x_947_ = lean_box(0);
v___x_948_ = lean_apply_1(v_y_942_, v___x_947_);
v___x_949_ = lean_apply_5(v___f_943_, lean_box(0), lean_box(0), v___x_948_, v___f_946_, v___y_945_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object* v_toPure_950_, lean_object* v___f_951_, lean_object* v_00_u03b1_952_, lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; 
lean_inc(v___f_951_);
v___f_957_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__4), 5, 3);
lean_closure_set(v___f_957_, 0, v_toPure_950_);
lean_closure_set(v___f_957_, 1, v_y_955_);
lean_closure_set(v___f_957_, 2, v___f_951_);
v___x_958_ = lean_apply_5(v___f_951_, lean_box(0), lean_box(0), v_x_954_, v___f_957_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__7(lean_object* v_a_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_a_961_ = lean_ctor_get(v_x_960_, 0);
v_a_962_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v_x_960_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_inc(v_a_961_);
lean_dec(v_x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_apply_1(v_a_959_, v_a_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_a_962_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_a_959_);
v_a_971_ = lean_ctor_get(v_x_960_, 0);
v_a_972_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v_x_960_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_inc(v_a_971_);
lean_dec(v_x_960_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__8(lean_object* v_toFunctor_980_, lean_object* v_x_981_, lean_object* v_toPure_982_, lean_object* v_____do__lift_983_){
_start:
{
if (lean_obj_tag(v_____do__lift_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v_map_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_toPure_982_);
v_a_984_ = lean_ctor_get(v_____do__lift_983_, 0);
lean_inc(v_a_984_);
v_a_985_ = lean_ctor_get(v_____do__lift_983_, 1);
lean_inc(v_a_985_);
lean_dec_ref(v_____do__lift_983_);
v_map_986_ = lean_ctor_get(v_toFunctor_980_, 0);
lean_inc(v_map_986_);
lean_dec_ref(v_toFunctor_980_);
v___f_987_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__7), 2, 1);
lean_closure_set(v___f_987_, 0, v_a_984_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_apply_2(v_x_981_, v___x_988_, v_a_985_);
v___x_990_ = lean_apply_4(v_map_986_, lean_box(0), lean_box(0), v___f_987_, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_a_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_x_981_);
lean_dec_ref(v_toFunctor_980_);
v_a_991_ = lean_ctor_get(v_____do__lift_983_, 0);
v_a_992_ = lean_ctor_get(v_____do__lift_983_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_____do__lift_983_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_994_ = v_____do__lift_983_;
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_inc(v_a_991_);
lean_dec(v_____do__lift_983_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_a_992_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = lean_apply_2(v_toPure_982_, lean_box(0), v___x_997_);
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object* v_toFunctor_1001_, lean_object* v_toPure_1002_, lean_object* v_toBind_1003_, lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_f_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___f_1009_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1009_, 0, v_toFunctor_1001_);
lean_closure_set(v___f_1009_, 1, v_x_1007_);
lean_closure_set(v___f_1009_, 2, v_toPure_1002_);
v___x_1010_ = lean_apply_1(v_f_1006_, v___y_1008_);
v___x_1011_ = lean_apply_4(v_toBind_1003_, lean_box(0), lean_box(0), v___x_1010_, v___f_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad___redArg(lean_object* v_inst_1012_){
_start:
{
lean_object* v_toApplicative_1013_; lean_object* v_toBind_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1039_; 
v_toApplicative_1013_ = lean_ctor_get(v_inst_1012_, 0);
v_toBind_1014_ = lean_ctor_get(v_inst_1012_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_inst_1012_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1016_ = v_inst_1012_;
v_isShared_1017_ = v_isSharedCheck_1039_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_toBind_1014_);
lean_inc(v_toApplicative_1013_);
lean_dec(v_inst_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1039_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_toFunctor_1018_; lean_object* v_toPure_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1035_; 
v_toFunctor_1018_ = lean_ctor_get(v_toApplicative_1013_, 0);
v_toPure_1019_ = lean_ctor_get(v_toApplicative_1013_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_toApplicative_1013_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; lean_object* v_unused_1037_; lean_object* v_unused_1038_; 
v_unused_1036_ = lean_ctor_get(v_toApplicative_1013_, 4);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_toApplicative_1013_, 3);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_toApplicative_1013_, 2);
lean_dec(v_unused_1038_);
v___x_1021_ = v_toApplicative_1013_;
v_isShared_1022_ = v_isSharedCheck_1035_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toPure_1019_);
lean_inc(v_toFunctor_1018_);
lean_dec(v_toApplicative_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1035_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1030_; 
lean_inc(v_toBind_1014_);
lean_inc(v_toPure_1019_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1023_, 0, v_toPure_1019_);
lean_closure_set(v___f_1023_, 1, v_toBind_1014_);
lean_inc(v_toBind_1014_);
lean_inc(v_toPure_1019_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1024_, 0, v_toPure_1019_);
lean_closure_set(v___f_1024_, 1, v_toBind_1014_);
lean_inc_ref(v___f_1023_);
lean_inc(v_toPure_1019_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1025_, 0, v_toPure_1019_);
lean_closure_set(v___f_1025_, 1, v___f_1023_);
lean_inc(v_toPure_1019_);
lean_inc_ref(v_toFunctor_1018_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1026_, 0, v_toFunctor_1018_);
lean_closure_set(v___f_1026_, 1, v_toPure_1019_);
lean_closure_set(v___f_1026_, 2, v_toBind_1014_);
v___x_1027_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1018_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1028_, 0, v_toPure_1019_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v___f_1024_);
lean_ctor_set(v___x_1021_, 3, v___f_1025_);
lean_ctor_set(v___x_1021_, 2, v___f_1026_);
lean_ctor_set(v___x_1021_, 1, v___f_1028_);
lean_ctor_set(v___x_1021_, 0, v___x_1027_);
v___x_1030_ = v___x_1021_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___f_1028_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v___f_1026_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v___f_1025_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v___f_1024_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___f_1023_);
lean_ctor_set(v___x_1016_, 0, v___x_1030_);
v___x_1032_ = v___x_1016_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___f_1023_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonad(lean_object* v_00_u03b5_1040_, lean_object* v_00_u03c3_1041_, lean_object* v_m_1042_, lean_object* v_inst_1043_){
_start:
{
lean_object* v_toApplicative_1044_; lean_object* v_toBind_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1070_; 
v_toApplicative_1044_ = lean_ctor_get(v_inst_1043_, 0);
v_toBind_1045_ = lean_ctor_get(v_inst_1043_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_inst_1043_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1047_ = v_inst_1043_;
v_isShared_1048_ = v_isSharedCheck_1070_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_toBind_1045_);
lean_inc(v_toApplicative_1044_);
lean_dec(v_inst_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1070_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_toFunctor_1049_; lean_object* v_toPure_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1066_; 
v_toFunctor_1049_ = lean_ctor_get(v_toApplicative_1044_, 0);
v_toPure_1050_ = lean_ctor_get(v_toApplicative_1044_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_toApplicative_1044_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1067_ = lean_ctor_get(v_toApplicative_1044_, 4);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_toApplicative_1044_, 3);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_toApplicative_1044_, 2);
lean_dec(v_unused_1069_);
v___x_1052_ = v_toApplicative_1044_;
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_toPure_1050_);
lean_inc(v_toFunctor_1049_);
lean_dec(v_toApplicative_1044_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1061_; 
lean_inc(v_toBind_1045_);
lean_inc(v_toPure_1050_);
v___f_1054_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1054_, 0, v_toPure_1050_);
lean_closure_set(v___f_1054_, 1, v_toBind_1045_);
lean_inc(v_toBind_1045_);
lean_inc(v_toPure_1050_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1055_, 0, v_toPure_1050_);
lean_closure_set(v___f_1055_, 1, v_toBind_1045_);
lean_inc_ref(v___f_1054_);
lean_inc(v_toPure_1050_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1056_, 0, v_toPure_1050_);
lean_closure_set(v___f_1056_, 1, v___f_1054_);
lean_inc(v_toPure_1050_);
lean_inc_ref(v_toFunctor_1049_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1057_, 0, v_toFunctor_1049_);
lean_closure_set(v___f_1057_, 1, v_toPure_1050_);
lean_closure_set(v___f_1057_, 2, v_toBind_1045_);
v___x_1058_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1049_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1059_, 0, v_toPure_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___f_1055_);
lean_ctor_set(v___x_1052_, 3, v___f_1056_);
lean_ctor_set(v___x_1052_, 2, v___f_1057_);
lean_ctor_set(v___x_1052_, 1, v___f_1059_);
lean_ctor_set(v___x_1052_, 0, v___x_1058_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___f_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v___f_1055_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___f_1054_);
lean_ctor_set(v___x_1047_, 0, v___x_1061_);
v___x_1063_ = v___x_1047_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___f_1054_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___redArg(lean_object* v_inst_1071_, lean_object* v_s_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_s_1072_);
v___x_1075_ = lean_apply_2(v_inst_1071_, lean_box(0), v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set(lean_object* v_00_u03b5_1076_, lean_object* v_00_u03c3_1077_, lean_object* v_m_1078_, lean_object* v_inst_1079_, lean_object* v_s_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_s_1080_);
v___x_1084_ = lean_apply_2(v_inst_1079_, lean_box(0), v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_set___boxed(lean_object* v_00_u03b5_1085_, lean_object* v_00_u03c3_1086_, lean_object* v_m_1087_, lean_object* v_inst_1088_, lean_object* v_s_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lake_EStateT_set(v_00_u03b5_1085_, v_00_u03c3_1086_, v_m_1087_, v_inst_1088_, v_s_1089_, v_x_1090_);
lean_dec(v_x_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get___redArg(lean_object* v_inst_1092_, lean_object* v_s_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_inc(v_s_1093_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_s_1093_);
lean_ctor_set(v___x_1094_, 1, v_s_1093_);
v___x_1095_ = lean_apply_2(v_inst_1092_, lean_box(0), v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_get(lean_object* v_00_u03b5_1096_, lean_object* v_00_u03c3_1097_, lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_s_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_inc(v_s_1100_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_s_1100_);
lean_ctor_set(v___x_1101_, 1, v_s_1100_);
v___x_1102_ = lean_apply_2(v_inst_1099_, lean_box(0), v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet___redArg(lean_object* v_inst_1103_, lean_object* v_f_1104_, lean_object* v_s_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v___x_1106_ = lean_apply_1(v_f_1104_, v_s_1105_);
v_fst_1107_ = lean_ctor_get(v___x_1106_, 0);
v_snd_1108_ = lean_ctor_get(v___x_1106_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1106_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_inc(v_fst_1107_);
lean_dec(v___x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_fst_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_snd_1108_);
v___x_1113_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_apply_2(v_inst_1103_, lean_box(0), v___x_1113_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_modifyGet(lean_object* v_00_u03b5_1117_, lean_object* v_00_u03c3_1118_, lean_object* v_00_u03b1_1119_, lean_object* v_m_1120_, lean_object* v_inst_1121_, lean_object* v_f_1122_, lean_object* v_s_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v___x_1124_ = lean_apply_1(v_f_1122_, v_s_1123_);
v_fst_1125_ = lean_ctor_get(v___x_1124_, 0);
v_snd_1126_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_inc(v_fst_1125_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_fst_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_snd_1126_);
v___x_1131_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_apply_2(v_inst_1121_, lean_box(0), v___x_1131_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(lean_object* v_inst_1135_, lean_object* v_00_u03b1_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v___x_1139_ = lean_apply_1(v___y_1137_, v___y_1138_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
v_snd_1141_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_1141_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_2(v_inst_1135_, lean_box(0), v___x_1146_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object* v_inst_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_inc(v_inst_1150_);
v___f_1151_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1151_, 0, v_inst_1150_);
lean_inc(v_inst_1150_);
v___x_1152_ = lean_alloc_closure((void*)(l_Lake_EStateT_get), 5, 4);
lean_closure_set(v___x_1152_, 0, lean_box(0));
lean_closure_set(v___x_1152_, 1, lean_box(0));
lean_closure_set(v___x_1152_, 2, lean_box(0));
lean_closure_set(v___x_1152_, 3, v_inst_1150_);
v___x_1153_ = lean_alloc_closure((void*)(l_Lake_EStateT_set___boxed), 6, 4);
lean_closure_set(v___x_1153_, 0, lean_box(0));
lean_closure_set(v___x_1153_, 1, lean_box(0));
lean_closure_set(v___x_1153_, 2, lean_box(0));
lean_closure_set(v___x_1153_, 3, v_inst_1150_);
v___x_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
lean_ctor_set(v___x_1154_, 2, v___f_1151_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadStateOfOfPure(lean_object* v_00_u03b5_1155_, lean_object* v_00_u03c3_1156_, lean_object* v_m_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw___redArg(lean_object* v_inst_1160_, lean_object* v_e_1161_, lean_object* v_s_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_e_1161_);
lean_ctor_set(v___x_1163_, 1, v_s_1162_);
v___x_1164_ = lean_apply_2(v_inst_1160_, lean_box(0), v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_throw(lean_object* v_00_u03b5_1165_, lean_object* v_00_u03c3_1166_, lean_object* v_00_u03b1_1167_, lean_object* v_m_1168_, lean_object* v_inst_1169_, lean_object* v_e_1170_, lean_object* v_s_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_e_1170_);
lean_ctor_set(v___x_1172_, 1, v_s_1171_);
v___x_1173_ = lean_apply_2(v_inst_1169_, lean_box(0), v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg___lam__0(lean_object* v_toPure_1174_, lean_object* v_handle_1175_, lean_object* v_____do__lift_1176_){
_start:
{
if (lean_obj_tag(v_____do__lift_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec(v_handle_1175_);
v___x_1177_ = lean_apply_2(v_toPure_1174_, lean_box(0), v_____do__lift_1176_);
return v___x_1177_;
}
else
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1180_; 
lean_dec(v_toPure_1174_);
v_a_1178_ = lean_ctor_get(v_____do__lift_1176_, 0);
lean_inc(v_a_1178_);
v_a_1179_ = lean_ctor_get(v_____do__lift_1176_, 1);
lean_inc(v_a_1179_);
lean_dec_ref(v_____do__lift_1176_);
v___x_1180_ = lean_apply_2(v_handle_1175_, v_a_1178_, v_a_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch___redArg(lean_object* v_inst_1181_, lean_object* v_x_1182_, lean_object* v_handle_1183_, lean_object* v_s_1184_){
_start:
{
lean_object* v_toApplicative_1185_; lean_object* v_toBind_1186_; lean_object* v_toPure_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; 
v_toApplicative_1185_ = lean_ctor_get(v_inst_1181_, 0);
lean_inc_ref(v_toApplicative_1185_);
v_toBind_1186_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc(v_toBind_1186_);
lean_dec_ref(v_inst_1181_);
v_toPure_1187_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_inc(v_toPure_1187_);
lean_dec_ref(v_toApplicative_1185_);
v___x_1188_ = lean_apply_1(v_x_1182_, v_s_1184_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1189_, 0, v_toPure_1187_);
lean_closure_set(v___f_1189_, 1, v_handle_1183_);
v___x_1190_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1188_, v___f_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryCatch(lean_object* v_00_u03b5_1191_, lean_object* v_00_u03c3_1192_, lean_object* v_00_u03b1_1193_, lean_object* v_m_1194_, lean_object* v_inst_1195_, lean_object* v_x_1196_, lean_object* v_handle_1197_, lean_object* v_s_1198_){
_start:
{
lean_object* v_toApplicative_1199_; lean_object* v_toBind_1200_; lean_object* v_toPure_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; 
v_toApplicative_1199_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_ref(v_toApplicative_1199_);
v_toBind_1200_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc(v_toBind_1200_);
lean_dec_ref(v_inst_1195_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1199_, 1);
lean_inc(v_toPure_1201_);
lean_dec_ref(v_toApplicative_1199_);
v___x_1202_ = lean_apply_1(v_x_1196_, v_s_1198_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v_toPure_1201_);
lean_closure_set(v___f_1203_, 1, v_handle_1197_);
v___x_1204_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v___x_1202_, v___f_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(lean_object* v_toPure_1205_, lean_object* v___y_1206_, lean_object* v_____do__lift_1207_){
_start:
{
if (lean_obj_tag(v_____do__lift_1207_) == 0)
{
lean_object* v___x_1208_; 
lean_dec(v___y_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1205_, lean_box(0), v_____do__lift_1207_);
return v___x_1208_;
}
else
{
lean_object* v_a_1209_; lean_object* v_a_1210_; lean_object* v___x_1211_; 
lean_dec(v_toPure_1205_);
v_a_1209_ = lean_ctor_get(v_____do__lift_1207_, 0);
lean_inc(v_a_1209_);
v_a_1210_ = lean_ctor_get(v_____do__lift_1207_, 1);
lean_inc(v_a_1210_);
lean_dec_ref(v_____do__lift_1207_);
v___x_1211_ = lean_apply_2(v___y_1206_, v_a_1209_, v_a_1210_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(lean_object* v_toPure_1212_, lean_object* v_toBind_1213_, lean_object* v_00_u03b1_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_apply_1(v___y_1215_, v___y_1217_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1219_, 0, v_toPure_1212_);
lean_closure_set(v___f_1219_, 1, v___y_1216_);
v___x_1220_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1218_, v___f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(lean_object* v_toPure_1221_, lean_object* v_00_u03b1_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___y_1223_);
lean_ctor_set(v___x_1225_, 1, v___y_1224_);
v___x_1226_ = lean_apply_2(v_toPure_1221_, lean_box(0), v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(lean_object* v_inst_1227_){
_start:
{
lean_object* v_toApplicative_1228_; lean_object* v_toBind_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1239_; 
v_toApplicative_1228_ = lean_ctor_get(v_inst_1227_, 0);
v_toBind_1229_ = lean_ctor_get(v_inst_1227_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_inst_1227_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1231_ = v_inst_1227_;
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_toBind_1229_);
lean_inc(v_toApplicative_1228_);
lean_dec(v_inst_1227_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_toPure_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1237_; 
v_toPure_1233_ = lean_ctor_get(v_toApplicative_1228_, 1);
lean_inc(v_toPure_1233_);
lean_dec_ref(v_toApplicative_1228_);
lean_inc(v_toPure_1233_);
v___f_1234_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1), 6, 2);
lean_closure_set(v___f_1234_, 0, v_toPure_1233_);
lean_closure_set(v___f_1234_, 1, v_toBind_1229_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2), 4, 1);
lean_closure_set(v___f_1235_, 0, v_toPure_1233_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___f_1234_);
lean_ctor_set(v___x_1231_, 0, v___f_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___f_1234_);
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
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad(lean_object* v_00_u03b5_1240_, lean_object* v_00_u03c3_1241_, lean_object* v_m_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg___lam__0(lean_object* v_toPure_1245_, lean_object* v_x_u2082_1246_, lean_object* v_____do__lift_1247_){
_start:
{
if (lean_obj_tag(v_____do__lift_1247_) == 0)
{
lean_object* v___x_1248_; 
lean_dec(v_x_u2082_1246_);
v___x_1248_ = lean_apply_2(v_toPure_1245_, lean_box(0), v_____do__lift_1247_);
return v___x_1248_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_toPure_1245_);
v_a_1249_ = lean_ctor_get(v_____do__lift_1247_, 1);
lean_inc(v_a_1249_);
lean_dec_ref(v_____do__lift_1247_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_apply_2(v_x_u2082_1246_, v___x_1250_, v_a_1249_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse___redArg(lean_object* v_inst_1252_, lean_object* v_x_u2081_1253_, lean_object* v_x_u2082_1254_, lean_object* v_s_1255_){
_start:
{
lean_object* v_toApplicative_1256_; lean_object* v_toBind_1257_; lean_object* v_toPure_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
v_toApplicative_1256_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc_ref(v_toApplicative_1256_);
v_toBind_1257_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc(v_toBind_1257_);
lean_dec_ref(v_inst_1252_);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1256_, 1);
lean_inc(v_toPure_1258_);
lean_dec_ref(v_toApplicative_1256_);
v___x_1259_ = lean_apply_1(v_x_u2081_1253_, v_s_1255_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1260_, 0, v_toPure_1258_);
lean_closure_set(v___f_1260_, 1, v_x_u2082_1254_);
v___x_1261_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1259_, v___f_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_orElse(lean_object* v_00_u03b5_1262_, lean_object* v_00_u03c3_1263_, lean_object* v_00_u03b1_1264_, lean_object* v_m_1265_, lean_object* v_inst_1266_, lean_object* v_x_u2081_1267_, lean_object* v_x_u2082_1268_, lean_object* v_s_1269_){
_start:
{
lean_object* v_toApplicative_1270_; lean_object* v_toBind_1271_; lean_object* v_toPure_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; 
v_toApplicative_1270_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc_ref(v_toApplicative_1270_);
v_toBind_1271_ = lean_ctor_get(v_inst_1266_, 1);
lean_inc(v_toBind_1271_);
lean_dec_ref(v_inst_1266_);
v_toPure_1272_ = lean_ctor_get(v_toApplicative_1270_, 1);
lean_inc(v_toPure_1272_);
lean_dec_ref(v_toApplicative_1270_);
v___x_1273_ = lean_apply_1(v_x_u2081_1267_, v_s_1269_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1274_, 0, v_toPure_1272_);
lean_closure_set(v___f_1274_, 1, v_x_u2082_1268_);
v___x_1275_ = lean_apply_4(v_toBind_1271_, lean_box(0), lean_box(0), v___x_1273_, v___f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad___redArg(lean_object* v_inst_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1277_, 0, lean_box(0));
lean_closure_set(v___x_1277_, 1, lean_box(0));
lean_closure_set(v___x_1277_, 2, lean_box(0));
lean_closure_set(v___x_1277_, 3, lean_box(0));
lean_closure_set(v___x_1277_, 4, v_inst_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instOrElseOfMonad(lean_object* v_00_u03b5_1278_, lean_object* v_00_u03c3_1279_, lean_object* v_00_u03b1_1280_, lean_object* v_m_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_closure((void*)(l_Lake_EStateT_orElse), 8, 5);
lean_closure_set(v___x_1283_, 0, lean_box(0));
lean_closure_set(v___x_1283_, 1, lean_box(0));
lean_closure_set(v___x_1283_, 2, lean_box(0));
lean_closure_set(v___x_1283_, 3, lean_box(0));
lean_closure_set(v___x_1283_, 4, v_inst_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg___lam__0(lean_object* v_f_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_f_1284_);
v_a_1286_ = lean_ctor_get(v_x_1285_, 0);
v_a_1287_ = lean_ctor_get(v_x_1285_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v_x_1285_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_inc(v_a_1286_);
lean_dec(v_x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1286_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1304_; 
v_a_1295_ = lean_ctor_get(v_x_1285_, 0);
v_a_1296_ = lean_ctor_get(v_x_1285_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1298_ = v_x_1285_;
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_inc(v_a_1295_);
lean_dec(v_x_1285_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_apply_1(v_f_1284_, v_a_1295_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_a_1296_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept___redArg(lean_object* v_inst_1305_, lean_object* v_f_1306_, lean_object* v_x_1307_, lean_object* v_s_1308_){
_start:
{
lean_object* v_map_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_map_1309_ = lean_ctor_get(v_inst_1305_, 0);
lean_inc(v_map_1309_);
lean_dec_ref(v_inst_1305_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1310_, 0, v_f_1306_);
v___x_1311_ = lean_apply_1(v_x_1307_, v_s_1308_);
v___x_1312_ = lean_apply_4(v_map_1309_, lean_box(0), lean_box(0), v___f_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_adaptExcept(lean_object* v_00_u03b5_1313_, lean_object* v_00_u03b5_x27_1314_, lean_object* v_00_u03c3_1315_, lean_object* v_00_u03b1_1316_, lean_object* v_m_1317_, lean_object* v_inst_1318_, lean_object* v_f_1319_, lean_object* v_x_1320_, lean_object* v_s_1321_){
_start:
{
lean_object* v_map_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_map_1322_ = lean_ctor_get(v_inst_1318_, 0);
lean_inc(v_map_1322_);
lean_dec_ref(v_inst_1318_);
v___f_1323_ = lean_alloc_closure((void*)(l_Lake_EStateT_adaptExcept___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1323_, 0, v_f_1319_);
v___x_1324_ = lean_apply_1(v_x_1320_, v_s_1321_);
v___x_1325_ = lean_apply_4(v_map_1322_, lean_box(0), lean_box(0), v___f_1323_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__0(lean_object* v_a_1326_, lean_object* v_toPure_1327_, lean_object* v_____do__lift_1328_){
_start:
{
if (lean_obj_tag(v_____do__lift_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1339_; 
v_a_1329_ = lean_ctor_get(v_____do__lift_1328_, 0);
v_a_1330_ = lean_ctor_get(v_____do__lift_1328_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_____do__lift_1328_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1332_ = v_____do__lift_1328_;
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_inc(v_a_1329_);
lean_dec(v_____do__lift_1328_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1326_);
lean_ctor_set(v___x_1334_, 1, v_a_1329_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_a_1330_);
v___x_1336_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1336_);
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_a_1326_);
v_a_1340_ = lean_ctor_get(v_____do__lift_1328_, 0);
v_a_1341_ = lean_ctor_get(v_____do__lift_1328_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_____do__lift_1328_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v_____do__lift_1328_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_inc(v_a_1340_);
lean_dec(v_____do__lift_1328_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1340_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1346_);
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__1(lean_object* v_a_1350_, lean_object* v_toPure_1351_, lean_object* v_____do__lift_1352_){
_start:
{
if (lean_obj_tag(v_____do__lift_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v_____do__lift_1352_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_____do__lift_1352_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_____do__lift_1352_, 0);
lean_dec(v_unused_1362_);
v___x_1355_ = v_____do__lift_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v_____do__lift_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v_a_1350_);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_apply_2(v_toPure_1351_, lean_box(0), v___x_1358_);
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_a_1350_);
v_a_1363_ = lean_ctor_get(v_____do__lift_1352_, 0);
v_a_1364_ = lean_ctor_get(v_____do__lift_1352_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_____do__lift_1352_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1366_ = v_____do__lift_1352_;
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_inc(v_a_1363_);
lean_dec(v_____do__lift_1352_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1363_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_apply_2(v_toPure_1351_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg___lam__2(lean_object* v_toPure_1373_, lean_object* v_f_1374_, lean_object* v_toBind_1375_, lean_object* v_r_1376_){
_start:
{
if (lean_obj_tag(v_r_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v_a_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1377_ = lean_ctor_get(v_r_1376_, 0);
lean_inc(v_a_1377_);
v_a_1378_ = lean_ctor_get(v_r_1376_, 1);
lean_inc(v_a_1378_);
lean_dec_ref(v_r_1376_);
lean_inc(v_a_1377_);
v___f_1379_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1379_, 0, v_a_1377_);
lean_closure_set(v___f_1379_, 1, v_toPure_1373_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1377_);
v___x_1381_ = lean_apply_2(v_f_1374_, v___x_1380_, v_a_1378_);
v___x_1382_ = lean_apply_4(v_toBind_1375_, lean_box(0), lean_box(0), v___x_1381_, v___f_1379_);
return v___x_1382_;
}
else
{
lean_object* v_a_1383_; lean_object* v_a_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1383_ = lean_ctor_get(v_r_1376_, 0);
lean_inc(v_a_1383_);
v_a_1384_ = lean_ctor_get(v_r_1376_, 1);
lean_inc(v_a_1384_);
lean_dec_ref(v_r_1376_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1385_, 0, v_a_1383_);
lean_closure_set(v___f_1385_, 1, v_toPure_1373_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_apply_2(v_f_1374_, v___x_1386_, v_a_1384_);
v___x_1388_ = lean_apply_4(v_toBind_1375_, lean_box(0), lean_box(0), v___x_1387_, v___f_1385_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27___redArg(lean_object* v_inst_1389_, lean_object* v_x_1390_, lean_object* v_f_1391_, lean_object* v_s_1392_){
_start:
{
lean_object* v_toApplicative_1393_; lean_object* v_toBind_1394_; lean_object* v_toPure_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; 
v_toApplicative_1393_ = lean_ctor_get(v_inst_1389_, 0);
lean_inc_ref(v_toApplicative_1393_);
v_toBind_1394_ = lean_ctor_get(v_inst_1389_, 1);
lean_inc(v_toBind_1394_);
lean_dec_ref(v_inst_1389_);
v_toPure_1395_ = lean_ctor_get(v_toApplicative_1393_, 1);
lean_inc(v_toPure_1395_);
lean_dec_ref(v_toApplicative_1393_);
v___x_1396_ = lean_apply_1(v_x_1390_, v_s_1392_);
lean_inc(v_toBind_1394_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1397_, 0, v_toPure_1395_);
lean_closure_set(v___f_1397_, 1, v_f_1391_);
lean_closure_set(v___f_1397_, 2, v_toBind_1394_);
v___x_1398_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1396_, v___f_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_tryFinally_x27(lean_object* v_00_u03b5_1399_, lean_object* v_00_u03c3_1400_, lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_m_1403_, lean_object* v_inst_1404_, lean_object* v_x_1405_, lean_object* v_f_1406_, lean_object* v_s_1407_){
_start:
{
lean_object* v_toApplicative_1408_; lean_object* v_toBind_1409_; lean_object* v_toPure_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; 
v_toApplicative_1408_ = lean_ctor_get(v_inst_1404_, 0);
lean_inc_ref(v_toApplicative_1408_);
v_toBind_1409_ = lean_ctor_get(v_inst_1404_, 1);
lean_inc(v_toBind_1409_);
lean_dec_ref(v_inst_1404_);
v_toPure_1410_ = lean_ctor_get(v_toApplicative_1408_, 1);
lean_inc(v_toPure_1410_);
lean_dec_ref(v_toApplicative_1408_);
v___x_1411_ = lean_apply_1(v_x_1405_, v_s_1407_);
lean_inc(v_toBind_1409_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1412_, 0, v_toPure_1410_);
lean_closure_set(v___f_1412_, 1, v_f_1406_);
lean_closure_set(v___f_1412_, 2, v_toBind_1409_);
v___x_1413_ = lean_apply_4(v_toBind_1409_, lean_box(0), lean_box(0), v___x_1411_, v___f_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(lean_object* v_toPure_1414_, lean_object* v___y_1415_, lean_object* v_toBind_1416_, lean_object* v_r_1417_){
_start:
{
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v_a_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1418_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_a_1418_);
v_a_1419_ = lean_ctor_get(v_r_1417_, 1);
lean_inc(v_a_1419_);
lean_dec_ref(v_r_1417_);
lean_inc(v_a_1418_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1420_, 0, v_a_1418_);
lean_closure_set(v___f_1420_, 1, v_toPure_1414_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1418_);
v___x_1422_ = lean_apply_2(v___y_1415_, v___x_1421_, v_a_1419_);
v___x_1423_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1422_, v___f_1420_);
return v___x_1423_;
}
else
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1424_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_a_1424_);
v_a_1425_ = lean_ctor_get(v_r_1417_, 1);
lean_inc(v_a_1425_);
lean_dec_ref(v_r_1417_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lake_EStateT_tryFinally_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1426_, 0, v_a_1424_);
lean_closure_set(v___f_1426_, 1, v_toPure_1414_);
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_apply_2(v___y_1415_, v___x_1427_, v_a_1425_);
v___x_1429_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1428_, v___f_1426_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(lean_object* v_inst_1430_, lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_toApplicative_1436_; lean_object* v_toBind_1437_; lean_object* v_toPure_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; 
v_toApplicative_1436_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1436_);
v_toBind_1437_ = lean_ctor_get(v_inst_1430_, 1);
lean_inc(v_toBind_1437_);
lean_dec_ref(v_inst_1430_);
v_toPure_1438_ = lean_ctor_get(v_toApplicative_1436_, 1);
lean_inc(v_toPure_1438_);
lean_dec_ref(v_toApplicative_1436_);
v___x_1439_ = lean_apply_1(v___y_1433_, v___y_1435_);
lean_inc(v_toBind_1437_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1440_, 0, v_toPure_1438_);
lean_closure_set(v___f_1440_, 1, v___y_1434_);
lean_closure_set(v___f_1440_, 2, v_toBind_1437_);
v___x_1441_ = lean_apply_4(v_toBind_1437_, lean_box(0), lean_box(0), v___x_1439_, v___f_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg(lean_object* v_inst_1442_){
_start:
{
lean_object* v___f_1443_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1443_, 0, v_inst_1442_);
return v___f_1443_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_instMonadFinallyOfMonad(lean_object* v_00_u03b5_1444_, lean_object* v_00_u03c3_1445_, lean_object* v_m_1446_, lean_object* v_inst_1447_){
_start:
{
lean_object* v___f_1448_; 
v___f_1448_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1448_, 0, v_inst_1447_);
return v___f_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM___redArg(lean_object* v_f_1449_, lean_object* v_s_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_apply_1(v_f_1449_, v_s_1450_);
v___x_1452_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_ofEStateM(lean_object* v_00_u03b5_1453_, lean_object* v_00_u03c3_1454_, lean_object* v_00_u03b1_1455_, lean_object* v_f_1456_, lean_object* v_s_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lake_EStateT_ofEStateM___redArg(v_f_1456_, v_s_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM___redArg(lean_object* v_f_1459_, lean_object* v_s_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_apply_1(v_f_1459_, v_s_1460_);
v___x_1462_ = l_Lake_EResult_toEStateMResult___redArg(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lake_EStateT_toEStateM(lean_object* v_00_u03b5_1463_, lean_object* v_00_u03c3_1464_, lean_object* v_00_u03b1_1465_, lean_object* v_f_1466_, lean_object* v_s_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lake_EStateT_toEStateM___redArg(v_f_1466_, v_s_1467_);
return v___x_1468_;
}
}
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_EStateT(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
