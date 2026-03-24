// Lean compiler output
// Module: Init.Control.Except
// Imports: public import Init.Control.Basic public import Init.Control.Id
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
LEAN_EXPORT lean_object* l_Except_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Except_0__Except_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Except_0__Except_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_mapError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_mapError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toBool___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Except_toBool___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Except_toBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_isOk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Except_isOk___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Except_isOk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_isOk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Except_toOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_tryCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_orElseLazy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Except_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___closed__0 = (const lean_object*)&l_Except_instMonad___closed__0_value;
static const lean_closure_object l_Except_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___closed__1 = (const lean_object*)&l_Except_instMonad___closed__1_value;
static const lean_closure_object l_Except_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___closed__2 = (const lean_object*)&l_Except_instMonad___closed__2_value;
static const lean_closure_object l_Except_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___closed__3 = (const lean_object*)&l_Except_instMonad___closed__3_value;
static const lean_closure_object l_Except_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___closed__4 = (const lean_object*)&l_Except_instMonad___closed__4_value;
static const lean_ctor_object l_Except_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___closed__4_value),((lean_object*)&l_Except_instMonad___closed__0_value)}};
static const lean_object* l_Except_instMonad___closed__5 = (const lean_object*)&l_Except_instMonad___closed__5_value;
static const lean_closure_object l_Except_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___closed__6 = (const lean_object*)&l_Except_instMonad___closed__6_value;
static const lean_ctor_object l_Except_instMonad___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___closed__5_value),((lean_object*)&l_Except_instMonad___closed__6_value),((lean_object*)&l_Except_instMonad___closed__1_value),((lean_object*)&l_Except_instMonad___closed__2_value),((lean_object*)&l_Except_instMonad___closed__3_value)}};
static const lean_object* l_Except_instMonad___closed__7 = (const lean_object*)&l_Except_instMonad___closed__7_value;
static const lean_closure_object l_Except_instMonad___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___closed__8 = (const lean_object*)&l_Except_instMonad___closed__8_value;
static const lean_ctor_object l_Except_instMonad___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___closed__7_value),((lean_object*)&l_Except_instMonad___closed__8_value)}};
static const lean_object* l_Except_instMonad___closed__9 = (const lean_object*)&l_Except_instMonad___closed__9_value;
LEAN_EXPORT lean_object* l_Except_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_runCatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg___lam__0(lean_object*);
static const lean_closure_object l_ExceptT_lift___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptT_lift___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptT_lift___redArg___closed__0 = (const lean_object*)&l_ExceptT_lift___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ExceptT_instMonadFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptT_instMonadFunctor___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptT_instMonadFunctor___closed__0 = (const lean_object*)&l_ExceptT_instMonadFunctor___closed__0_value;
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_adapt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfExcept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfExcept___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadExceptOfExcept___closed__0 = (const lean_object*)&l_instMonadExceptOfExcept___closed__0_value;
static const lean_closure_object l_instMonadExceptOfExcept___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_tryCatch, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfExcept___closed__1 = (const lean_object*)&l_instMonadExceptOfExcept___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfExcept___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfExcept___closed__0_value),((lean_object*)&l_instMonadExceptOfExcept___closed__1_value)}};
static const lean_object* l_instMonadExceptOfExcept___closed__2 = (const lean_object*)&l_instMonadExceptOfExcept___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_observing___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_observing___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_observing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_observing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMonadControlExceptTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlExceptTOfMonad___redArg___closed__0 = (const lean_object*)&l_instMonadControlExceptTOfMonad___redArg___closed__0_value;
static const lean_closure_object l_instMonadControlExceptTOfMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlExceptTOfMonad___redArg___closed__1 = (const lean_object*)&l_instMonadControlExceptTOfMonad___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_tryFinally___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_tryFinally___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_tryFinally___redArg___closed__0 = (const lean_object*)&l_tryFinally___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_tryFinally___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tryFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Id_finally___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Id_finally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_finally___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Id_finally___closed__0 = (const lean_object*)&l_Id_finally___closed__0_value;
LEAN_EXPORT const lean_object* l_Id_finally = (const lean_object*)&l_Id_finally___closed__0_value;
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachExceptTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachExceptTOfMonad___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachExceptTOfMonad___redArg___closed__0 = (const lean_object*)&l_instMonadAttachExceptTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_pure___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Except_pure(lean_object* v_00_u03b5_3_, lean_object* v_00_u03b1_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_a_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Except_map___redArg(lean_object* v_f_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
lean_dec(v_f_7_);
v_a_9_ = lean_ctor_get(v_x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v_x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_a_17_ = lean_ctor_get(v_x_8_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_25_ == 0)
{
v___x_19_ = v_x_8_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v_x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_apply_1(v_f_7_, v_a_17_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_21_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_map(lean_object* v_00_u03b5_26_, lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_f_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
lean_dec(v_f_29_);
v_a_31_ = lean_ctor_get(v_x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v_x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v_x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_a_39_ = lean_ctor_get(v_x_30_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_30_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v_x_30_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v_x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = lean_apply_1(v_f_29_, v_a_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Except_0__Except_map_match__1_splitter___redArg(lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_50_);
v_a_51_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_a_51_);
lean_dec_ref(v_x_48_);
v___x_52_ = lean_apply_1(v_h__1_49_, v_a_51_);
return v___x_52_;
}
else
{
lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_49_);
v_a_53_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_a_53_);
lean_dec_ref(v_x_48_);
v___x_54_ = lean_apply_1(v_h__2_50_, v_a_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Except_0__Except_map_match__1_splitter(lean_object* v_00_u03b5_55_, lean_object* v_00_u03b1_56_, lean_object* v_motive_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_60_);
v_a_61_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v_x_58_);
v___x_62_ = lean_apply_1(v_h__1_59_, v_a_61_);
return v___x_62_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_59_);
v_a_63_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_a_63_);
lean_dec_ref(v_x_58_);
v___x_64_ = lean_apply_1(v_h__2_60_, v_a_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Except_mapError___redArg(lean_object* v_f_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_a_67_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v_x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v_x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_apply_1(v_f_65_, v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_f_65_);
v_a_76_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v_x_66_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v_x_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_mapError(lean_object* v_00_u03b5_84_, lean_object* v_00_u03b5_x27_85_, lean_object* v_00_u03b1_86_, lean_object* v_f_87_, lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_a_89_ = lean_ctor_get(v_x_88_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v_x_88_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v_x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_apply_1(v_f_87_, v_a_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_f_87_);
v_a_98_ = lean_ctor_get(v_x_88_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v_x_88_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v_x_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_bind___redArg(lean_object* v_ma_106_, lean_object* v_f_107_){
_start:
{
if (lean_obj_tag(v_ma_106_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_f_107_);
v_a_108_ = lean_ctor_get(v_ma_106_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v_ma_106_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v_ma_106_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v_ma_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_116_ = lean_ctor_get(v_ma_106_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v_ma_106_);
v___x_117_ = lean_apply_1(v_f_107_, v_a_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Except_bind(lean_object* v_00_u03b5_118_, lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_ma_121_, lean_object* v_f_122_){
_start:
{
if (lean_obj_tag(v_ma_121_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec_ref(v_f_122_);
v_a_123_ = lean_ctor_get(v_ma_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_ma_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v_ma_121_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v_ma_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
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
lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_131_ = lean_ctor_get(v_ma_121_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v_ma_121_);
v___x_132_ = lean_apply_1(v_f_122_, v_a_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT uint8_t l_Except_toBool___redArg(lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 1;
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toBool___redArg___boxed(lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Except_toBool___redArg(v_x_136_);
lean_dec_ref(v_x_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Except_toBool(lean_object* v_00_u03b5_139_, lean_object* v_00_u03b1_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 1;
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toBool___boxed(lean_object* v_00_u03b5_144_, lean_object* v_00_u03b1_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Except_toBool(v_00_u03b5_144_, v_00_u03b1_145_, v_x_146_);
lean_dec_ref(v_x_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Except_isOk___redArg(lean_object* v_a_149_){
_start:
{
if (lean_obj_tag(v_a_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 1;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Except_isOk___redArg___boxed(lean_object* v_a_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Except_isOk___redArg(v_a_152_);
lean_dec_ref(v_a_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Except_isOk(lean_object* v_00_u03b5_155_, lean_object* v_00_u03b1_156_, lean_object* v_a_157_){
_start:
{
if (lean_obj_tag(v_a_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 1;
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Except_isOk___boxed(lean_object* v_00_u03b5_160_, lean_object* v_00_u03b1_161_, lean_object* v_a_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Except_isOk(v_00_u03b5_160_, v_00_u03b1_161_, v_a_162_);
lean_dec_ref(v_a_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_Except_toOption___redArg(lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_166_; 
lean_dec_ref(v_x_165_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v_x_165_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v_x_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toOption(lean_object* v_00_u03b5_175_, lean_object* v_00_u03b1_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_178_; 
lean_dec_ref(v_x_177_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v_x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v_x_177_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v_x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch___redArg(lean_object* v_ma_187_, lean_object* v_handle_188_){
_start:
{
if (lean_obj_tag(v_ma_187_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; 
v_a_189_ = lean_ctor_get(v_ma_187_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v_ma_187_);
v___x_190_ = lean_apply_1(v_handle_188_, v_a_189_);
return v___x_190_;
}
else
{
lean_dec_ref(v_handle_188_);
return v_ma_187_;
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object* v_00_u03b5_191_, lean_object* v_00_u03b1_192_, lean_object* v_ma_193_, lean_object* v_handle_194_){
_start:
{
if (lean_obj_tag(v_ma_193_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_ctor_get(v_ma_193_, 0);
lean_inc(v_a_195_);
lean_dec_ref(v_ma_193_);
v___x_196_ = lean_apply_1(v_handle_194_, v_a_195_);
return v___x_196_;
}
else
{
lean_dec_ref(v_handle_194_);
return v_ma_193_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg(lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_y_198_, v___x_199_);
return v___x_200_;
}
else
{
lean_dec_ref(v_y_198_);
lean_inc_ref(v_x_197_);
return v_x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg___boxed(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Except_orElseLazy___redArg(v_x_201_, v_y_202_);
lean_dec_ref(v_x_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object* v_00_u03b5_204_, lean_object* v_00_u03b1_205_, lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Except_orElseLazy___redArg(v_x_206_, v_y_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___boxed(lean_object* v_00_u03b5_209_, lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v_y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Except_orElseLazy(v_00_u03b5_209_, v_00_u03b1_210_, v_x_211_, v_y_212_);
lean_dec_ref(v_x_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__0(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
if (lean_obj_tag(v___y_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v___y_216_);
v_a_218_ = lean_ctor_get(v___y_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___y_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___y_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___y_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_isSharedCheck_232_ = !lean_is_exclusive(v___y_217_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___y_217_, 0);
lean_dec(v_unused_233_);
v___x_227_ = v___y_217_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_dec(v___y_217_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___y_216_);
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___y_216_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__1(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_f_236_, lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_f_236_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v_x_237_);
v_a_238_ = lean_ctor_get(v_f_236_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_f_236_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v_f_236_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v_f_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_a_246_ = lean_ctor_get(v_f_236_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v_f_236_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_x_237_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec(v_a_246_);
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_a_257_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_apply_1(v_a_246_, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_x_268_, lean_object* v_y_269_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_dec_ref(v_y_269_);
lean_inc_ref(v_x_268_);
return v_x_268_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_y_269_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_dec_ref(v___x_271_);
lean_inc_ref(v_x_268_);
return v_x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2___boxed(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_x_282_, lean_object* v_y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Except_instMonad___lam__2(v_00_u03b1_280_, v_00_u03b2_281_, v_x_282_, v_y_283_);
lean_dec_ref(v_x_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__3(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_x_287_, lean_object* v_y_288_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_y_288_);
v_a_289_ = lean_ctor_get(v_x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v_x_287_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v_x_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_x_287_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_apply_1(v_y_288_, v___x_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad(lean_object* v_00_u03b5_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_Except_instMonad___closed__9));
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg(lean_object* v_x_320_){
_start:
{
lean_inc(v_x_320_);
return v_x_320_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg___boxed(lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_ExceptT_mk___redArg(v_x_321_);
lean_dec(v_x_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object* v_00_u03b5_323_, lean_object* v_m_324_, lean_object* v_00_u03b1_325_, lean_object* v_x_326_){
_start:
{
lean_inc(v_x_326_);
return v_x_326_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___boxed(lean_object* v_00_u03b5_327_, lean_object* v_m_328_, lean_object* v_00_u03b1_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_ExceptT_mk(v_00_u03b5_327_, v_m_328_, v_00_u03b1_329_, v_x_330_);
lean_dec(v_x_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg(lean_object* v_x_332_){
_start:
{
lean_inc(v_x_332_);
return v_x_332_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg___boxed(lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_ExceptT_run___redArg(v_x_333_);
lean_dec(v_x_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object* v_00_u03b5_335_, lean_object* v_m_336_, lean_object* v_00_u03b1_337_, lean_object* v_x_338_){
_start:
{
lean_inc(v_x_338_);
return v_x_338_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___boxed(lean_object* v_00_u03b5_339_, lean_object* v_m_340_, lean_object* v_00_u03b1_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_ExceptT_run(v_00_u03b5_339_, v_m_340_, v_00_u03b1_341_, v_x_342_);
lean_dec(v_x_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg___lam__0(lean_object* v_error_344_, lean_object* v_ok_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
lean_dec(v_ok_345_);
v_a_347_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v_x_346_);
v___x_348_ = lean_apply_1(v_error_344_, v_a_347_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v___x_350_; 
lean_dec(v_error_344_);
v_a_349_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_a_349_);
lean_dec_ref(v_x_346_);
v___x_350_ = lean_apply_1(v_ok_345_, v_a_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg(lean_object* v_inst_351_, lean_object* v_x_352_, lean_object* v_ok_353_, lean_object* v_error_354_){
_start:
{
lean_object* v_toBind_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v_toBind_355_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_toBind_355_);
lean_dec_ref(v_inst_351_);
v___f_356_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_356_, 0, v_error_354_);
lean_closure_set(v___f_356_, 1, v_ok_353_);
v___x_357_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v_x_352_, v___f_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK(lean_object* v_m_358_, lean_object* v_00_u03b5_359_, lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_inst_362_, lean_object* v_x_363_, lean_object* v_ok_364_, lean_object* v_error_365_){
_start:
{
lean_object* v_toBind_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
v_toBind_366_ = lean_ctor_get(v_inst_362_, 1);
lean_inc(v_toBind_366_);
lean_dec_ref(v_inst_362_);
v___f_367_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_367_, 0, v_error_365_);
lean_closure_set(v___f_367_, 1, v_ok_364_);
v___x_368_ = lean_apply_4(v_toBind_366_, lean_box(0), lean_box(0), v_x_363_, v___f_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg___lam__0(lean_object* v_toPure_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_a_371_; lean_object* v___x_372_; 
v_a_371_ = lean_ctor_get(v_x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref(v_x_370_);
v___x_372_ = lean_apply_2(v_toPure_369_, lean_box(0), v_a_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg(lean_object* v_inst_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_toApplicative_375_; lean_object* v_toBind_376_; lean_object* v_toPure_377_; lean_object* v___f_378_; lean_object* v___x_379_; 
v_toApplicative_375_ = lean_ctor_get(v_inst_373_, 0);
lean_inc_ref(v_toApplicative_375_);
v_toBind_376_ = lean_ctor_get(v_inst_373_, 1);
lean_inc(v_toBind_376_);
lean_dec_ref(v_inst_373_);
v_toPure_377_ = lean_ctor_get(v_toApplicative_375_, 1);
lean_inc(v_toPure_377_);
lean_dec_ref(v_toApplicative_375_);
v___f_378_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_378_, 0, v_toPure_377_);
v___x_379_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v_x_374_, v___f_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch(lean_object* v_m_380_, lean_object* v_00_u03b1_381_, lean_object* v_inst_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_toApplicative_384_; lean_object* v_toBind_385_; lean_object* v_toPure_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_toApplicative_384_ = lean_ctor_get(v_inst_382_, 0);
lean_inc_ref(v_toApplicative_384_);
v_toBind_385_ = lean_ctor_get(v_inst_382_, 1);
lean_inc(v_toBind_385_);
lean_dec_ref(v_inst_382_);
v_toPure_386_ = lean_ctor_get(v_toApplicative_384_, 1);
lean_inc(v_toPure_386_);
lean_dec_ref(v_toApplicative_384_);
v___f_387_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_387_, 0, v_toPure_386_);
v___x_388_ = lean_apply_4(v_toBind_385_, lean_box(0), lean_box(0), v_x_383_, v___f_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure___redArg(lean_object* v_inst_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_toApplicative_391_; lean_object* v_toPure_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_toApplicative_391_ = lean_ctor_get(v_inst_389_, 0);
lean_inc_ref(v_toApplicative_391_);
lean_dec_ref(v_inst_389_);
v_toPure_392_ = lean_ctor_get(v_toApplicative_391_, 1);
lean_inc(v_toPure_392_);
lean_dec_ref(v_toApplicative_391_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_a_390_);
v___x_394_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object* v_00_u03b5_395_, lean_object* v_m_396_, lean_object* v_inst_397_, lean_object* v_00_u03b1_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toPure_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_397_, 0);
lean_inc_ref(v_toApplicative_400_);
lean_dec_ref(v_inst_397_);
v_toPure_401_ = lean_ctor_get(v_toApplicative_400_, 1);
lean_inc(v_toPure_401_);
lean_dec_ref(v_toApplicative_400_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_a_399_);
v___x_403_ = lean_apply_2(v_toPure_401_, lean_box(0), v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___redArg(lean_object* v_inst_404_, lean_object* v_f_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_toApplicative_407_; 
v_toApplicative_407_ = lean_ctor_get(v_inst_404_, 0);
lean_inc_ref(v_toApplicative_407_);
lean_dec_ref(v_inst_404_);
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v_toPure_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_f_405_);
v_toPure_408_ = lean_ctor_get(v_toApplicative_407_, 1);
lean_inc(v_toPure_408_);
lean_dec_ref(v_toApplicative_407_);
v_a_409_ = lean_ctor_get(v_x_406_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_417_ == 0)
{
v___x_411_ = v_x_406_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v_x_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_apply_2(v_toPure_408_, lean_box(0), v___x_414_);
return v___x_415_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_419_; 
lean_dec_ref(v_toApplicative_407_);
v_a_418_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v_x_406_);
v___x_419_ = lean_apply_1(v_f_405_, v_a_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object* v_00_u03b5_420_, lean_object* v_m_421_, lean_object* v_inst_422_, lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_f_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_toApplicative_427_; 
v_toApplicative_427_ = lean_ctor_get(v_inst_422_, 0);
lean_inc_ref(v_toApplicative_427_);
lean_dec_ref(v_inst_422_);
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_toPure_428_; lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_f_425_);
v_toPure_428_ = lean_ctor_get(v_toApplicative_427_, 1);
lean_inc(v_toPure_428_);
lean_dec_ref(v_toApplicative_427_);
v_a_429_ = lean_ctor_get(v_x_426_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v_x_426_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v_x_426_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_apply_2(v_toPure_428_, lean_box(0), v___x_434_);
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_439_; 
lean_dec_ref(v_toApplicative_427_);
v_a_438_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v_x_426_);
v___x_439_ = lean_apply_1(v_f_425_, v_a_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind___redArg(lean_object* v_inst_440_, lean_object* v_ma_441_, lean_object* v_f_442_){
_start:
{
lean_object* v_toBind_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_toBind_443_ = lean_ctor_get(v_inst_440_, 1);
lean_inc(v_toBind_443_);
v___x_444_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_444_, 0, lean_box(0));
lean_closure_set(v___x_444_, 1, lean_box(0));
lean_closure_set(v___x_444_, 2, v_inst_440_);
lean_closure_set(v___x_444_, 3, lean_box(0));
lean_closure_set(v___x_444_, 4, lean_box(0));
lean_closure_set(v___x_444_, 5, v_f_442_);
v___x_445_ = lean_apply_4(v_toBind_443_, lean_box(0), lean_box(0), v_ma_441_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object* v_00_u03b5_446_, lean_object* v_m_447_, lean_object* v_inst_448_, lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_ma_451_, lean_object* v_f_452_){
_start:
{
lean_object* v_toBind_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_toBind_453_ = lean_ctor_get(v_inst_448_, 1);
lean_inc(v_toBind_453_);
v___x_454_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_454_, 0, lean_box(0));
lean_closure_set(v___x_454_, 1, lean_box(0));
lean_closure_set(v___x_454_, 2, v_inst_448_);
lean_closure_set(v___x_454_, 3, lean_box(0));
lean_closure_set(v___x_454_, 4, lean_box(0));
lean_closure_set(v___x_454_, 5, v_f_452_);
v___x_455_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v_ma_451_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg___lam__0(lean_object* v_toPure_456_, lean_object* v_f_457_, lean_object* v_a_458_){
_start:
{
if (lean_obj_tag(v_a_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_f_457_);
v_a_459_ = lean_ctor_get(v_a_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v_a_458_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v_a_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = lean_apply_2(v_toPure_456_, lean_box(0), v___x_464_);
return v___x_465_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_a_468_ = lean_ctor_get(v_a_458_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_a_458_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v_a_458_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_apply_1(v_f_457_, v_a_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_472_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_476_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_apply_2(v_toPure_456_, lean_box(0), v___x_474_);
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg(lean_object* v_inst_478_, lean_object* v_f_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_toApplicative_481_; lean_object* v_toBind_482_; lean_object* v_toPure_483_; lean_object* v___f_484_; lean_object* v___x_485_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc_ref(v_toApplicative_481_);
v_toBind_482_ = lean_ctor_get(v_inst_478_, 1);
lean_inc(v_toBind_482_);
lean_dec_ref(v_inst_478_);
v_toPure_483_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_483_);
lean_dec_ref(v_toApplicative_481_);
v___f_484_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_484_, 0, v_toPure_483_);
lean_closure_set(v___f_484_, 1, v_f_479_);
v___x_485_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v_x_480_, v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object* v_00_u03b5_486_, lean_object* v_m_487_, lean_object* v_inst_488_, lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_f_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_toApplicative_493_; lean_object* v_toBind_494_; lean_object* v_toPure_495_; lean_object* v___f_496_; lean_object* v___x_497_; 
v_toApplicative_493_ = lean_ctor_get(v_inst_488_, 0);
lean_inc_ref(v_toApplicative_493_);
v_toBind_494_ = lean_ctor_get(v_inst_488_, 1);
lean_inc(v_toBind_494_);
lean_dec_ref(v_inst_488_);
v_toPure_495_ = lean_ctor_get(v_toApplicative_493_, 1);
lean_inc(v_toPure_495_);
lean_dec_ref(v_toApplicative_493_);
v___f_496_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_496_, 0, v_toPure_495_);
lean_closure_set(v___f_496_, 1, v_f_491_);
v___x_497_ = lean_apply_4(v_toBind_494_, lean_box(0), lean_box(0), v_x_492_, v___f_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg___lam__0(lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg(lean_object* v_inst_501_, lean_object* v_t_502_){
_start:
{
lean_object* v_toApplicative_503_; lean_object* v_toFunctor_504_; lean_object* v_map_505_; lean_object* v___f_506_; lean_object* v___x_507_; 
v_toApplicative_503_ = lean_ctor_get(v_inst_501_, 0);
lean_inc_ref(v_toApplicative_503_);
lean_dec_ref(v_inst_501_);
v_toFunctor_504_ = lean_ctor_get(v_toApplicative_503_, 0);
lean_inc_ref(v_toFunctor_504_);
lean_dec_ref(v_toApplicative_503_);
v_map_505_ = lean_ctor_get(v_toFunctor_504_, 0);
lean_inc(v_map_505_);
lean_dec_ref(v_toFunctor_504_);
v___f_506_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_507_ = lean_apply_4(v_map_505_, lean_box(0), lean_box(0), v___f_506_, v_t_502_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object* v_00_u03b5_508_, lean_object* v_m_509_, lean_object* v_inst_510_, lean_object* v_00_u03b1_511_, lean_object* v_t_512_){
_start:
{
lean_object* v_toApplicative_513_; lean_object* v_toFunctor_514_; lean_object* v_map_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v_toApplicative_513_ = lean_ctor_get(v_inst_510_, 0);
lean_inc_ref(v_toApplicative_513_);
lean_dec_ref(v_inst_510_);
v_toFunctor_514_ = lean_ctor_get(v_toApplicative_513_, 0);
lean_inc_ref(v_toFunctor_514_);
lean_dec_ref(v_toApplicative_513_);
v_map_515_ = lean_ctor_get(v_toFunctor_514_, 0);
lean_inc(v_map_515_);
lean_dec_ref(v_toFunctor_514_);
v___f_516_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_517_ = lean_apply_4(v_map_515_, lean_box(0), lean_box(0), v___f_516_, v_t_512_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg___lam__0(lean_object* v_toPure_518_, lean_object* v_00_u03b1_519_, lean_object* v_e_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_apply_2(v_toPure_518_, lean_box(0), v_e_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg(lean_object* v_inst_522_){
_start:
{
lean_object* v_toApplicative_523_; lean_object* v_toPure_524_; lean_object* v___f_525_; 
v_toApplicative_523_ = lean_ctor_get(v_inst_522_, 0);
lean_inc_ref(v_toApplicative_523_);
lean_dec_ref(v_inst_522_);
v_toPure_524_ = lean_ctor_get(v_toApplicative_523_, 1);
lean_inc(v_toPure_524_);
lean_dec_ref(v_toApplicative_523_);
v___f_525_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_525_, 0, v_toPure_524_);
return v___f_525_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept(lean_object* v_00_u03b5_526_, lean_object* v_m_527_, lean_object* v_inst_528_){
_start:
{
lean_object* v_toApplicative_529_; lean_object* v_toPure_530_; lean_object* v___f_531_; 
v_toApplicative_529_ = lean_ctor_get(v_inst_528_, 0);
lean_inc_ref(v_toApplicative_529_);
lean_dec_ref(v_inst_528_);
v_toPure_530_ = lean_ctor_get(v_toApplicative_529_, 1);
lean_inc(v_toPure_530_);
lean_dec_ref(v_toApplicative_529_);
v___f_531_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_531_, 0, v_toPure_530_);
return v___f_531_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift___redArg(lean_object* v_inst_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_533_, 0, lean_box(0));
lean_closure_set(v___x_533_, 1, lean_box(0));
lean_closure_set(v___x_533_, 2, v_inst_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift(lean_object* v_00_u03b5_534_, lean_object* v_m_535_, lean_object* v_inst_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_537_, 0, lean_box(0));
lean_closure_set(v___x_537_, 1, lean_box(0));
lean_closure_set(v___x_537_, 2, v_inst_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg___lam__0(lean_object* v_handle_538_, lean_object* v_toPure_539_, lean_object* v_res_540_){
_start:
{
if (lean_obj_tag(v_res_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
lean_dec(v_toPure_539_);
v_a_541_ = lean_ctor_get(v_res_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v_res_540_);
v___x_542_ = lean_apply_1(v_handle_538_, v_a_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_dec(v_handle_538_);
v___x_543_ = lean_apply_2(v_toPure_539_, lean_box(0), v_res_540_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg(lean_object* v_inst_544_, lean_object* v_ma_545_, lean_object* v_handle_546_){
_start:
{
lean_object* v_toApplicative_547_; lean_object* v_toBind_548_; lean_object* v_toPure_549_; lean_object* v___f_550_; lean_object* v___x_551_; 
v_toApplicative_547_ = lean_ctor_get(v_inst_544_, 0);
lean_inc_ref(v_toApplicative_547_);
v_toBind_548_ = lean_ctor_get(v_inst_544_, 1);
lean_inc(v_toBind_548_);
lean_dec_ref(v_inst_544_);
v_toPure_549_ = lean_ctor_get(v_toApplicative_547_, 1);
lean_inc(v_toPure_549_);
lean_dec_ref(v_toApplicative_547_);
v___f_550_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_550_, 0, v_handle_546_);
lean_closure_set(v___f_550_, 1, v_toPure_549_);
v___x_551_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v_ma_545_, v___f_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object* v_00_u03b5_552_, lean_object* v_m_553_, lean_object* v_inst_554_, lean_object* v_00_u03b1_555_, lean_object* v_ma_556_, lean_object* v_handle_557_){
_start:
{
lean_object* v_toApplicative_558_; lean_object* v_toBind_559_; lean_object* v_toPure_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v_toApplicative_558_ = lean_ctor_get(v_inst_554_, 0);
lean_inc_ref(v_toApplicative_558_);
v_toBind_559_ = lean_ctor_get(v_inst_554_, 1);
lean_inc(v_toBind_559_);
lean_dec_ref(v_inst_554_);
v_toPure_560_ = lean_ctor_get(v_toApplicative_558_, 1);
lean_inc(v_toPure_560_);
lean_dec_ref(v_toApplicative_558_);
v___f_561_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_561_, 0, v_handle_557_);
lean_closure_set(v___f_561_, 1, v_toPure_560_);
v___x_562_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v_ma_556_, v___f_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___lam__0(lean_object* v_00_u03b1_563_, lean_object* v_f_564_, lean_object* v_x_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_apply_2(v_f_564_, lean_box(0), v_x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor(lean_object* v_00_u03b5_568_, lean_object* v_m_569_){
_start:
{
lean_object* v___f_570_; 
v___f_570_ = ((lean_object*)(l_ExceptT_instMonadFunctor___closed__0));
return v___f_570_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__0(lean_object* v_toPure_571_, lean_object* v___y_572_, lean_object* v_a_573_){
_start:
{
if (lean_obj_tag(v_a_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
lean_dec(v___y_572_);
v_a_574_ = lean_ctor_get(v_a_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v_a_573_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v_a_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_579_);
return v___x_580_;
}
}
}
else
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_a_573_, 0);
lean_dec(v_unused_591_);
v___x_584_ = v_a_573_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_a_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___y_572_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___y_572_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_587_);
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object* v_inst_592_, lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_toApplicative_597_; lean_object* v_toBind_598_; lean_object* v_toPure_599_; lean_object* v___f_600_; lean_object* v___x_601_; 
v_toApplicative_597_ = lean_ctor_get(v_inst_592_, 0);
lean_inc_ref(v_toApplicative_597_);
v_toBind_598_ = lean_ctor_get(v_inst_592_, 1);
lean_inc(v_toBind_598_);
lean_dec_ref(v_inst_592_);
v_toPure_599_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc(v_toPure_599_);
lean_dec_ref(v_toApplicative_597_);
v___f_600_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_600_, 0, v_toPure_599_);
lean_closure_set(v___f_600_, 1, v___y_595_);
v___x_601_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v___y_596_, v___f_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__2(lean_object* v_toPure_602_, lean_object* v_y_603_, lean_object* v_a_604_){
_start:
{
if (lean_obj_tag(v_a_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_y_603_);
v_a_605_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v_a_604_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v_a_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_612_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = lean_apply_2(v_toPure_602_, lean_box(0), v___x_610_);
return v___x_611_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
v_a_614_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v_a_604_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v_a_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_apply_1(v_y_603_, v_a_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_apply_2(v_toPure_602_, lean_box(0), v___x_620_);
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__3(lean_object* v_toApplicative_624_, lean_object* v_x_625_, lean_object* v_toBind_626_, lean_object* v_y_627_){
_start:
{
lean_object* v_toPure_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___f_631_; lean_object* v___x_632_; 
v_toPure_628_ = lean_ctor_get(v_toApplicative_624_, 1);
lean_inc(v_toPure_628_);
lean_dec_ref(v_toApplicative_624_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_apply_1(v_x_625_, v___x_629_);
v___f_631_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_631_, 0, v_toPure_628_);
lean_closure_set(v___f_631_, 1, v_y_627_);
v___x_632_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_630_, v___f_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object* v_inst_633_, lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_f_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_toApplicative_638_; lean_object* v_toBind_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_toApplicative_638_ = lean_ctor_get(v_inst_633_, 0);
v_toBind_639_ = lean_ctor_get(v_inst_633_, 1);
lean_inc(v_toBind_639_);
lean_inc(v_toBind_639_);
lean_inc_ref(v_toApplicative_638_);
v___f_640_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_640_, 0, v_toApplicative_638_);
lean_closure_set(v___f_640_, 1, v_x_637_);
lean_closure_set(v___f_640_, 2, v_toBind_639_);
v___x_641_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_inst_633_);
lean_closure_set(v___x_641_, 3, lean_box(0));
lean_closure_set(v___x_641_, 4, lean_box(0));
lean_closure_set(v___x_641_, 5, v___f_640_);
v___x_642_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v_f_636_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5(lean_object* v_toApplicative_643_, lean_object* v_a_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_toPure_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_toPure_646_ = lean_ctor_get(v_toApplicative_643_, 1);
lean_inc(v_toPure_646_);
lean_dec_ref(v_toApplicative_643_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_a_644_);
v___x_648_ = lean_apply_2(v_toPure_646_, lean_box(0), v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5___boxed(lean_object* v_toApplicative_649_, lean_object* v_a_650_, lean_object* v_x_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_ExceptT_instMonad___redArg___lam__5(v_toApplicative_649_, v_a_650_, v_x_651_);
lean_dec(v_x_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__6(lean_object* v_toApplicative_653_, lean_object* v_y_654_, lean_object* v_inst_655_, lean_object* v_toBind_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___f_658_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_658_, 0, v_toApplicative_653_);
lean_closure_set(v___f_658_, 1, v_a_657_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_apply_1(v_y_654_, v___x_659_);
v___x_661_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_661_, 0, lean_box(0));
lean_closure_set(v___x_661_, 1, lean_box(0));
lean_closure_set(v___x_661_, 2, v_inst_655_);
lean_closure_set(v___x_661_, 3, lean_box(0));
lean_closure_set(v___x_661_, 4, lean_box(0));
lean_closure_set(v___x_661_, 5, v___f_658_);
v___x_662_ = lean_apply_4(v_toBind_656_, lean_box(0), lean_box(0), v___x_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object* v_inst_663_, lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_y_667_){
_start:
{
lean_object* v_toApplicative_668_; lean_object* v_toBind_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_toApplicative_668_ = lean_ctor_get(v_inst_663_, 0);
v_toBind_669_ = lean_ctor_get(v_inst_663_, 1);
lean_inc(v_toBind_669_);
lean_inc(v_toBind_669_);
lean_inc_ref(v_inst_663_);
lean_inc_ref(v_toApplicative_668_);
v___f_670_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__6), 5, 4);
lean_closure_set(v___f_670_, 0, v_toApplicative_668_);
lean_closure_set(v___f_670_, 1, v_y_667_);
lean_closure_set(v___f_670_, 2, v_inst_663_);
lean_closure_set(v___f_670_, 3, v_toBind_669_);
v___x_671_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_671_, 0, lean_box(0));
lean_closure_set(v___x_671_, 1, lean_box(0));
lean_closure_set(v___x_671_, 2, v_inst_663_);
lean_closure_set(v___x_671_, 3, lean_box(0));
lean_closure_set(v___x_671_, 4, lean_box(0));
lean_closure_set(v___x_671_, 5, v___f_670_);
v___x_672_ = lean_apply_4(v_toBind_669_, lean_box(0), lean_box(0), v_x_666_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8(lean_object* v_y_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_box(0);
v___x_676_ = lean_apply_1(v_y_673_, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8___boxed(lean_object* v_y_677_, lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_ExceptT_instMonad___redArg___lam__8(v_y_677_, v_x_678_);
lean_dec(v_x_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object* v_inst_680_, lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_y_684_){
_start:
{
lean_object* v_toBind_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_toBind_685_ = lean_ctor_get(v_inst_680_, 1);
lean_inc(v_toBind_685_);
v___f_686_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_686_, 0, v_y_684_);
v___x_687_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_687_, 0, lean_box(0));
lean_closure_set(v___x_687_, 1, lean_box(0));
lean_closure_set(v___x_687_, 2, v_inst_680_);
lean_closure_set(v___x_687_, 3, lean_box(0));
lean_closure_set(v___x_687_, 4, lean_box(0));
lean_closure_set(v___x_687_, 5, v___f_686_);
v___x_688_ = lean_apply_4(v_toBind_685_, lean_box(0), lean_box(0), v_x_683_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg(lean_object* v_inst_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_inc_ref(v_inst_689_);
v___f_690_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_690_, 0, v_inst_689_);
lean_inc_ref(v_inst_689_);
v___f_691_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_691_, 0, v_inst_689_);
lean_inc_ref(v_inst_689_);
v___f_692_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_692_, 0, v_inst_689_);
lean_inc_ref(v_inst_689_);
v___f_693_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_693_, 0, v_inst_689_);
lean_inc_ref(v_inst_689_);
v___x_694_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_694_, 0, lean_box(0));
lean_closure_set(v___x_694_, 1, lean_box(0));
lean_closure_set(v___x_694_, 2, v_inst_689_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___f_690_);
lean_inc_ref(v_inst_689_);
v___x_696_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_696_, 0, lean_box(0));
lean_closure_set(v___x_696_, 1, lean_box(0));
lean_closure_set(v___x_696_, 2, v_inst_689_);
v___x_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_ctor_set(v___x_697_, 2, v___f_691_);
lean_ctor_set(v___x_697_, 3, v___f_692_);
lean_ctor_set(v___x_697_, 4, v___f_693_);
v___x_698_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_698_, 0, lean_box(0));
lean_closure_set(v___x_698_, 1, lean_box(0));
lean_closure_set(v___x_698_, 2, v_inst_689_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad(lean_object* v_00_u03b5_700_, lean_object* v_m_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc_ref(v_inst_702_);
v___f_703_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_703_, 0, v_inst_702_);
lean_inc_ref(v_inst_702_);
v___f_704_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_704_, 0, v_inst_702_);
lean_inc_ref(v_inst_702_);
v___f_705_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_705_, 0, v_inst_702_);
lean_inc_ref(v_inst_702_);
v___f_706_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_706_, 0, v_inst_702_);
lean_inc_ref(v_inst_702_);
v___x_707_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_707_, 0, lean_box(0));
lean_closure_set(v___x_707_, 1, lean_box(0));
lean_closure_set(v___x_707_, 2, v_inst_702_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___f_703_);
lean_inc_ref(v_inst_702_);
v___x_709_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_709_, 0, lean_box(0));
lean_closure_set(v___x_709_, 1, lean_box(0));
lean_closure_set(v___x_709_, 2, v_inst_702_);
v___x_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
lean_ctor_set(v___x_710_, 2, v___f_704_);
lean_ctor_set(v___x_710_, 3, v___f_705_);
lean_ctor_set(v___x_710_, 4, v___f_706_);
v___x_711_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_711_, 0, lean_box(0));
lean_closure_set(v___x_711_, 1, lean_box(0));
lean_closure_set(v___x_711_, 2, v_inst_702_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt___redArg(lean_object* v_inst_713_, lean_object* v_f_714_, lean_object* v_x_715_){
_start:
{
lean_object* v_toApplicative_716_; lean_object* v_toFunctor_717_; lean_object* v_map_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_toApplicative_716_ = lean_ctor_get(v_inst_713_, 0);
lean_inc_ref(v_toApplicative_716_);
lean_dec_ref(v_inst_713_);
v_toFunctor_717_ = lean_ctor_get(v_toApplicative_716_, 0);
lean_inc_ref(v_toFunctor_717_);
lean_dec_ref(v_toApplicative_716_);
v_map_718_ = lean_ctor_get(v_toFunctor_717_, 0);
lean_inc(v_map_718_);
lean_dec_ref(v_toFunctor_717_);
v___x_719_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_719_, 0, lean_box(0));
lean_closure_set(v___x_719_, 1, lean_box(0));
lean_closure_set(v___x_719_, 2, lean_box(0));
lean_closure_set(v___x_719_, 3, v_f_714_);
v___x_720_ = lean_apply_4(v_map_718_, lean_box(0), lean_box(0), v___x_719_, v_x_715_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object* v_00_u03b5_721_, lean_object* v_m_722_, lean_object* v_inst_723_, lean_object* v_00_u03b5_x27_724_, lean_object* v_00_u03b1_725_, lean_object* v_f_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_toApplicative_728_; lean_object* v_toFunctor_729_; lean_object* v_map_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_toApplicative_728_ = lean_ctor_get(v_inst_723_, 0);
lean_inc_ref(v_toApplicative_728_);
lean_dec_ref(v_inst_723_);
v_toFunctor_729_ = lean_ctor_get(v_toApplicative_728_, 0);
lean_inc_ref(v_toFunctor_729_);
lean_dec_ref(v_toApplicative_728_);
v_map_730_ = lean_ctor_get(v_toFunctor_729_, 0);
lean_inc(v_map_730_);
lean_dec_ref(v_toFunctor_729_);
v___x_731_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_731_, 0, lean_box(0));
lean_closure_set(v___x_731_, 1, lean_box(0));
lean_closure_set(v___x_731_, 2, lean_box(0));
lean_closure_set(v___x_731_, 3, v_f_726_);
v___x_732_ = lean_apply_4(v_map_730_, lean_box(0), lean_box(0), v___x_731_, v_x_727_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__0(lean_object* v_inst_733_, lean_object* v_00_u03b1_734_, lean_object* v_e_735_){
_start:
{
lean_object* v_throw_736_; lean_object* v___x_737_; 
v_throw_736_ = lean_ctor_get(v_inst_733_, 0);
lean_inc(v_throw_736_);
lean_dec_ref(v_inst_733_);
v___x_737_ = lean_apply_2(v_throw_736_, lean_box(0), v_e_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__1(lean_object* v_inst_738_, lean_object* v_00_u03b1_739_, lean_object* v_x_740_, lean_object* v_handle_741_){
_start:
{
lean_object* v_tryCatch_742_; lean_object* v___x_743_; 
v_tryCatch_742_ = lean_ctor_get(v_inst_738_, 1);
lean_inc(v_tryCatch_742_);
lean_dec_ref(v_inst_738_);
v___x_743_ = lean_apply_3(v_tryCatch_742_, lean_box(0), v_x_740_, v_handle_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg(lean_object* v_inst_744_){
_start:
{
lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_747_; 
lean_inc_ref(v_inst_744_);
v___f_745_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_745_, 0, v_inst_744_);
v___f_746_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_746_, 0, v_inst_744_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___f_745_);
lean_ctor_set(v___x_747_, 1, v___f_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object* v_m_748_, lean_object* v_00_u03b5_u2081_749_, lean_object* v_00_u03b5_u2082_750_, lean_object* v_inst_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
lean_inc_ref(v_inst_751_);
v___f_752_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_752_, 0, v_inst_751_);
v___f_753_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_753_, 0, v_inst_751_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___f_752_);
lean_ctor_set(v___x_754_, 1, v___f_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object* v_toPure_755_, lean_object* v_00_u03b1_756_, lean_object* v_e_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_e_757_);
v___x_759_ = lean_apply_2(v_toPure_755_, lean_box(0), v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg(lean_object* v_inst_760_){
_start:
{
lean_object* v_toApplicative_761_; lean_object* v_toPure_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_toApplicative_761_ = lean_ctor_get(v_inst_760_, 0);
v_toPure_762_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_inc(v_toPure_762_);
v___f_763_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_763_, 0, v_toPure_762_);
v___x_764_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_764_, 0, lean_box(0));
lean_closure_set(v___x_764_, 1, lean_box(0));
lean_closure_set(v___x_764_, 2, v_inst_760_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___f_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad(lean_object* v_m_766_, lean_object* v_00_u03b5_767_, lean_object* v_inst_768_){
_start:
{
lean_object* v_toApplicative_769_; lean_object* v_toPure_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_toApplicative_769_ = lean_ctor_get(v_inst_768_, 0);
v_toPure_770_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_770_);
v___f_771_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_771_, 0, v_toPure_770_);
v___x_772_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_772_, 0, lean_box(0));
lean_closure_set(v___x_772_, 1, lean_box(0));
lean_closure_set(v___x_772_, 2, v_inst_768_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___f_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad___redArg(lean_object* v_inst_774_, lean_object* v_inst_775_){
_start:
{
lean_object* v_toApplicative_776_; lean_object* v_toPure_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_toApplicative_776_ = lean_ctor_get(v_inst_774_, 0);
lean_inc_ref(v_toApplicative_776_);
lean_dec_ref(v_inst_774_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_inst_775_);
v___x_779_ = lean_apply_2(v_toPure_777_, lean_box(0), v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad(lean_object* v_m_780_, lean_object* v_00_u03b5_781_, lean_object* v_00_u03b1_782_, lean_object* v_inst_783_, lean_object* v_inst_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_instInhabitedExceptTOfMonad___redArg(v_inst_783_, v_inst_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___lam__0(lean_object* v_00_u03b1_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___y_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object* v_00_u03b5_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l_instMonadExceptOfExcept___closed__2));
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0(uint8_t v_useFirstEx_796_, lean_object* v_throw_797_, lean_object* v_e_u2081_798_, lean_object* v_e_u2082_799_){
_start:
{
if (v_useFirstEx_796_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v_e_u2081_798_);
v___x_800_ = lean_apply_2(v_throw_797_, lean_box(0), v_e_u2082_799_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; 
lean_dec(v_e_u2082_799_);
v___x_801_ = lean_apply_2(v_throw_797_, lean_box(0), v_e_u2081_798_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0___boxed(lean_object* v_useFirstEx_802_, lean_object* v_throw_803_, lean_object* v_e_u2081_804_, lean_object* v_e_u2082_805_){
_start:
{
uint8_t v_useFirstEx_boxed_806_; lean_object* v_res_807_; 
v_useFirstEx_boxed_806_ = lean_unbox(v_useFirstEx_802_);
v_res_807_ = l_MonadExcept_orelse_x27___redArg___lam__0(v_useFirstEx_boxed_806_, v_throw_803_, v_e_u2081_804_, v_e_u2082_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1(uint8_t v_useFirstEx_808_, lean_object* v_throw_809_, lean_object* v_tryCatch_810_, lean_object* v_t_u2082_811_, lean_object* v_e_u2081_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; 
v___x_813_ = lean_box(v_useFirstEx_808_);
v___f_814_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_814_, 0, v___x_813_);
lean_closure_set(v___f_814_, 1, v_throw_809_);
lean_closure_set(v___f_814_, 2, v_e_u2081_812_);
v___x_815_ = lean_apply_3(v_tryCatch_810_, lean_box(0), v_t_u2082_811_, v___f_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1___boxed(lean_object* v_useFirstEx_816_, lean_object* v_throw_817_, lean_object* v_tryCatch_818_, lean_object* v_t_u2082_819_, lean_object* v_e_u2081_820_){
_start:
{
uint8_t v_useFirstEx_boxed_821_; lean_object* v_res_822_; 
v_useFirstEx_boxed_821_ = lean_unbox(v_useFirstEx_816_);
v_res_822_ = l_MonadExcept_orelse_x27___redArg___lam__1(v_useFirstEx_boxed_821_, v_throw_817_, v_tryCatch_818_, v_t_u2082_819_, v_e_u2081_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg(lean_object* v_inst_823_, lean_object* v_t_u2081_824_, lean_object* v_t_u2082_825_, uint8_t v_useFirstEx_826_){
_start:
{
lean_object* v_throw_827_; lean_object* v_tryCatch_828_; lean_object* v___x_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
v_throw_827_ = lean_ctor_get(v_inst_823_, 0);
lean_inc(v_throw_827_);
v_tryCatch_828_ = lean_ctor_get(v_inst_823_, 1);
lean_inc(v_tryCatch_828_);
lean_dec_ref(v_inst_823_);
v___x_829_ = lean_box(v_useFirstEx_826_);
lean_inc(v_tryCatch_828_);
v___f_830_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_830_, 0, v___x_829_);
lean_closure_set(v___f_830_, 1, v_throw_827_);
lean_closure_set(v___f_830_, 2, v_tryCatch_828_);
lean_closure_set(v___f_830_, 3, v_t_u2082_825_);
v___x_831_ = lean_apply_3(v_tryCatch_828_, lean_box(0), v_t_u2081_824_, v___f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___boxed(lean_object* v_inst_832_, lean_object* v_t_u2081_833_, lean_object* v_t_u2082_834_, lean_object* v_useFirstEx_835_){
_start:
{
uint8_t v_useFirstEx_boxed_836_; lean_object* v_res_837_; 
v_useFirstEx_boxed_836_ = lean_unbox(v_useFirstEx_835_);
v_res_837_ = l_MonadExcept_orelse_x27___redArg(v_inst_832_, v_t_u2081_833_, v_t_u2082_834_, v_useFirstEx_boxed_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object* v_00_u03b5_838_, lean_object* v_m_839_, lean_object* v_inst_840_, lean_object* v_00_u03b1_841_, lean_object* v_t_u2081_842_, lean_object* v_t_u2082_843_, uint8_t v_useFirstEx_844_){
_start:
{
lean_object* v_throw_845_; lean_object* v_tryCatch_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___x_849_; 
v_throw_845_ = lean_ctor_get(v_inst_840_, 0);
lean_inc(v_throw_845_);
v_tryCatch_846_ = lean_ctor_get(v_inst_840_, 1);
lean_inc(v_tryCatch_846_);
lean_dec_ref(v_inst_840_);
v___x_847_ = lean_box(v_useFirstEx_844_);
lean_inc(v_tryCatch_846_);
v___f_848_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_848_, 0, v___x_847_);
lean_closure_set(v___f_848_, 1, v_throw_845_);
lean_closure_set(v___f_848_, 2, v_tryCatch_846_);
lean_closure_set(v___f_848_, 3, v_t_u2082_843_);
v___x_849_ = lean_apply_3(v_tryCatch_846_, lean_box(0), v_t_u2081_842_, v___f_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___boxed(lean_object* v_00_u03b5_850_, lean_object* v_m_851_, lean_object* v_inst_852_, lean_object* v_00_u03b1_853_, lean_object* v_t_u2081_854_, lean_object* v_t_u2082_855_, lean_object* v_useFirstEx_856_){
_start:
{
uint8_t v_useFirstEx_boxed_857_; lean_object* v_res_858_; 
v_useFirstEx_boxed_857_ = lean_unbox(v_useFirstEx_856_);
v_res_858_ = l_MonadExcept_orelse_x27(v_00_u03b5_850_, v_m_851_, v_inst_852_, v_00_u03b1_853_, v_t_u2081_854_, v_t_u2082_855_, v_useFirstEx_boxed_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__0(lean_object* v_toPure_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_a_860_);
v___x_862_ = lean_apply_2(v_toPure_859_, lean_box(0), v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__1(lean_object* v_toPure_863_, lean_object* v_ex_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_ex_864_);
v___x_866_ = lean_apply_2(v_toPure_863_, lean_box(0), v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg(lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_toApplicative_870_; lean_object* v_tryCatch_871_; lean_object* v_toBind_872_; lean_object* v_toPure_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_toApplicative_870_ = lean_ctor_get(v_inst_867_, 0);
lean_inc_ref(v_toApplicative_870_);
v_tryCatch_871_ = lean_ctor_get(v_inst_868_, 1);
lean_inc(v_tryCatch_871_);
lean_dec_ref(v_inst_868_);
v_toBind_872_ = lean_ctor_get(v_inst_867_, 1);
lean_inc(v_toBind_872_);
lean_dec_ref(v_inst_867_);
v_toPure_873_ = lean_ctor_get(v_toApplicative_870_, 1);
lean_inc(v_toPure_873_);
lean_dec_ref(v_toApplicative_870_);
lean_inc(v_toPure_873_);
v___f_874_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_874_, 0, v_toPure_873_);
v___f_875_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_875_, 0, v_toPure_873_);
v___x_876_ = lean_apply_4(v_toBind_872_, lean_box(0), lean_box(0), v_x_869_, v___f_874_);
v___x_877_ = lean_apply_3(v_tryCatch_871_, lean_box(0), v___x_876_, v___f_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_observing(lean_object* v_00_u03b5_878_, lean_object* v_00_u03b1_879_, lean_object* v_m_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_toApplicative_884_; lean_object* v_tryCatch_885_; lean_object* v_toBind_886_; lean_object* v_toPure_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_toApplicative_884_ = lean_ctor_get(v_inst_881_, 0);
lean_inc_ref(v_toApplicative_884_);
v_tryCatch_885_ = lean_ctor_get(v_inst_882_, 1);
lean_inc(v_tryCatch_885_);
lean_dec_ref(v_inst_882_);
v_toBind_886_ = lean_ctor_get(v_inst_881_, 1);
lean_inc(v_toBind_886_);
lean_dec_ref(v_inst_881_);
v_toPure_887_ = lean_ctor_get(v_toApplicative_884_, 1);
lean_inc(v_toPure_887_);
lean_dec_ref(v_toApplicative_884_);
lean_inc(v_toPure_887_);
v___f_888_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_888_, 0, v_toPure_887_);
v___f_889_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_889_, 0, v_toPure_887_);
v___x_890_ = lean_apply_4(v_toBind_886_, lean_box(0), lean_box(0), v_x_883_, v___f_888_);
v___x_891_ = lean_apply_3(v_tryCatch_885_, lean_box(0), v___x_890_, v___f_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_throw_896_; lean_object* v___x_897_; 
lean_dec(v_inst_893_);
v_a_895_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v_x_894_);
v_throw_896_ = lean_ctor_get(v_inst_892_, 0);
lean_inc(v_throw_896_);
lean_dec_ref(v_inst_892_);
v___x_897_ = lean_apply_2(v_throw_896_, lean_box(0), v_a_895_);
return v___x_897_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; 
lean_dec_ref(v_inst_892_);
v_a_898_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v_x_894_);
v___x_899_ = lean_apply_2(v_inst_893_, lean_box(0), v_a_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept(lean_object* v_00_u03b5_900_, lean_object* v_m_901_, lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_liftExcept___redArg(v_inst_903_, v_inst_904_, v_x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_907_, lean_object* v_x_908_){
_start:
{
lean_inc(v_x_908_);
return v_x_908_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_instMonadControlExceptTOfMonad___redArg___lam__0(v_00_u03b2_909_, v_x_910_);
lean_dec(v_x_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__2(lean_object* v_inst_912_, lean_object* v___f_913_, lean_object* v___f_914_, lean_object* v_00_u03b1_915_, lean_object* v_f_916_){
_start:
{
lean_object* v_toApplicative_917_; lean_object* v_toFunctor_918_; lean_object* v_map_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_toApplicative_917_ = lean_ctor_get(v_inst_912_, 0);
lean_inc_ref(v_toApplicative_917_);
lean_dec_ref(v_inst_912_);
v_toFunctor_918_ = lean_ctor_get(v_toApplicative_917_, 0);
lean_inc_ref(v_toFunctor_918_);
lean_dec_ref(v_toApplicative_917_);
v_map_919_ = lean_ctor_get(v_toFunctor_918_, 0);
lean_inc(v_map_919_);
lean_dec_ref(v_toFunctor_918_);
v___x_920_ = lean_apply_1(v_f_916_, v___f_913_);
v___x_921_ = lean_apply_4(v_map_919_, lean_box(0), lean_box(0), v___f_914_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_922_, lean_object* v_x_923_){
_start:
{
lean_inc(v_x_923_);
return v_x_923_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_924_, lean_object* v_x_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_instMonadControlExceptTOfMonad___redArg___lam__1(v_00_u03b1_924_, v_x_925_);
lean_dec(v_x_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg(lean_object* v_inst_929_){
_start:
{
lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; 
v___f_930_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__0));
v___f_931_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___f_932_ = lean_alloc_closure((void*)(l_instMonadControlExceptTOfMonad___redArg___lam__2), 5, 3);
lean_closure_set(v___f_932_, 0, v_inst_929_);
lean_closure_set(v___f_932_, 1, v___f_930_);
lean_closure_set(v___f_932_, 2, v___f_931_);
v___f_933_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__1));
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___f_932_);
lean_ctor_set(v___x_934_, 1, v___f_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad(lean_object* v_00_u03b5_935_, lean_object* v_m_936_, lean_object* v_inst_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_instMonadControlExceptTOfMonad___redArg(v_inst_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0(lean_object* v_finalizer_939_, lean_object* v_x_940_){
_start:
{
lean_inc(v_finalizer_939_);
return v_finalizer_939_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0___boxed(lean_object* v_finalizer_941_, lean_object* v_x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_tryFinally___redArg___lam__0(v_finalizer_941_, v_x_942_);
lean_dec(v_x_942_);
lean_dec(v_finalizer_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1(lean_object* v_x_944_){
_start:
{
lean_object* v_fst_945_; 
v_fst_945_ = lean_ctor_get(v_x_944_, 0);
lean_inc(v_fst_945_);
return v_fst_945_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_tryFinally___redArg___lam__1(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg(lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_x_951_, lean_object* v_finalizer_952_){
_start:
{
lean_object* v_map_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v_y_956_; lean_object* v___x_957_; 
v_map_953_ = lean_ctor_get(v_inst_950_, 0);
lean_inc(v_map_953_);
lean_dec_ref(v_inst_950_);
v___f_954_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_954_, 0, v_finalizer_952_);
v___f_955_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_956_ = lean_apply_4(v_inst_949_, lean_box(0), lean_box(0), v_x_951_, v___f_954_);
v___x_957_ = lean_apply_4(v_map_953_, lean_box(0), lean_box(0), v___f_955_, v_y_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_tryFinally(lean_object* v_m_958_, lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_x_963_, lean_object* v_finalizer_964_){
_start:
{
lean_object* v_map_965_; lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v_y_968_; lean_object* v___x_969_; 
v_map_965_ = lean_ctor_get(v_inst_962_, 0);
lean_inc(v_map_965_);
lean_dec_ref(v_inst_962_);
v___f_966_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_966_, 0, v_finalizer_964_);
v___f_967_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_968_ = lean_apply_4(v_inst_961_, lean_box(0), lean_box(0), v_x_963_, v___f_966_);
v___x_969_ = lean_apply_4(v_map_965_, lean_box(0), lean_box(0), v___f_967_, v_y_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Id_finally___lam__0(lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_h_973_){
_start:
{
lean_object* v___x_974_; lean_object* v_b_975_; lean_object* v___x_976_; 
lean_inc(v_x_972_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_x_972_);
v_b_975_ = lean_apply_1(v_h_973_, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_x_972_);
lean_ctor_set(v___x_976_, 1, v_b_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__0(lean_object* v_toPure_979_, lean_object* v_r_980_){
_start:
{
lean_object* v_e_982_; lean_object* v_fst_985_; 
v_fst_985_ = lean_ctor_get(v_r_980_, 0);
lean_inc(v_fst_985_);
if (lean_obj_tag(v_fst_985_) == 0)
{
lean_object* v_snd_986_; 
v_snd_986_ = lean_ctor_get(v_r_980_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v_r_980_);
if (lean_obj_tag(v_snd_986_) == 0)
{
lean_object* v_a_987_; 
lean_dec_ref(v_fst_985_);
v_a_987_ = lean_ctor_get(v_snd_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v_snd_986_);
v_e_982_ = v_a_987_;
goto v___jp_981_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_a_988_ = lean_ctor_get(v_fst_985_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v_fst_985_);
v_isSharedCheck_996_ = !lean_is_exclusive(v_snd_986_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v_snd_986_, 0);
lean_dec(v_unused_997_);
v___x_990_ = v_snd_986_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_dec(v_snd_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 0);
lean_ctor_set(v___x_990_, 0, v_a_988_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_apply_2(v_toPure_979_, lean_box(0), v___x_993_);
return v___x_994_;
}
}
}
}
else
{
lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1016_; 
v_snd_998_ = lean_ctor_get(v_r_980_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_r_980_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v_r_980_, 0);
lean_dec(v_unused_1017_);
v___x_1000_ = v_r_980_;
v_isShared_1001_ = v_isSharedCheck_1016_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_dec(v_r_980_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1016_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
if (lean_obj_tag(v_snd_998_) == 0)
{
lean_object* v_a_1002_; 
lean_del_object(v___x_1000_);
lean_dec_ref(v_fst_985_);
v_a_1002_ = lean_ctor_get(v_snd_998_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v_snd_998_);
v_e_982_ = v_a_1002_;
goto v___jp_981_;
}
else
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1015_; 
v_a_1003_ = lean_ctor_get(v_fst_985_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v_fst_985_);
v_a_1004_ = lean_ctor_get(v_snd_998_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_snd_998_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1006_ = v_snd_998_;
v_isShared_1007_ = v_isSharedCheck_1015_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v_snd_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1015_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v_a_1004_);
lean_ctor_set(v___x_1000_, 0, v_a_1003_);
v___x_1009_ = v___x_1000_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1003_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1009_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_apply_2(v_toPure_979_, lean_box(0), v___x_1011_);
return v___x_1012_;
}
}
}
}
}
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_e_982_);
v___x_984_ = lean_apply_2(v_toPure_979_, lean_box(0), v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__1(lean_object* v_h_1018_, lean_object* v_e_x3f_1019_){
_start:
{
if (lean_obj_tag(v_e_x3f_1019_) == 0)
{
goto v___jp_1020_;
}
else
{
lean_object* v_val_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v_val_1023_ = lean_ctor_get(v_e_x3f_1019_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_e_x3f_1019_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1025_ = v_e_x3f_1019_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_val_1023_);
lean_dec(v_e_x3f_1019_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
if (lean_obj_tag(v_val_1023_) == 0)
{
lean_dec_ref(v_val_1023_);
lean_del_object(v___x_1025_);
goto v___jp_1020_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v_val_1023_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v_val_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_a_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1027_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_apply_1(v_h_1018_, v___x_1029_);
return v___x_1030_;
}
}
}
}
v___jp_1020_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_apply_1(v_h_1018_, v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__2(lean_object* v_inst_1033_, lean_object* v_toBind_1034_, lean_object* v___f_1035_, lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_h_1039_){
_start:
{
lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___f_1040_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1040_, 0, v_h_1039_);
v___x_1041_ = lean_apply_4(v_inst_1033_, lean_box(0), lean_box(0), v_x_1038_, v___f_1040_);
v___x_1042_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1041_, v___f_1035_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_){
_start:
{
lean_object* v_toApplicative_1045_; lean_object* v_toBind_1046_; lean_object* v_toPure_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; 
v_toApplicative_1045_ = lean_ctor_get(v_inst_1044_, 0);
lean_inc_ref(v_toApplicative_1045_);
v_toBind_1046_ = lean_ctor_get(v_inst_1044_, 1);
lean_inc(v_toBind_1046_);
lean_dec_ref(v_inst_1044_);
v_toPure_1047_ = lean_ctor_get(v_toApplicative_1045_, 1);
lean_inc(v_toPure_1047_);
lean_dec_ref(v_toApplicative_1045_);
v___f_1048_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1048_, 0, v_toPure_1047_);
v___f_1049_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1049_, 0, v_inst_1043_);
lean_closure_set(v___f_1049_, 1, v_toBind_1046_);
lean_closure_set(v___f_1049_, 2, v___f_1048_);
return v___f_1049_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object* v_m_1050_, lean_object* v_00_u03b5_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_toApplicative_1054_; lean_object* v_toBind_1055_; lean_object* v_toPure_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; 
v_toApplicative_1054_ = lean_ctor_get(v_inst_1053_, 0);
lean_inc_ref(v_toApplicative_1054_);
v_toBind_1055_ = lean_ctor_get(v_inst_1053_, 1);
lean_inc(v_toBind_1055_);
lean_dec_ref(v_inst_1053_);
v_toPure_1056_ = lean_ctor_get(v_toApplicative_1054_, 1);
lean_inc(v_toPure_1056_);
lean_dec_ref(v_toApplicative_1054_);
v___f_1057_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1057_, 0, v_toPure_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1058_, 0, v_inst_1052_);
lean_closure_set(v___f_1058_, 1, v_toBind_1055_);
lean_closure_set(v___f_1058_, 2, v___f_1057_);
return v___f_1058_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__0(lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v_x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v_x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v_x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v_x_1059_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v_x_1059_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v_x_1059_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__1(lean_object* v_toFunctor_1076_, lean_object* v_inst_1077_, lean_object* v___f_1078_, lean_object* v_00_u03b1_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v_map_1081_; lean_object* v___x_1082_; lean_object* v_this_1083_; 
v_map_1081_ = lean_ctor_get(v_toFunctor_1076_, 0);
lean_inc(v_map_1081_);
lean_dec_ref(v_toFunctor_1076_);
v___x_1082_ = lean_apply_2(v_inst_1077_, lean_box(0), v_x_1080_);
v_this_1083_ = lean_apply_4(v_map_1081_, lean_box(0), lean_box(0), v___f_1078_, v___x_1082_);
return v_this_1083_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg(lean_object* v_inst_1085_, lean_object* v_inst_1086_){
_start:
{
lean_object* v_toApplicative_1087_; lean_object* v_toFunctor_1088_; lean_object* v___f_1089_; lean_object* v___f_1090_; 
v_toApplicative_1087_ = lean_ctor_get(v_inst_1085_, 0);
lean_inc_ref(v_toApplicative_1087_);
lean_dec_ref(v_inst_1085_);
v_toFunctor_1088_ = lean_ctor_get(v_toApplicative_1087_, 0);
lean_inc_ref(v_toFunctor_1088_);
lean_dec_ref(v_toApplicative_1087_);
v___f_1089_ = ((lean_object*)(l_instMonadAttachExceptTOfMonad___redArg___closed__0));
v___f_1090_ = lean_alloc_closure((void*)(l_instMonadAttachExceptTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1090_, 0, v_toFunctor_1088_);
lean_closure_set(v___f_1090_, 1, v_inst_1086_);
lean_closure_set(v___f_1090_, 2, v___f_1089_);
return v___f_1090_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad(lean_object* v_m_1091_, lean_object* v_00_u03b5_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_instMonadAttachExceptTOfMonad___redArg(v_inst_1093_, v_inst_1094_);
return v___x_1095_;
}
}
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Except(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Id(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Except(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Except(builtin);
}
#ifdef __cplusplus
}
#endif
