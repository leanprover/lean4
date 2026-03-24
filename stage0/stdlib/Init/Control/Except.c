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
lean_object* v___x_61_; 
v___x_61_ = l___private_Init_Control_Except_0__Except_map_match__1_splitter___redArg(v_x_58_, v_h__1_59_, v_h__2_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Except_mapError___redArg(lean_object* v_f_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_72_; 
v_a_64_ = lean_ctor_get(v_x_63_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_72_ == 0)
{
v___x_66_ = v_x_63_;
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v_x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_apply_1(v_f_62_, v_a_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_68_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_f_62_);
v_a_73_ = lean_ctor_get(v_x_63_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v_x_63_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v_x_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_mapError(lean_object* v_00_u03b5_81_, lean_object* v_00_u03b5_x27_82_, lean_object* v_00_u03b1_83_, lean_object* v_f_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_a_86_ = lean_ctor_get(v_x_85_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v_x_85_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v_x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_apply_1(v_f_84_, v_a_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v_f_84_);
v_a_95_ = lean_ctor_get(v_x_85_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v_x_85_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v_x_85_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_bind___redArg(lean_object* v_ma_103_, lean_object* v_f_104_){
_start:
{
if (lean_obj_tag(v_ma_103_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_f_104_);
v_a_105_ = lean_ctor_get(v_ma_103_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_ma_103_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v_ma_103_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v_ma_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_114_; 
v_a_113_ = lean_ctor_get(v_ma_103_, 0);
lean_inc(v_a_113_);
lean_dec_ref(v_ma_103_);
v___x_114_ = lean_apply_1(v_f_104_, v_a_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Except_bind(lean_object* v_00_u03b5_115_, lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_ma_118_, lean_object* v_f_119_){
_start:
{
if (lean_obj_tag(v_ma_118_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_f_119_);
v_a_120_ = lean_ctor_get(v_ma_118_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_ma_118_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v_ma_118_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v_ma_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v_ma_118_, 0);
lean_inc(v_a_128_);
lean_dec_ref(v_ma_118_);
v___x_129_ = lean_apply_1(v_f_119_, v_a_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT uint8_t l_Except_toBool___redArg(lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toBool___redArg___boxed(lean_object* v_x_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Except_toBool___redArg(v_x_133_);
lean_dec_ref(v_x_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Except_toBool(lean_object* v_00_u03b5_136_, lean_object* v_00_u03b1_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toBool___boxed(lean_object* v_00_u03b5_141_, lean_object* v_00_u03b1_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Except_toBool(v_00_u03b5_141_, v_00_u03b1_142_, v_x_143_);
lean_dec_ref(v_x_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_Except_isOk___redArg(lean_object* v_a_146_){
_start:
{
if (lean_obj_tag(v_a_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Except_isOk___redArg___boxed(lean_object* v_a_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Except_isOk___redArg(v_a_149_);
lean_dec_ref(v_a_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Except_isOk(lean_object* v_00_u03b5_152_, lean_object* v_00_u03b1_153_, lean_object* v_a_154_){
_start:
{
if (lean_obj_tag(v_a_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 1;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Except_isOk___boxed(lean_object* v_00_u03b5_157_, lean_object* v_00_u03b1_158_, lean_object* v_a_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Except_isOk(v_00_u03b5_157_, v_00_u03b1_158_, v_a_159_);
lean_dec_ref(v_a_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Except_toOption___redArg(lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v_x_162_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v_x_162_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v_x_162_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v_x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toOption(lean_object* v_00_u03b5_172_, lean_object* v_00_u03b1_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v_x_174_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v_x_174_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v_x_174_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v_x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
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
LEAN_EXPORT lean_object* l_Except_tryCatch___redArg(lean_object* v_ma_184_, lean_object* v_handle_185_){
_start:
{
if (lean_obj_tag(v_ma_184_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v_ma_184_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v_ma_184_);
v___x_187_ = lean_apply_1(v_handle_185_, v_a_186_);
return v___x_187_;
}
else
{
lean_dec_ref(v_handle_185_);
return v_ma_184_;
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object* v_00_u03b5_188_, lean_object* v_00_u03b1_189_, lean_object* v_ma_190_, lean_object* v_handle_191_){
_start:
{
if (lean_obj_tag(v_ma_190_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; 
v_a_192_ = lean_ctor_get(v_ma_190_, 0);
lean_inc(v_a_192_);
lean_dec_ref(v_ma_190_);
v___x_193_ = lean_apply_1(v_handle_191_, v_a_192_);
return v___x_193_;
}
else
{
lean_dec_ref(v_handle_191_);
return v_ma_190_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg(lean_object* v_x_194_, lean_object* v_y_195_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_box(0);
v___x_197_ = lean_apply_1(v_y_195_, v___x_196_);
return v___x_197_;
}
else
{
lean_dec_ref(v_y_195_);
lean_inc_ref(v_x_194_);
return v_x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg___boxed(lean_object* v_x_198_, lean_object* v_y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Except_orElseLazy___redArg(v_x_198_, v_y_199_);
lean_dec_ref(v_x_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object* v_00_u03b5_201_, lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v_y_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Except_orElseLazy___redArg(v_x_203_, v_y_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___boxed(lean_object* v_00_u03b5_206_, lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Except_orElseLazy(v_00_u03b5_206_, v_00_u03b1_207_, v_x_208_, v_y_209_);
lean_dec_ref(v_x_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__0(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
if (lean_obj_tag(v___y_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v___y_213_);
v_a_215_ = lean_ctor_get(v___y_214_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___y_214_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___y_214_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___y_214_);
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
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v___y_214_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___y_214_, 0);
lean_dec(v_unused_230_);
v___x_224_ = v___y_214_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_dec(v___y_214_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___y_213_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___y_213_);
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
LEAN_EXPORT lean_object* l_Except_instMonad___lam__1(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_f_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_f_233_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_x_234_);
v_a_235_ = lean_ctor_get(v_f_233_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_f_233_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v_f_233_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v_f_233_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_243_ = lean_ctor_get(v_f_233_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v_f_233_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_x_234_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_243_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_a_254_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v___x_245_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_245_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_apply_1(v_a_243_, v_a_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_x_265_, lean_object* v_y_266_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_dec_ref(v_y_266_);
lean_inc_ref(v_x_265_);
return v_x_265_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_apply_1(v_y_266_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_dec_ref(v___x_268_);
lean_inc_ref(v_x_265_);
return v_x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__2___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_x_279_, lean_object* v_y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Except_instMonad___lam__2(v_00_u03b1_277_, v_00_u03b2_278_, v_x_279_, v_y_280_);
lean_dec_ref(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___lam__3(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_x_284_, lean_object* v_y_285_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_y_285_);
v_a_286_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_x_284_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_apply_1(v_y_285_, v___x_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad(lean_object* v_00_u03b5_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = ((lean_object*)(l_Except_instMonad___closed__9));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg(lean_object* v_x_317_){
_start:
{
lean_inc(v_x_317_);
return v_x_317_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg___boxed(lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_ExceptT_mk___redArg(v_x_318_);
lean_dec(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object* v_00_u03b5_320_, lean_object* v_m_321_, lean_object* v_00_u03b1_322_, lean_object* v_x_323_){
_start:
{
lean_inc(v_x_323_);
return v_x_323_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___boxed(lean_object* v_00_u03b5_324_, lean_object* v_m_325_, lean_object* v_00_u03b1_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_ExceptT_mk(v_00_u03b5_324_, v_m_325_, v_00_u03b1_326_, v_x_327_);
lean_dec(v_x_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg(lean_object* v_x_329_){
_start:
{
lean_inc(v_x_329_);
return v_x_329_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg___boxed(lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_ExceptT_run___redArg(v_x_330_);
lean_dec(v_x_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object* v_00_u03b5_332_, lean_object* v_m_333_, lean_object* v_00_u03b1_334_, lean_object* v_x_335_){
_start:
{
lean_inc(v_x_335_);
return v_x_335_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___boxed(lean_object* v_00_u03b5_336_, lean_object* v_m_337_, lean_object* v_00_u03b1_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_ExceptT_run(v_00_u03b5_336_, v_m_337_, v_00_u03b1_338_, v_x_339_);
lean_dec(v_x_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg___lam__0(lean_object* v_error_341_, lean_object* v_ok_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; 
lean_dec(v_ok_342_);
v_a_344_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref(v_x_343_);
v___x_345_ = lean_apply_1(v_error_341_, v_a_344_);
return v___x_345_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_347_; 
lean_dec(v_error_341_);
v_a_346_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v_x_343_);
v___x_347_ = lean_apply_1(v_ok_342_, v_a_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg(lean_object* v_inst_348_, lean_object* v_x_349_, lean_object* v_ok_350_, lean_object* v_error_351_){
_start:
{
lean_object* v_toBind_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v_toBind_352_ = lean_ctor_get(v_inst_348_, 1);
lean_inc(v_toBind_352_);
lean_dec_ref(v_inst_348_);
v___f_353_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_353_, 0, v_error_351_);
lean_closure_set(v___f_353_, 1, v_ok_350_);
v___x_354_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v_x_349_, v___f_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK(lean_object* v_m_355_, lean_object* v_00_u03b5_356_, lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_inst_359_, lean_object* v_x_360_, lean_object* v_ok_361_, lean_object* v_error_362_){
_start:
{
lean_object* v_toBind_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_toBind_363_ = lean_ctor_get(v_inst_359_, 1);
lean_inc(v_toBind_363_);
lean_dec_ref(v_inst_359_);
v___f_364_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_364_, 0, v_error_362_);
lean_closure_set(v___f_364_, 1, v_ok_361_);
v___x_365_ = lean_apply_4(v_toBind_363_, lean_box(0), lean_box(0), v_x_360_, v___f_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg___lam__0(lean_object* v_toPure_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v_x_367_);
v___x_369_ = lean_apply_2(v_toPure_366_, lean_box(0), v_a_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg(lean_object* v_inst_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_toApplicative_372_; lean_object* v_toBind_373_; lean_object* v_toPure_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_toApplicative_372_ = lean_ctor_get(v_inst_370_, 0);
lean_inc_ref(v_toApplicative_372_);
v_toBind_373_ = lean_ctor_get(v_inst_370_, 1);
lean_inc(v_toBind_373_);
lean_dec_ref(v_inst_370_);
v_toPure_374_ = lean_ctor_get(v_toApplicative_372_, 1);
lean_inc(v_toPure_374_);
lean_dec_ref(v_toApplicative_372_);
v___f_375_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_375_, 0, v_toPure_374_);
v___x_376_ = lean_apply_4(v_toBind_373_, lean_box(0), lean_box(0), v_x_371_, v___f_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch(lean_object* v_m_377_, lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_x_380_){
_start:
{
lean_object* v_toApplicative_381_; lean_object* v_toBind_382_; lean_object* v_toPure_383_; lean_object* v___f_384_; lean_object* v___x_385_; 
v_toApplicative_381_ = lean_ctor_get(v_inst_379_, 0);
lean_inc_ref(v_toApplicative_381_);
v_toBind_382_ = lean_ctor_get(v_inst_379_, 1);
lean_inc(v_toBind_382_);
lean_dec_ref(v_inst_379_);
v_toPure_383_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_inc(v_toPure_383_);
lean_dec_ref(v_toApplicative_381_);
v___f_384_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_384_, 0, v_toPure_383_);
v___x_385_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v_x_380_, v___f_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure___redArg(lean_object* v_inst_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_toApplicative_388_; lean_object* v_toPure_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_toApplicative_388_ = lean_ctor_get(v_inst_386_, 0);
lean_inc_ref(v_toApplicative_388_);
lean_dec_ref(v_inst_386_);
v_toPure_389_ = lean_ctor_get(v_toApplicative_388_, 1);
lean_inc(v_toPure_389_);
lean_dec_ref(v_toApplicative_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_a_387_);
v___x_391_ = lean_apply_2(v_toPure_389_, lean_box(0), v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object* v_00_u03b5_392_, lean_object* v_m_393_, lean_object* v_inst_394_, lean_object* v_00_u03b1_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_toApplicative_397_; lean_object* v_toPure_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_toApplicative_397_ = lean_ctor_get(v_inst_394_, 0);
lean_inc_ref(v_toApplicative_397_);
lean_dec_ref(v_inst_394_);
v_toPure_398_ = lean_ctor_get(v_toApplicative_397_, 1);
lean_inc(v_toPure_398_);
lean_dec_ref(v_toApplicative_397_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_a_396_);
v___x_400_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___redArg(lean_object* v_inst_401_, lean_object* v_f_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_toApplicative_404_; 
v_toApplicative_404_ = lean_ctor_get(v_inst_401_, 0);
lean_inc_ref(v_toApplicative_404_);
lean_dec_ref(v_inst_401_);
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v_toPure_405_; lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_f_402_);
v_toPure_405_ = lean_ctor_get(v_toApplicative_404_, 1);
lean_inc(v_toPure_405_);
lean_dec_ref(v_toApplicative_404_);
v_a_406_ = lean_ctor_get(v_x_403_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_414_ == 0)
{
v___x_408_ = v_x_403_;
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v_x_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; 
v___x_412_ = lean_apply_2(v_toPure_405_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_416_; 
lean_dec_ref(v_toApplicative_404_);
v_a_415_ = lean_ctor_get(v_x_403_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v_x_403_);
v___x_416_ = lean_apply_1(v_f_402_, v_a_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object* v_00_u03b5_417_, lean_object* v_m_418_, lean_object* v_inst_419_, lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_f_422_, lean_object* v_x_423_){
_start:
{
lean_object* v_toApplicative_424_; 
v_toApplicative_424_ = lean_ctor_get(v_inst_419_, 0);
lean_inc_ref(v_toApplicative_424_);
lean_dec_ref(v_inst_419_);
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_toPure_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_f_422_);
v_toPure_425_ = lean_ctor_get(v_toApplicative_424_, 1);
lean_inc(v_toPure_425_);
lean_dec_ref(v_toApplicative_424_);
v_a_426_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v_x_423_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v_x_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_apply_2(v_toPure_425_, lean_box(0), v___x_431_);
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; 
lean_dec_ref(v_toApplicative_424_);
v_a_435_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v_x_423_);
v___x_436_ = lean_apply_1(v_f_422_, v_a_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind___redArg(lean_object* v_inst_437_, lean_object* v_ma_438_, lean_object* v_f_439_){
_start:
{
lean_object* v_toBind_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_toBind_440_ = lean_ctor_get(v_inst_437_, 1);
lean_inc(v_toBind_440_);
v___x_441_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_441_, 0, lean_box(0));
lean_closure_set(v___x_441_, 1, lean_box(0));
lean_closure_set(v___x_441_, 2, v_inst_437_);
lean_closure_set(v___x_441_, 3, lean_box(0));
lean_closure_set(v___x_441_, 4, lean_box(0));
lean_closure_set(v___x_441_, 5, v_f_439_);
v___x_442_ = lean_apply_4(v_toBind_440_, lean_box(0), lean_box(0), v_ma_438_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object* v_00_u03b5_443_, lean_object* v_m_444_, lean_object* v_inst_445_, lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_ma_448_, lean_object* v_f_449_){
_start:
{
lean_object* v_toBind_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_toBind_450_ = lean_ctor_get(v_inst_445_, 1);
lean_inc(v_toBind_450_);
v___x_451_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_451_, 0, lean_box(0));
lean_closure_set(v___x_451_, 1, lean_box(0));
lean_closure_set(v___x_451_, 2, v_inst_445_);
lean_closure_set(v___x_451_, 3, lean_box(0));
lean_closure_set(v___x_451_, 4, lean_box(0));
lean_closure_set(v___x_451_, 5, v_f_449_);
v___x_452_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v_ma_448_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg___lam__0(lean_object* v_toPure_453_, lean_object* v_f_454_, lean_object* v_a_455_){
_start:
{
if (lean_obj_tag(v_a_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_f_454_);
v_a_456_ = lean_ctor_get(v_a_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_a_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v_a_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
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
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_apply_2(v_toPure_453_, lean_box(0), v___x_461_);
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_a_465_ = lean_ctor_get(v_a_455_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_455_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v_a_455_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v_a_455_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_apply_1(v_f_454_, v_a_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_2(v_toPure_453_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg(lean_object* v_inst_475_, lean_object* v_f_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_toApplicative_478_; lean_object* v_toBind_479_; lean_object* v_toPure_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v_toApplicative_478_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toApplicative_478_);
v_toBind_479_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toBind_479_);
lean_dec_ref(v_inst_475_);
v_toPure_480_ = lean_ctor_get(v_toApplicative_478_, 1);
lean_inc(v_toPure_480_);
lean_dec_ref(v_toApplicative_478_);
v___f_481_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_481_, 0, v_toPure_480_);
lean_closure_set(v___f_481_, 1, v_f_476_);
v___x_482_ = lean_apply_4(v_toBind_479_, lean_box(0), lean_box(0), v_x_477_, v___f_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object* v_00_u03b5_483_, lean_object* v_m_484_, lean_object* v_inst_485_, lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_f_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_toApplicative_490_; lean_object* v_toBind_491_; lean_object* v_toPure_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_toApplicative_490_ = lean_ctor_get(v_inst_485_, 0);
lean_inc_ref(v_toApplicative_490_);
v_toBind_491_ = lean_ctor_get(v_inst_485_, 1);
lean_inc(v_toBind_491_);
lean_dec_ref(v_inst_485_);
v_toPure_492_ = lean_ctor_get(v_toApplicative_490_, 1);
lean_inc(v_toPure_492_);
lean_dec_ref(v_toApplicative_490_);
v___f_493_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_493_, 0, v_toPure_492_);
lean_closure_set(v___f_493_, 1, v_f_488_);
v___x_494_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v_x_489_, v___f_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg___lam__0(lean_object* v_a_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_a_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg(lean_object* v_inst_498_, lean_object* v_t_499_){
_start:
{
lean_object* v_toApplicative_500_; lean_object* v_toFunctor_501_; lean_object* v_map_502_; lean_object* v___f_503_; lean_object* v___x_504_; 
v_toApplicative_500_ = lean_ctor_get(v_inst_498_, 0);
lean_inc_ref(v_toApplicative_500_);
lean_dec_ref(v_inst_498_);
v_toFunctor_501_ = lean_ctor_get(v_toApplicative_500_, 0);
lean_inc_ref(v_toFunctor_501_);
lean_dec_ref(v_toApplicative_500_);
v_map_502_ = lean_ctor_get(v_toFunctor_501_, 0);
lean_inc(v_map_502_);
lean_dec_ref(v_toFunctor_501_);
v___f_503_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_504_ = lean_apply_4(v_map_502_, lean_box(0), lean_box(0), v___f_503_, v_t_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object* v_00_u03b5_505_, lean_object* v_m_506_, lean_object* v_inst_507_, lean_object* v_00_u03b1_508_, lean_object* v_t_509_){
_start:
{
lean_object* v_toApplicative_510_; lean_object* v_toFunctor_511_; lean_object* v_map_512_; lean_object* v___f_513_; lean_object* v___x_514_; 
v_toApplicative_510_ = lean_ctor_get(v_inst_507_, 0);
lean_inc_ref(v_toApplicative_510_);
lean_dec_ref(v_inst_507_);
v_toFunctor_511_ = lean_ctor_get(v_toApplicative_510_, 0);
lean_inc_ref(v_toFunctor_511_);
lean_dec_ref(v_toApplicative_510_);
v_map_512_ = lean_ctor_get(v_toFunctor_511_, 0);
lean_inc(v_map_512_);
lean_dec_ref(v_toFunctor_511_);
v___f_513_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_514_ = lean_apply_4(v_map_512_, lean_box(0), lean_box(0), v___f_513_, v_t_509_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg___lam__0(lean_object* v_toPure_515_, lean_object* v_00_u03b1_516_, lean_object* v_e_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_apply_2(v_toPure_515_, lean_box(0), v_e_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg(lean_object* v_inst_519_){
_start:
{
lean_object* v_toApplicative_520_; lean_object* v_toPure_521_; lean_object* v___f_522_; 
v_toApplicative_520_ = lean_ctor_get(v_inst_519_, 0);
lean_inc_ref(v_toApplicative_520_);
lean_dec_ref(v_inst_519_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_520_, 1);
lean_inc(v_toPure_521_);
lean_dec_ref(v_toApplicative_520_);
v___f_522_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_522_, 0, v_toPure_521_);
return v___f_522_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept(lean_object* v_00_u03b5_523_, lean_object* v_m_524_, lean_object* v_inst_525_){
_start:
{
lean_object* v_toApplicative_526_; lean_object* v_toPure_527_; lean_object* v___f_528_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_525_, 0);
lean_inc_ref(v_toApplicative_526_);
lean_dec_ref(v_inst_525_);
v_toPure_527_ = lean_ctor_get(v_toApplicative_526_, 1);
lean_inc(v_toPure_527_);
lean_dec_ref(v_toApplicative_526_);
v___f_528_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_528_, 0, v_toPure_527_);
return v___f_528_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift___redArg(lean_object* v_inst_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_530_, 0, lean_box(0));
lean_closure_set(v___x_530_, 1, lean_box(0));
lean_closure_set(v___x_530_, 2, v_inst_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift(lean_object* v_00_u03b5_531_, lean_object* v_m_532_, lean_object* v_inst_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_534_, 0, lean_box(0));
lean_closure_set(v___x_534_, 1, lean_box(0));
lean_closure_set(v___x_534_, 2, v_inst_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg___lam__0(lean_object* v_handle_535_, lean_object* v_toPure_536_, lean_object* v_res_537_){
_start:
{
if (lean_obj_tag(v_res_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
lean_dec(v_toPure_536_);
v_a_538_ = lean_ctor_get(v_res_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v_res_537_);
v___x_539_ = lean_apply_1(v_handle_535_, v_a_538_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
lean_dec(v_handle_535_);
v___x_540_ = lean_apply_2(v_toPure_536_, lean_box(0), v_res_537_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg(lean_object* v_inst_541_, lean_object* v_ma_542_, lean_object* v_handle_543_){
_start:
{
lean_object* v_toApplicative_544_; lean_object* v_toBind_545_; lean_object* v_toPure_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v_toApplicative_544_ = lean_ctor_get(v_inst_541_, 0);
lean_inc_ref(v_toApplicative_544_);
v_toBind_545_ = lean_ctor_get(v_inst_541_, 1);
lean_inc(v_toBind_545_);
lean_dec_ref(v_inst_541_);
v_toPure_546_ = lean_ctor_get(v_toApplicative_544_, 1);
lean_inc(v_toPure_546_);
lean_dec_ref(v_toApplicative_544_);
v___f_547_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_547_, 0, v_handle_543_);
lean_closure_set(v___f_547_, 1, v_toPure_546_);
v___x_548_ = lean_apply_4(v_toBind_545_, lean_box(0), lean_box(0), v_ma_542_, v___f_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object* v_00_u03b5_549_, lean_object* v_m_550_, lean_object* v_inst_551_, lean_object* v_00_u03b1_552_, lean_object* v_ma_553_, lean_object* v_handle_554_){
_start:
{
lean_object* v_toApplicative_555_; lean_object* v_toBind_556_; lean_object* v_toPure_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v_toApplicative_555_ = lean_ctor_get(v_inst_551_, 0);
lean_inc_ref(v_toApplicative_555_);
v_toBind_556_ = lean_ctor_get(v_inst_551_, 1);
lean_inc(v_toBind_556_);
lean_dec_ref(v_inst_551_);
v_toPure_557_ = lean_ctor_get(v_toApplicative_555_, 1);
lean_inc(v_toPure_557_);
lean_dec_ref(v_toApplicative_555_);
v___f_558_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_558_, 0, v_handle_554_);
lean_closure_set(v___f_558_, 1, v_toPure_557_);
v___x_559_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v_ma_553_, v___f_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___lam__0(lean_object* v_00_u03b1_560_, lean_object* v_f_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_2(v_f_561_, lean_box(0), v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor(lean_object* v_00_u03b5_565_, lean_object* v_m_566_){
_start:
{
lean_object* v___f_567_; 
v___f_567_ = ((lean_object*)(l_ExceptT_instMonadFunctor___closed__0));
return v___f_567_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__0(lean_object* v_toPure_568_, lean_object* v___y_569_, lean_object* v_a_570_){
_start:
{
if (lean_obj_tag(v_a_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
lean_dec(v___y_569_);
v_a_571_ = lean_ctor_get(v_a_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_a_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v_a_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
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
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_a_570_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_a_570_, 0);
lean_dec(v_unused_588_);
v___x_581_ = v_a_570_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_a_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___y_569_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___y_569_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_584_);
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object* v_inst_589_, lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_toApplicative_594_; lean_object* v_toBind_595_; lean_object* v_toPure_596_; lean_object* v___f_597_; lean_object* v___x_598_; 
v_toApplicative_594_ = lean_ctor_get(v_inst_589_, 0);
lean_inc_ref(v_toApplicative_594_);
v_toBind_595_ = lean_ctor_get(v_inst_589_, 1);
lean_inc(v_toBind_595_);
lean_dec_ref(v_inst_589_);
v_toPure_596_ = lean_ctor_get(v_toApplicative_594_, 1);
lean_inc(v_toPure_596_);
lean_dec_ref(v_toApplicative_594_);
v___f_597_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_597_, 0, v_toPure_596_);
lean_closure_set(v___f_597_, 1, v___y_592_);
v___x_598_ = lean_apply_4(v_toBind_595_, lean_box(0), lean_box(0), v___y_593_, v___f_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__2(lean_object* v_toPure_599_, lean_object* v_y_600_, lean_object* v_a_601_){
_start:
{
if (lean_obj_tag(v_a_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_y_600_);
v_a_602_ = lean_ctor_get(v_a_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_a_601_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v_a_601_);
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
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_apply_2(v_toPure_599_, lean_box(0), v___x_607_);
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_a_611_ = lean_ctor_get(v_a_601_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v_a_601_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v_a_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_apply_1(v_y_600_, v_a_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = lean_apply_2(v_toPure_599_, lean_box(0), v___x_617_);
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__3(lean_object* v_toApplicative_621_, lean_object* v_x_622_, lean_object* v_toBind_623_, lean_object* v_y_624_){
_start:
{
lean_object* v_toPure_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___x_629_; 
v_toPure_625_ = lean_ctor_get(v_toApplicative_621_, 1);
lean_inc(v_toPure_625_);
lean_dec_ref(v_toApplicative_621_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_apply_1(v_x_622_, v___x_626_);
v___f_628_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_628_, 0, v_toPure_625_);
lean_closure_set(v___f_628_, 1, v_y_624_);
v___x_629_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_627_, v___f_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object* v_inst_630_, lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_f_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_toApplicative_635_; lean_object* v_toBind_636_; lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_toApplicative_635_ = lean_ctor_get(v_inst_630_, 0);
v_toBind_636_ = lean_ctor_get(v_inst_630_, 1);
lean_inc(v_toBind_636_);
lean_inc(v_toBind_636_);
lean_inc_ref(v_toApplicative_635_);
v___f_637_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_637_, 0, v_toApplicative_635_);
lean_closure_set(v___f_637_, 1, v_x_634_);
lean_closure_set(v___f_637_, 2, v_toBind_636_);
v___x_638_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_638_, 0, lean_box(0));
lean_closure_set(v___x_638_, 1, lean_box(0));
lean_closure_set(v___x_638_, 2, v_inst_630_);
lean_closure_set(v___x_638_, 3, lean_box(0));
lean_closure_set(v___x_638_, 4, lean_box(0));
lean_closure_set(v___x_638_, 5, v___f_637_);
v___x_639_ = lean_apply_4(v_toBind_636_, lean_box(0), lean_box(0), v_f_633_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5(lean_object* v_toApplicative_640_, lean_object* v_a_641_, lean_object* v_x_642_){
_start:
{
lean_object* v_toPure_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_toPure_643_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_643_);
lean_dec_ref(v_toApplicative_640_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_a_641_);
v___x_645_ = lean_apply_2(v_toPure_643_, lean_box(0), v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5___boxed(lean_object* v_toApplicative_646_, lean_object* v_a_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_ExceptT_instMonad___redArg___lam__5(v_toApplicative_646_, v_a_647_, v_x_648_);
lean_dec(v_x_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__6(lean_object* v_toApplicative_650_, lean_object* v_y_651_, lean_object* v_inst_652_, lean_object* v_toBind_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___f_655_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_655_, 0, v_toApplicative_650_);
lean_closure_set(v___f_655_, 1, v_a_654_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_apply_1(v_y_651_, v___x_656_);
v___x_658_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_658_, 0, lean_box(0));
lean_closure_set(v___x_658_, 1, lean_box(0));
lean_closure_set(v___x_658_, 2, v_inst_652_);
lean_closure_set(v___x_658_, 3, lean_box(0));
lean_closure_set(v___x_658_, 4, lean_box(0));
lean_closure_set(v___x_658_, 5, v___f_655_);
v___x_659_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object* v_inst_660_, lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_y_664_){
_start:
{
lean_object* v_toApplicative_665_; lean_object* v_toBind_666_; lean_object* v___f_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_toApplicative_665_ = lean_ctor_get(v_inst_660_, 0);
v_toBind_666_ = lean_ctor_get(v_inst_660_, 1);
lean_inc(v_toBind_666_);
lean_inc(v_toBind_666_);
lean_inc_ref(v_inst_660_);
lean_inc_ref(v_toApplicative_665_);
v___f_667_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__6), 5, 4);
lean_closure_set(v___f_667_, 0, v_toApplicative_665_);
lean_closure_set(v___f_667_, 1, v_y_664_);
lean_closure_set(v___f_667_, 2, v_inst_660_);
lean_closure_set(v___f_667_, 3, v_toBind_666_);
v___x_668_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_668_, 0, lean_box(0));
lean_closure_set(v___x_668_, 1, lean_box(0));
lean_closure_set(v___x_668_, 2, v_inst_660_);
lean_closure_set(v___x_668_, 3, lean_box(0));
lean_closure_set(v___x_668_, 4, lean_box(0));
lean_closure_set(v___x_668_, 5, v___f_667_);
v___x_669_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v_x_663_, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8(lean_object* v_y_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = lean_apply_1(v_y_670_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8___boxed(lean_object* v_y_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_ExceptT_instMonad___redArg___lam__8(v_y_674_, v_x_675_);
lean_dec(v_x_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object* v_inst_677_, lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_y_681_){
_start:
{
lean_object* v_toBind_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_toBind_682_ = lean_ctor_get(v_inst_677_, 1);
lean_inc(v_toBind_682_);
v___f_683_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_683_, 0, v_y_681_);
v___x_684_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_684_, 0, lean_box(0));
lean_closure_set(v___x_684_, 1, lean_box(0));
lean_closure_set(v___x_684_, 2, v_inst_677_);
lean_closure_set(v___x_684_, 3, lean_box(0));
lean_closure_set(v___x_684_, 4, lean_box(0));
lean_closure_set(v___x_684_, 5, v___f_683_);
v___x_685_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v_x_680_, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg(lean_object* v_inst_686_){
_start:
{
lean_object* v___f_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_inc_ref(v_inst_686_);
v___f_687_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_687_, 0, v_inst_686_);
lean_inc_ref(v_inst_686_);
v___f_688_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_688_, 0, v_inst_686_);
lean_inc_ref(v_inst_686_);
v___f_689_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_689_, 0, v_inst_686_);
lean_inc_ref(v_inst_686_);
v___f_690_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_690_, 0, v_inst_686_);
lean_inc_ref(v_inst_686_);
v___x_691_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_691_, 0, lean_box(0));
lean_closure_set(v___x_691_, 1, lean_box(0));
lean_closure_set(v___x_691_, 2, v_inst_686_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___f_687_);
lean_inc_ref(v_inst_686_);
v___x_693_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_693_, 0, lean_box(0));
lean_closure_set(v___x_693_, 1, lean_box(0));
lean_closure_set(v___x_693_, 2, v_inst_686_);
v___x_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
lean_ctor_set(v___x_694_, 2, v___f_688_);
lean_ctor_set(v___x_694_, 3, v___f_689_);
lean_ctor_set(v___x_694_, 4, v___f_690_);
v___x_695_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_695_, 0, lean_box(0));
lean_closure_set(v___x_695_, 1, lean_box(0));
lean_closure_set(v___x_695_, 2, v_inst_686_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad(lean_object* v_00_u03b5_697_, lean_object* v_m_698_, lean_object* v_inst_699_){
_start:
{
lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc_ref(v_inst_699_);
v___f_700_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_700_, 0, v_inst_699_);
lean_inc_ref(v_inst_699_);
v___f_701_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_701_, 0, v_inst_699_);
lean_inc_ref(v_inst_699_);
v___f_702_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_702_, 0, v_inst_699_);
lean_inc_ref(v_inst_699_);
v___f_703_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_703_, 0, v_inst_699_);
lean_inc_ref(v_inst_699_);
v___x_704_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_704_, 0, lean_box(0));
lean_closure_set(v___x_704_, 1, lean_box(0));
lean_closure_set(v___x_704_, 2, v_inst_699_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___f_700_);
lean_inc_ref(v_inst_699_);
v___x_706_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, lean_box(0));
lean_closure_set(v___x_706_, 2, v_inst_699_);
v___x_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
lean_ctor_set(v___x_707_, 2, v___f_701_);
lean_ctor_set(v___x_707_, 3, v___f_702_);
lean_ctor_set(v___x_707_, 4, v___f_703_);
v___x_708_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, lean_box(0));
lean_closure_set(v___x_708_, 2, v_inst_699_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt___redArg(lean_object* v_inst_710_, lean_object* v_f_711_, lean_object* v_x_712_){
_start:
{
lean_object* v_toApplicative_713_; lean_object* v_toFunctor_714_; lean_object* v_map_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_toApplicative_713_ = lean_ctor_get(v_inst_710_, 0);
lean_inc_ref(v_toApplicative_713_);
lean_dec_ref(v_inst_710_);
v_toFunctor_714_ = lean_ctor_get(v_toApplicative_713_, 0);
lean_inc_ref(v_toFunctor_714_);
lean_dec_ref(v_toApplicative_713_);
v_map_715_ = lean_ctor_get(v_toFunctor_714_, 0);
lean_inc(v_map_715_);
lean_dec_ref(v_toFunctor_714_);
v___x_716_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_716_, 0, lean_box(0));
lean_closure_set(v___x_716_, 1, lean_box(0));
lean_closure_set(v___x_716_, 2, lean_box(0));
lean_closure_set(v___x_716_, 3, v_f_711_);
v___x_717_ = lean_apply_4(v_map_715_, lean_box(0), lean_box(0), v___x_716_, v_x_712_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object* v_00_u03b5_718_, lean_object* v_m_719_, lean_object* v_inst_720_, lean_object* v_00_u03b5_x27_721_, lean_object* v_00_u03b1_722_, lean_object* v_f_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_toApplicative_725_; lean_object* v_toFunctor_726_; lean_object* v_map_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_toApplicative_725_ = lean_ctor_get(v_inst_720_, 0);
lean_inc_ref(v_toApplicative_725_);
lean_dec_ref(v_inst_720_);
v_toFunctor_726_ = lean_ctor_get(v_toApplicative_725_, 0);
lean_inc_ref(v_toFunctor_726_);
lean_dec_ref(v_toApplicative_725_);
v_map_727_ = lean_ctor_get(v_toFunctor_726_, 0);
lean_inc(v_map_727_);
lean_dec_ref(v_toFunctor_726_);
v___x_728_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_728_, 0, lean_box(0));
lean_closure_set(v___x_728_, 1, lean_box(0));
lean_closure_set(v___x_728_, 2, lean_box(0));
lean_closure_set(v___x_728_, 3, v_f_723_);
v___x_729_ = lean_apply_4(v_map_727_, lean_box(0), lean_box(0), v___x_728_, v_x_724_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__0(lean_object* v_inst_730_, lean_object* v_00_u03b1_731_, lean_object* v_e_732_){
_start:
{
lean_object* v_throw_733_; lean_object* v___x_734_; 
v_throw_733_ = lean_ctor_get(v_inst_730_, 0);
lean_inc(v_throw_733_);
lean_dec_ref(v_inst_730_);
v___x_734_ = lean_apply_2(v_throw_733_, lean_box(0), v_e_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__1(lean_object* v_inst_735_, lean_object* v_00_u03b1_736_, lean_object* v_x_737_, lean_object* v_handle_738_){
_start:
{
lean_object* v_tryCatch_739_; lean_object* v___x_740_; 
v_tryCatch_739_ = lean_ctor_get(v_inst_735_, 1);
lean_inc(v_tryCatch_739_);
lean_dec_ref(v_inst_735_);
v___x_740_ = lean_apply_3(v_tryCatch_739_, lean_box(0), v_x_737_, v_handle_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg(lean_object* v_inst_741_){
_start:
{
lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; 
lean_inc_ref(v_inst_741_);
v___f_742_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_742_, 0, v_inst_741_);
v___f_743_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_743_, 0, v_inst_741_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___f_742_);
lean_ctor_set(v___x_744_, 1, v___f_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object* v_m_745_, lean_object* v_00_u03b5_u2081_746_, lean_object* v_00_u03b5_u2082_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
lean_inc_ref(v_inst_748_);
v___f_749_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_749_, 0, v_inst_748_);
v___f_750_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_750_, 0, v_inst_748_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___f_749_);
lean_ctor_set(v___x_751_, 1, v___f_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object* v_toPure_752_, lean_object* v_00_u03b1_753_, lean_object* v_e_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_e_754_);
v___x_756_ = lean_apply_2(v_toPure_752_, lean_box(0), v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg(lean_object* v_inst_757_){
_start:
{
lean_object* v_toApplicative_758_; lean_object* v_toPure_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_toApplicative_758_ = lean_ctor_get(v_inst_757_, 0);
v_toPure_759_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_759_);
v___f_760_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_760_, 0, v_toPure_759_);
v___x_761_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_761_, 0, lean_box(0));
lean_closure_set(v___x_761_, 1, lean_box(0));
lean_closure_set(v___x_761_, 2, v_inst_757_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___f_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad(lean_object* v_m_763_, lean_object* v_00_u03b5_764_, lean_object* v_inst_765_){
_start:
{
lean_object* v_toApplicative_766_; lean_object* v_toPure_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_toApplicative_766_ = lean_ctor_get(v_inst_765_, 0);
v_toPure_767_ = lean_ctor_get(v_toApplicative_766_, 1);
lean_inc(v_toPure_767_);
v___f_768_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_768_, 0, v_toPure_767_);
v___x_769_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_769_, 0, lean_box(0));
lean_closure_set(v___x_769_, 1, lean_box(0));
lean_closure_set(v___x_769_, 2, v_inst_765_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___f_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad___redArg(lean_object* v_inst_771_, lean_object* v_inst_772_){
_start:
{
lean_object* v_toApplicative_773_; lean_object* v_toPure_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_toApplicative_773_ = lean_ctor_get(v_inst_771_, 0);
lean_inc_ref(v_toApplicative_773_);
lean_dec_ref(v_inst_771_);
v_toPure_774_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc(v_toPure_774_);
lean_dec_ref(v_toApplicative_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_inst_772_);
v___x_776_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad(lean_object* v_m_777_, lean_object* v_00_u03b5_778_, lean_object* v_00_u03b1_779_, lean_object* v_inst_780_, lean_object* v_inst_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_instInhabitedExceptTOfMonad___redArg(v_inst_780_, v_inst_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___lam__0(lean_object* v_00_u03b1_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___y_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object* v_00_u03b5_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_instMonadExceptOfExcept___closed__2));
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0(uint8_t v_useFirstEx_793_, lean_object* v_throw_794_, lean_object* v_e_u2081_795_, lean_object* v_e_u2082_796_){
_start:
{
if (v_useFirstEx_793_ == 0)
{
lean_object* v___x_797_; 
lean_dec(v_e_u2081_795_);
v___x_797_ = lean_apply_2(v_throw_794_, lean_box(0), v_e_u2082_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; 
lean_dec(v_e_u2082_796_);
v___x_798_ = lean_apply_2(v_throw_794_, lean_box(0), v_e_u2081_795_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0___boxed(lean_object* v_useFirstEx_799_, lean_object* v_throw_800_, lean_object* v_e_u2081_801_, lean_object* v_e_u2082_802_){
_start:
{
uint8_t v_useFirstEx_boxed_803_; lean_object* v_res_804_; 
v_useFirstEx_boxed_803_ = lean_unbox(v_useFirstEx_799_);
v_res_804_ = l_MonadExcept_orelse_x27___redArg___lam__0(v_useFirstEx_boxed_803_, v_throw_800_, v_e_u2081_801_, v_e_u2082_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1(uint8_t v_useFirstEx_805_, lean_object* v_throw_806_, lean_object* v_tryCatch_807_, lean_object* v_t_u2082_808_, lean_object* v_e_u2081_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; 
v___x_810_ = lean_box(v_useFirstEx_805_);
v___f_811_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_811_, 0, v___x_810_);
lean_closure_set(v___f_811_, 1, v_throw_806_);
lean_closure_set(v___f_811_, 2, v_e_u2081_809_);
v___x_812_ = lean_apply_3(v_tryCatch_807_, lean_box(0), v_t_u2082_808_, v___f_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1___boxed(lean_object* v_useFirstEx_813_, lean_object* v_throw_814_, lean_object* v_tryCatch_815_, lean_object* v_t_u2082_816_, lean_object* v_e_u2081_817_){
_start:
{
uint8_t v_useFirstEx_boxed_818_; lean_object* v_res_819_; 
v_useFirstEx_boxed_818_ = lean_unbox(v_useFirstEx_813_);
v_res_819_ = l_MonadExcept_orelse_x27___redArg___lam__1(v_useFirstEx_boxed_818_, v_throw_814_, v_tryCatch_815_, v_t_u2082_816_, v_e_u2081_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg(lean_object* v_inst_820_, lean_object* v_t_u2081_821_, lean_object* v_t_u2082_822_, uint8_t v_useFirstEx_823_){
_start:
{
lean_object* v_throw_824_; lean_object* v_tryCatch_825_; lean_object* v___x_826_; lean_object* v___f_827_; lean_object* v___x_828_; 
v_throw_824_ = lean_ctor_get(v_inst_820_, 0);
lean_inc(v_throw_824_);
v_tryCatch_825_ = lean_ctor_get(v_inst_820_, 1);
lean_inc(v_tryCatch_825_);
lean_dec_ref(v_inst_820_);
v___x_826_ = lean_box(v_useFirstEx_823_);
lean_inc(v_tryCatch_825_);
v___f_827_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_827_, 0, v___x_826_);
lean_closure_set(v___f_827_, 1, v_throw_824_);
lean_closure_set(v___f_827_, 2, v_tryCatch_825_);
lean_closure_set(v___f_827_, 3, v_t_u2082_822_);
v___x_828_ = lean_apply_3(v_tryCatch_825_, lean_box(0), v_t_u2081_821_, v___f_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___boxed(lean_object* v_inst_829_, lean_object* v_t_u2081_830_, lean_object* v_t_u2082_831_, lean_object* v_useFirstEx_832_){
_start:
{
uint8_t v_useFirstEx_boxed_833_; lean_object* v_res_834_; 
v_useFirstEx_boxed_833_ = lean_unbox(v_useFirstEx_832_);
v_res_834_ = l_MonadExcept_orelse_x27___redArg(v_inst_829_, v_t_u2081_830_, v_t_u2082_831_, v_useFirstEx_boxed_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object* v_00_u03b5_835_, lean_object* v_m_836_, lean_object* v_inst_837_, lean_object* v_00_u03b1_838_, lean_object* v_t_u2081_839_, lean_object* v_t_u2082_840_, uint8_t v_useFirstEx_841_){
_start:
{
lean_object* v_throw_842_; lean_object* v_tryCatch_843_; lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v___x_846_; 
v_throw_842_ = lean_ctor_get(v_inst_837_, 0);
lean_inc(v_throw_842_);
v_tryCatch_843_ = lean_ctor_get(v_inst_837_, 1);
lean_inc(v_tryCatch_843_);
lean_dec_ref(v_inst_837_);
v___x_844_ = lean_box(v_useFirstEx_841_);
lean_inc(v_tryCatch_843_);
v___f_845_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_845_, 0, v___x_844_);
lean_closure_set(v___f_845_, 1, v_throw_842_);
lean_closure_set(v___f_845_, 2, v_tryCatch_843_);
lean_closure_set(v___f_845_, 3, v_t_u2082_840_);
v___x_846_ = lean_apply_3(v_tryCatch_843_, lean_box(0), v_t_u2081_839_, v___f_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___boxed(lean_object* v_00_u03b5_847_, lean_object* v_m_848_, lean_object* v_inst_849_, lean_object* v_00_u03b1_850_, lean_object* v_t_u2081_851_, lean_object* v_t_u2082_852_, lean_object* v_useFirstEx_853_){
_start:
{
uint8_t v_useFirstEx_boxed_854_; lean_object* v_res_855_; 
v_useFirstEx_boxed_854_ = lean_unbox(v_useFirstEx_853_);
v_res_855_ = l_MonadExcept_orelse_x27(v_00_u03b5_847_, v_m_848_, v_inst_849_, v_00_u03b1_850_, v_t_u2081_851_, v_t_u2082_852_, v_useFirstEx_boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__0(lean_object* v_toPure_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_a_857_);
v___x_859_ = lean_apply_2(v_toPure_856_, lean_box(0), v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__1(lean_object* v_toPure_860_, lean_object* v_ex_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_ex_861_);
v___x_863_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg(lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_x_866_){
_start:
{
lean_object* v_toApplicative_867_; lean_object* v_tryCatch_868_; lean_object* v_toBind_869_; lean_object* v_toPure_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_toApplicative_867_ = lean_ctor_get(v_inst_864_, 0);
lean_inc_ref(v_toApplicative_867_);
v_tryCatch_868_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_tryCatch_868_);
lean_dec_ref(v_inst_865_);
v_toBind_869_ = lean_ctor_get(v_inst_864_, 1);
lean_inc(v_toBind_869_);
lean_dec_ref(v_inst_864_);
v_toPure_870_ = lean_ctor_get(v_toApplicative_867_, 1);
lean_inc(v_toPure_870_);
lean_dec_ref(v_toApplicative_867_);
lean_inc(v_toPure_870_);
v___f_871_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_871_, 0, v_toPure_870_);
v___f_872_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_872_, 0, v_toPure_870_);
v___x_873_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v_x_866_, v___f_871_);
v___x_874_ = lean_apply_3(v_tryCatch_868_, lean_box(0), v___x_873_, v___f_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_observing(lean_object* v_00_u03b5_875_, lean_object* v_00_u03b1_876_, lean_object* v_m_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_x_880_){
_start:
{
lean_object* v_toApplicative_881_; lean_object* v_tryCatch_882_; lean_object* v_toBind_883_; lean_object* v_toPure_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_toApplicative_881_ = lean_ctor_get(v_inst_878_, 0);
lean_inc_ref(v_toApplicative_881_);
v_tryCatch_882_ = lean_ctor_get(v_inst_879_, 1);
lean_inc(v_tryCatch_882_);
lean_dec_ref(v_inst_879_);
v_toBind_883_ = lean_ctor_get(v_inst_878_, 1);
lean_inc(v_toBind_883_);
lean_dec_ref(v_inst_878_);
v_toPure_884_ = lean_ctor_get(v_toApplicative_881_, 1);
lean_inc(v_toPure_884_);
lean_dec_ref(v_toApplicative_881_);
lean_inc(v_toPure_884_);
v___f_885_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_885_, 0, v_toPure_884_);
v___f_886_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_886_, 0, v_toPure_884_);
v___x_887_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v_x_880_, v___f_885_);
v___x_888_ = lean_apply_3(v_tryCatch_882_, lean_box(0), v___x_887_, v___f_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___redArg(lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_throw_893_; lean_object* v___x_894_; 
lean_dec(v_inst_890_);
v_a_892_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v_x_891_);
v_throw_893_ = lean_ctor_get(v_inst_889_, 0);
lean_inc(v_throw_893_);
lean_dec_ref(v_inst_889_);
v___x_894_ = lean_apply_2(v_throw_893_, lean_box(0), v_a_892_);
return v___x_894_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_896_; 
lean_dec_ref(v_inst_889_);
v_a_895_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v_x_891_);
v___x_896_ = lean_apply_2(v_inst_890_, lean_box(0), v_a_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept(lean_object* v_00_u03b5_897_, lean_object* v_m_898_, lean_object* v_00_u03b1_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_liftExcept___redArg(v_inst_900_, v_inst_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_904_, lean_object* v_x_905_){
_start:
{
lean_inc(v_x_905_);
return v_x_905_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_instMonadControlExceptTOfMonad___redArg___lam__0(v_00_u03b2_906_, v_x_907_);
lean_dec(v_x_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__2(lean_object* v_inst_909_, lean_object* v___f_910_, lean_object* v___f_911_, lean_object* v_00_u03b1_912_, lean_object* v_f_913_){
_start:
{
lean_object* v_toApplicative_914_; lean_object* v_toFunctor_915_; lean_object* v_map_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_toApplicative_914_ = lean_ctor_get(v_inst_909_, 0);
lean_inc_ref(v_toApplicative_914_);
lean_dec_ref(v_inst_909_);
v_toFunctor_915_ = lean_ctor_get(v_toApplicative_914_, 0);
lean_inc_ref(v_toFunctor_915_);
lean_dec_ref(v_toApplicative_914_);
v_map_916_ = lean_ctor_get(v_toFunctor_915_, 0);
lean_inc(v_map_916_);
lean_dec_ref(v_toFunctor_915_);
v___x_917_ = lean_apply_1(v_f_913_, v___f_910_);
v___x_918_ = lean_apply_4(v_map_916_, lean_box(0), lean_box(0), v___f_911_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_919_, lean_object* v_x_920_){
_start:
{
lean_inc(v_x_920_);
return v_x_920_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_921_, lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_instMonadControlExceptTOfMonad___redArg___lam__1(v_00_u03b1_921_, v_x_922_);
lean_dec(v_x_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg(lean_object* v_inst_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_931_; 
v___f_927_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__0));
v___f_928_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___f_929_ = lean_alloc_closure((void*)(l_instMonadControlExceptTOfMonad___redArg___lam__2), 5, 3);
lean_closure_set(v___f_929_, 0, v_inst_926_);
lean_closure_set(v___f_929_, 1, v___f_927_);
lean_closure_set(v___f_929_, 2, v___f_928_);
v___f_930_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__1));
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___f_929_);
lean_ctor_set(v___x_931_, 1, v___f_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad(lean_object* v_00_u03b5_932_, lean_object* v_m_933_, lean_object* v_inst_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_instMonadControlExceptTOfMonad___redArg(v_inst_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0(lean_object* v_finalizer_936_, lean_object* v_x_937_){
_start:
{
lean_inc(v_finalizer_936_);
return v_finalizer_936_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0___boxed(lean_object* v_finalizer_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_tryFinally___redArg___lam__0(v_finalizer_938_, v_x_939_);
lean_dec(v_x_939_);
lean_dec(v_finalizer_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1(lean_object* v_x_941_){
_start:
{
lean_object* v_fst_942_; 
v_fst_942_ = lean_ctor_get(v_x_941_, 0);
lean_inc(v_fst_942_);
return v_fst_942_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1___boxed(lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_tryFinally___redArg___lam__1(v_x_943_);
lean_dec_ref(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg(lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_x_948_, lean_object* v_finalizer_949_){
_start:
{
lean_object* v_map_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v_y_953_; lean_object* v___x_954_; 
v_map_950_ = lean_ctor_get(v_inst_947_, 0);
lean_inc(v_map_950_);
lean_dec_ref(v_inst_947_);
v___f_951_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_951_, 0, v_finalizer_949_);
v___f_952_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_953_ = lean_apply_4(v_inst_946_, lean_box(0), lean_box(0), v_x_948_, v___f_951_);
v___x_954_ = lean_apply_4(v_map_950_, lean_box(0), lean_box(0), v___f_952_, v_y_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_tryFinally(lean_object* v_m_955_, lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_x_960_, lean_object* v_finalizer_961_){
_start:
{
lean_object* v_map_962_; lean_object* v___f_963_; lean_object* v___f_964_; lean_object* v_y_965_; lean_object* v___x_966_; 
v_map_962_ = lean_ctor_get(v_inst_959_, 0);
lean_inc(v_map_962_);
lean_dec_ref(v_inst_959_);
v___f_963_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_963_, 0, v_finalizer_961_);
v___f_964_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_965_ = lean_apply_4(v_inst_958_, lean_box(0), lean_box(0), v_x_960_, v___f_963_);
v___x_966_ = lean_apply_4(v_map_962_, lean_box(0), lean_box(0), v___f_964_, v_y_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Id_finally___lam__0(lean_object* v_00_u03b1_967_, lean_object* v_00_u03b2_968_, lean_object* v_x_969_, lean_object* v_h_970_){
_start:
{
lean_object* v___x_971_; lean_object* v_b_972_; lean_object* v___x_973_; 
lean_inc(v_x_969_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_x_969_);
v_b_972_ = lean_apply_1(v_h_970_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_x_969_);
lean_ctor_set(v___x_973_, 1, v_b_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__0(lean_object* v_toPure_976_, lean_object* v_r_977_){
_start:
{
lean_object* v_e_979_; lean_object* v_fst_982_; 
v_fst_982_ = lean_ctor_get(v_r_977_, 0);
lean_inc(v_fst_982_);
if (lean_obj_tag(v_fst_982_) == 0)
{
lean_object* v_snd_983_; 
v_snd_983_ = lean_ctor_get(v_r_977_, 1);
lean_inc(v_snd_983_);
lean_dec_ref(v_r_977_);
if (lean_obj_tag(v_snd_983_) == 0)
{
lean_object* v_a_984_; 
lean_dec_ref(v_fst_982_);
v_a_984_ = lean_ctor_get(v_snd_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v_snd_983_);
v_e_979_ = v_a_984_;
goto v___jp_978_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_a_985_ = lean_ctor_get(v_fst_982_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v_fst_982_);
v_isSharedCheck_993_ = !lean_is_exclusive(v_snd_983_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_snd_983_, 0);
lean_dec(v_unused_994_);
v___x_987_ = v_snd_983_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_dec(v_snd_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v_a_985_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_apply_2(v_toPure_976_, lean_box(0), v___x_990_);
return v___x_991_;
}
}
}
}
else
{
lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1013_; 
v_snd_995_ = lean_ctor_get(v_r_977_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_r_977_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_r_977_, 0);
lean_dec(v_unused_1014_);
v___x_997_ = v_r_977_;
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_dec(v_r_977_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
if (lean_obj_tag(v_snd_995_) == 0)
{
lean_object* v_a_999_; 
lean_del_object(v___x_997_);
lean_dec_ref(v_fst_982_);
v_a_999_ = lean_ctor_get(v_snd_995_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v_snd_995_);
v_e_979_ = v_a_999_;
goto v___jp_978_;
}
else
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1012_; 
v_a_1000_ = lean_ctor_get(v_fst_982_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v_fst_982_);
v_a_1001_ = lean_ctor_get(v_snd_995_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_snd_995_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1003_ = v_snd_995_;
v_isShared_1004_ = v_isSharedCheck_1012_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v_snd_995_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1012_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_a_1001_);
lean_ctor_set(v___x_997_, 0, v_a_1000_);
v___x_1006_ = v___x_997_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1000_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_2(v_toPure_976_, lean_box(0), v___x_1008_);
return v___x_1009_;
}
}
}
}
}
}
v___jp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_e_979_);
v___x_981_ = lean_apply_2(v_toPure_976_, lean_box(0), v___x_980_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__1(lean_object* v_h_1015_, lean_object* v_e_x3f_1016_){
_start:
{
if (lean_obj_tag(v_e_x3f_1016_) == 0)
{
goto v___jp_1017_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
v_val_1020_ = lean_ctor_get(v_e_x3f_1016_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_e_x3f_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1022_ = v_e_x3f_1016_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v_e_x3f_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
if (lean_obj_tag(v_val_1020_) == 0)
{
lean_dec_ref(v_val_1020_);
lean_del_object(v___x_1022_);
goto v___jp_1017_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; 
v_a_1024_ = lean_ctor_get(v_val_1020_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v_val_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_a_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1024_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_apply_1(v_h_1015_, v___x_1026_);
return v___x_1027_;
}
}
}
}
v___jp_1017_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_apply_1(v_h_1015_, v___x_1018_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__2(lean_object* v_inst_1030_, lean_object* v_toBind_1031_, lean_object* v___f_1032_, lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_h_1036_){
_start:
{
lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___f_1037_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1037_, 0, v_h_1036_);
v___x_1038_ = lean_apply_4(v_inst_1030_, lean_box(0), lean_box(0), v_x_1035_, v___f_1037_);
v___x_1039_ = lean_apply_4(v_toBind_1031_, lean_box(0), lean_box(0), v___x_1038_, v___f_1032_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg(lean_object* v_inst_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v_toApplicative_1042_; lean_object* v_toBind_1043_; lean_object* v_toPure_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; 
v_toApplicative_1042_ = lean_ctor_get(v_inst_1041_, 0);
lean_inc_ref(v_toApplicative_1042_);
v_toBind_1043_ = lean_ctor_get(v_inst_1041_, 1);
lean_inc(v_toBind_1043_);
lean_dec_ref(v_inst_1041_);
v_toPure_1044_ = lean_ctor_get(v_toApplicative_1042_, 1);
lean_inc(v_toPure_1044_);
lean_dec_ref(v_toApplicative_1042_);
v___f_1045_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1045_, 0, v_toPure_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1046_, 0, v_inst_1040_);
lean_closure_set(v___f_1046_, 1, v_toBind_1043_);
lean_closure_set(v___f_1046_, 2, v___f_1045_);
return v___f_1046_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object* v_m_1047_, lean_object* v_00_u03b5_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v_toApplicative_1051_; lean_object* v_toBind_1052_; lean_object* v_toPure_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; 
v_toApplicative_1051_ = lean_ctor_get(v_inst_1050_, 0);
lean_inc_ref(v_toApplicative_1051_);
v_toBind_1052_ = lean_ctor_get(v_inst_1050_, 1);
lean_inc(v_toBind_1052_);
lean_dec_ref(v_inst_1050_);
v_toPure_1053_ = lean_ctor_get(v_toApplicative_1051_, 1);
lean_inc(v_toPure_1053_);
lean_dec_ref(v_toApplicative_1051_);
v___f_1054_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1054_, 0, v_toPure_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1055_, 0, v_inst_1049_);
lean_closure_set(v___f_1055_, 1, v_toBind_1052_);
lean_closure_set(v___f_1055_, 2, v___f_1054_);
return v___f_1055_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__0(lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v_x_1056_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v_x_1056_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v_x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v_x_1056_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v_x_1056_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v_x_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__1(lean_object* v_toFunctor_1073_, lean_object* v_inst_1074_, lean_object* v___f_1075_, lean_object* v_00_u03b1_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_map_1078_; lean_object* v___x_1079_; lean_object* v_this_1080_; 
v_map_1078_ = lean_ctor_get(v_toFunctor_1073_, 0);
lean_inc(v_map_1078_);
lean_dec_ref(v_toFunctor_1073_);
v___x_1079_ = lean_apply_2(v_inst_1074_, lean_box(0), v_x_1077_);
v_this_1080_ = lean_apply_4(v_map_1078_, lean_box(0), lean_box(0), v___f_1075_, v___x_1079_);
return v_this_1080_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg(lean_object* v_inst_1082_, lean_object* v_inst_1083_){
_start:
{
lean_object* v_toApplicative_1084_; lean_object* v_toFunctor_1085_; lean_object* v___f_1086_; lean_object* v___f_1087_; 
v_toApplicative_1084_ = lean_ctor_get(v_inst_1082_, 0);
lean_inc_ref(v_toApplicative_1084_);
lean_dec_ref(v_inst_1082_);
v_toFunctor_1085_ = lean_ctor_get(v_toApplicative_1084_, 0);
lean_inc_ref(v_toFunctor_1085_);
lean_dec_ref(v_toApplicative_1084_);
v___f_1086_ = ((lean_object*)(l_instMonadAttachExceptTOfMonad___redArg___closed__0));
v___f_1087_ = lean_alloc_closure((void*)(l_instMonadAttachExceptTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1087_, 0, v_toFunctor_1085_);
lean_closure_set(v___f_1087_, 1, v_inst_1083_);
lean_closure_set(v___f_1087_, 2, v___f_1086_);
return v___f_1087_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad(lean_object* v_m_1088_, lean_object* v_00_u03b5_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_instMonadAttachExceptTOfMonad___redArg(v_inst_1090_, v_inst_1091_);
return v___x_1092_;
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
