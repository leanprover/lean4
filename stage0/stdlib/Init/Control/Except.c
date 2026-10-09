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
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Except_instMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___redArg___closed__0 = (const lean_object*)&l_Except_instMonad___redArg___closed__0_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___redArg___closed__1 = (const lean_object*)&l_Except_instMonad___redArg___closed__1_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___redArg___closed__2 = (const lean_object*)&l_Except_instMonad___redArg___closed__2_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Except_instMonad___redArg___closed__3 = (const lean_object*)&l_Except_instMonad___redArg___closed__3_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___redArg___closed__4 = (const lean_object*)&l_Except_instMonad___redArg___closed__4_value;
static const lean_ctor_object l_Except_instMonad___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___redArg___closed__4_value),((lean_object*)&l_Except_instMonad___redArg___closed__0_value)}};
static const lean_object* l_Except_instMonad___redArg___closed__5 = (const lean_object*)&l_Except_instMonad___redArg___closed__5_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___redArg___closed__6 = (const lean_object*)&l_Except_instMonad___redArg___closed__6_value;
static const lean_ctor_object l_Except_instMonad___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___redArg___closed__5_value),((lean_object*)&l_Except_instMonad___redArg___closed__6_value),((lean_object*)&l_Except_instMonad___redArg___closed__1_value),((lean_object*)&l_Except_instMonad___redArg___closed__2_value),((lean_object*)&l_Except_instMonad___redArg___closed__3_value)}};
static const lean_object* l_Except_instMonad___redArg___closed__7 = (const lean_object*)&l_Except_instMonad___redArg___closed__7_value;
static const lean_closure_object l_Except_instMonad___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Except_instMonad___redArg___closed__8 = (const lean_object*)&l_Except_instMonad___redArg___closed__8_value;
static const lean_ctor_object l_Except_instMonad___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Except_instMonad___redArg___closed__7_value),((lean_object*)&l_Except_instMonad___redArg___closed__8_value)}};
static const lean_object* l_Except_instMonad___redArg___closed__9 = (const lean_object*)&l_Except_instMonad___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Except_instMonad___redArg();
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ExceptT_instMonadFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptT_instMonadFunctor___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ExceptT_instMonadFunctor___redArg___closed__0 = (const lean_object*)&l_ExceptT_instMonadFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg();
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfExcept___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfExcept___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadExceptOfExcept___redArg___closed__0 = (const lean_object*)&l_instMonadExceptOfExcept___redArg___closed__0_value;
static const lean_closure_object l_instMonadExceptOfExcept___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_tryCatch, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfExcept___redArg___closed__1 = (const lean_object*)&l_instMonadExceptOfExcept___redArg___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfExcept___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfExcept___redArg___closed__0_value),((lean_object*)&l_instMonadExceptOfExcept___redArg___closed__1_value)}};
static const lean_object* l_instMonadExceptOfExcept___redArg___closed__2 = (const lean_object*)&l_instMonadExceptOfExcept___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg();
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___boxed(lean_object*);
static lean_once_cell_t l_instMonadExceptOfExcept___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadExceptOfExcept___closed__0;
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
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachExcept___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachExcept___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachExcept___redArg___closed__0 = (const lean_object*)&l_instMonadAttachExcept___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg();
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachExcept(lean_object*);
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
lean_dec_ref_known(v_x_48_, 1);
v___x_52_ = lean_apply_1(v_h__1_49_, v_a_51_);
return v___x_52_;
}
else
{
lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_49_);
v_a_53_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v_x_48_, 1);
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
lean_dec_ref_known(v_x_58_, 1);
v___x_62_ = lean_apply_1(v_h__1_59_, v_a_61_);
return v___x_62_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_59_);
v_a_63_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v_x_58_, 1);
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
lean_dec_ref_known(v_ma_106_, 1);
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
lean_dec_ref_known(v_ma_121_, 1);
v___x_132_ = lean_apply_1(v_f_122_, v_a_131_);
return v___x_132_;
}
}
}
uint8_t l_Except_toBool___redArg(lean_object* v_x_133_){
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
LEAN_EXPORT void l_Except_toBool___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_133_ = stack[0].m_obj;
uint8_t v_res_136_;
v_res_136_ = l_Except_toBool___redArg(v_x_133_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_Except_toBool___redArg___boxed(lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Except_toBool___redArg(v_x_137_);
lean_dec_ref(v_x_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
uint8_t l_Except_toBool(lean_object* v_00_u03b5_140_, lean_object* v_00_u03b1_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
}
}
LEAN_EXPORT void l_Except_toBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[2].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Except_toBool(lean_box(0), lean_box(0), v_x_142_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Except_toBool___boxed(lean_object* v_00_u03b5_146_, lean_object* v_00_u03b1_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Except_toBool(v_00_u03b5_146_, v_00_u03b1_147_, v_x_148_);
lean_dec_ref(v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
uint8_t l_Except_isOk___redArg(lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_a_151_) == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 1;
return v___x_153_;
}
}
}
LEAN_EXPORT void l_Except_isOk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_151_ = stack[0].m_obj;
uint8_t v_res_154_;
v_res_154_ = l_Except_isOk___redArg(v_a_151_);
stack->m_num = v_res_154_;
}
LEAN_EXPORT lean_object* l_Except_isOk___redArg___boxed(lean_object* v_a_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Except_isOk___redArg(v_a_155_);
lean_dec_ref(v_a_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
uint8_t l_Except_isOk(lean_object* v_00_u03b5_158_, lean_object* v_00_u03b1_159_, lean_object* v_a_160_){
_start:
{
if (lean_obj_tag(v_a_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
}
}
LEAN_EXPORT void l_Except_isOk_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_160_ = stack[2].m_obj;
uint8_t v_res_163_;
v_res_163_ = l_Except_isOk(lean_box(0), lean_box(0), v_a_160_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Except_isOk___boxed(lean_object* v_00_u03b5_164_, lean_object* v_00_u03b1_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Except_isOk(v_00_u03b5_164_, v_00_u03b1_165_, v_a_166_);
lean_dec_ref(v_a_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Except_toOption___redArg(lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref_known(v_x_169_, 1);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toOption(lean_object* v_00_u03b5_179_, lean_object* v_00_u03b1_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_182_; 
lean_dec_ref_known(v_x_181_, 1);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v_x_181_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v_x_181_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v_x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch___redArg(lean_object* v_ma_191_, lean_object* v_handle_192_){
_start:
{
if (lean_obj_tag(v_ma_191_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; 
v_a_193_ = lean_ctor_get(v_ma_191_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v_ma_191_, 1);
v___x_194_ = lean_apply_1(v_handle_192_, v_a_193_);
return v___x_194_;
}
else
{
lean_dec_ref(v_handle_192_);
return v_ma_191_;
}
}
}
LEAN_EXPORT lean_object* l_Except_tryCatch(lean_object* v_00_u03b5_195_, lean_object* v_00_u03b1_196_, lean_object* v_ma_197_, lean_object* v_handle_198_){
_start:
{
if (lean_obj_tag(v_ma_197_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v_ma_197_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v_ma_197_, 1);
v___x_200_ = lean_apply_1(v_handle_198_, v_a_199_);
return v___x_200_;
}
else
{
lean_dec_ref(v_handle_198_);
return v_ma_197_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_y_202_, v___x_203_);
return v___x_204_;
}
else
{
lean_dec_ref(v_y_202_);
lean_inc_ref(v_x_201_);
return v_x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___redArg___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Except_orElseLazy___redArg(v_x_205_, v_y_206_);
lean_dec_ref(v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy(lean_object* v_00_u03b5_208_, lean_object* v_00_u03b1_209_, lean_object* v_x_210_, lean_object* v_y_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Except_orElseLazy___redArg(v_x_210_, v_y_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Except_orElseLazy___boxed(lean_object* v_00_u03b5_213_, lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v_y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Except_orElseLazy(v_00_u03b5_213_, v_00_u03b1_214_, v_x_215_, v_y_216_);
lean_dec_ref(v_x_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__0(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
if (lean_obj_tag(v___y_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v___y_220_);
v_a_222_ = lean_ctor_get(v___y_221_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___y_221_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___y_221_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___y_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v___y_221_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___y_221_, 0);
lean_dec(v_unused_237_);
v___x_231_ = v___y_221_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_dec(v___y_221_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___y_220_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___y_220_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__1(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_f_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_f_240_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_x_241_);
v_a_242_ = lean_ctor_get(v_f_240_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_f_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v_f_240_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v_f_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v_f_240_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v_f_240_, 1);
v___x_251_ = lean_box(0);
v___x_252_ = lean_apply_1(v_x_241_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_250_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v___x_252_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_apply_1(v_a_250_, v_a_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_x_272_, lean_object* v_y_273_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_dec_ref(v_y_273_);
lean_inc_ref(v_x_272_);
return v_x_272_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_box(0);
v___x_275_ = lean_apply_1(v_y_273_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_dec_ref_known(v___x_275_, 1);
lean_inc_ref(v_x_272_);
return v_x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_x_286_, lean_object* v_y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Except_instMonad___redArg___lam__2(v_00_u03b1_284_, v_00_u03b2_285_, v_x_286_, v_y_287_);
lean_dec_ref(v_x_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__3(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_x_291_, lean_object* v_y_292_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_y_292_);
v_a_293_ = lean_ctor_get(v_x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v_x_291_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v_x_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref_known(v_x_291_, 1);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_y_292_, v___x_301_);
return v___x_302_;
}
}
}
lean_object* l_Except_instMonad___redArg(){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Except_instMonad___redArg___closed__9));
return v___x_323_;
}
}
LEAN_EXPORT void l_Except_instMonad___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_324_;
v_res_324_ = l_Except_instMonad___redArg();
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___boxed(lean_object* v___dummy_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Except_instMonad___redArg();
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad(lean_object* v_00_u03b5_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_Except_instMonad___redArg___closed__9));
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg(lean_object* v_x_329_){
_start:
{
lean_inc(v_x_329_);
return v_x_329_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg___boxed(lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_ExceptT_mk___redArg(v_x_330_);
lean_dec(v_x_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object* v_00_u03b5_332_, lean_object* v_m_333_, lean_object* v_00_u03b1_334_, lean_object* v_x_335_){
_start:
{
lean_inc(v_x_335_);
return v_x_335_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___boxed(lean_object* v_00_u03b5_336_, lean_object* v_m_337_, lean_object* v_00_u03b1_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_ExceptT_mk(v_00_u03b5_336_, v_m_337_, v_00_u03b1_338_, v_x_339_);
lean_dec(v_x_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg(lean_object* v_x_341_){
_start:
{
lean_inc(v_x_341_);
return v_x_341_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg___boxed(lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_ExceptT_run___redArg(v_x_342_);
lean_dec(v_x_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object* v_00_u03b5_344_, lean_object* v_m_345_, lean_object* v_00_u03b1_346_, lean_object* v_x_347_){
_start:
{
lean_inc(v_x_347_);
return v_x_347_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___boxed(lean_object* v_00_u03b5_348_, lean_object* v_m_349_, lean_object* v_00_u03b1_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_ExceptT_run(v_00_u03b5_348_, v_m_349_, v_00_u03b1_350_, v_x_351_);
lean_dec(v_x_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg___lam__0(lean_object* v_error_353_, lean_object* v_ok_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; 
lean_dec(v_ok_354_);
v_a_356_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v_x_355_, 1);
v___x_357_ = lean_apply_1(v_error_353_, v_a_356_);
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_359_; 
lean_dec(v_error_353_);
v_a_358_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_x_355_, 1);
v___x_359_ = lean_apply_1(v_ok_354_, v_a_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg(lean_object* v_inst_360_, lean_object* v_x_361_, lean_object* v_ok_362_, lean_object* v_error_363_){
_start:
{
lean_object* v_toBind_364_; lean_object* v___f_365_; lean_object* v___x_366_; 
v_toBind_364_ = lean_ctor_get(v_inst_360_, 1);
lean_inc(v_toBind_364_);
lean_dec_ref(v_inst_360_);
v___f_365_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_365_, 0, v_error_363_);
lean_closure_set(v___f_365_, 1, v_ok_362_);
v___x_366_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v_x_361_, v___f_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK(lean_object* v_m_367_, lean_object* v_00_u03b5_368_, lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_inst_371_, lean_object* v_x_372_, lean_object* v_ok_373_, lean_object* v_error_374_){
_start:
{
lean_object* v_toBind_375_; lean_object* v___f_376_; lean_object* v___x_377_; 
v_toBind_375_ = lean_ctor_get(v_inst_371_, 1);
lean_inc(v_toBind_375_);
lean_dec_ref(v_inst_371_);
v___f_376_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_376_, 0, v_error_374_);
lean_closure_set(v___f_376_, 1, v_ok_373_);
v___x_377_ = lean_apply_4(v_toBind_375_, lean_box(0), lean_box(0), v_x_372_, v___f_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg___lam__0(lean_object* v_toPure_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v_x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v_x_379_);
v___x_381_ = lean_apply_2(v_toPure_378_, lean_box(0), v_a_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg(lean_object* v_inst_382_, lean_object* v_x_383_){
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
LEAN_EXPORT lean_object* l_ExceptT_runCatch(lean_object* v_m_389_, lean_object* v_00_u03b1_390_, lean_object* v_inst_391_, lean_object* v_x_392_){
_start:
{
lean_object* v_toApplicative_393_; lean_object* v_toBind_394_; lean_object* v_toPure_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
v_toApplicative_393_ = lean_ctor_get(v_inst_391_, 0);
lean_inc_ref(v_toApplicative_393_);
v_toBind_394_ = lean_ctor_get(v_inst_391_, 1);
lean_inc(v_toBind_394_);
lean_dec_ref(v_inst_391_);
v_toPure_395_ = lean_ctor_get(v_toApplicative_393_, 1);
lean_inc(v_toPure_395_);
lean_dec_ref(v_toApplicative_393_);
v___f_396_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_396_, 0, v_toPure_395_);
v___x_397_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v_x_392_, v___f_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure___redArg(lean_object* v_inst_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toPure_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_398_, 0);
lean_inc_ref(v_toApplicative_400_);
lean_dec_ref(v_inst_398_);
v_toPure_401_ = lean_ctor_get(v_toApplicative_400_, 1);
lean_inc(v_toPure_401_);
lean_dec_ref(v_toApplicative_400_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_a_399_);
v___x_403_ = lean_apply_2(v_toPure_401_, lean_box(0), v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object* v_00_u03b5_404_, lean_object* v_m_405_, lean_object* v_inst_406_, lean_object* v_00_u03b1_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toPure_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_406_, 0);
lean_inc_ref(v_toApplicative_409_);
lean_dec_ref(v_inst_406_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_409_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_a_408_);
v___x_412_ = lean_apply_2(v_toPure_410_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___redArg(lean_object* v_inst_413_, lean_object* v_f_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_toApplicative_416_; 
v_toApplicative_416_ = lean_ctor_get(v_inst_413_, 0);
lean_inc_ref(v_toApplicative_416_);
lean_dec_ref(v_inst_413_);
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v_toPure_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_f_414_);
v_toPure_417_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_417_);
lean_dec_ref(v_toApplicative_416_);
v_a_418_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v_x_415_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_x_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
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
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = lean_apply_2(v_toPure_417_, lean_box(0), v___x_423_);
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_428_; 
lean_dec_ref(v_toApplicative_416_);
v_a_427_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v_x_415_, 1);
v___x_428_ = lean_apply_1(v_f_414_, v_a_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object* v_00_u03b5_429_, lean_object* v_m_430_, lean_object* v_inst_431_, lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_f_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_toApplicative_436_; 
v_toApplicative_436_ = lean_ctor_get(v_inst_431_, 0);
lean_inc_ref(v_toApplicative_436_);
lean_dec_ref(v_inst_431_);
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v_toPure_437_; lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_f_434_);
v_toPure_437_ = lean_ctor_get(v_toApplicative_436_, 1);
lean_inc(v_toPure_437_);
lean_dec_ref(v_toApplicative_436_);
v_a_438_ = lean_ctor_get(v_x_435_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v_x_435_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_435_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_apply_2(v_toPure_437_, lean_box(0), v___x_443_);
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; 
lean_dec_ref(v_toApplicative_436_);
v_a_447_ = lean_ctor_get(v_x_435_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_x_435_, 1);
v___x_448_ = lean_apply_1(v_f_434_, v_a_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind___redArg(lean_object* v_inst_449_, lean_object* v_ma_450_, lean_object* v_f_451_){
_start:
{
lean_object* v_toBind_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_toBind_452_ = lean_ctor_get(v_inst_449_, 1);
lean_inc(v_toBind_452_);
v___x_453_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_453_, 0, lean_box(0));
lean_closure_set(v___x_453_, 1, lean_box(0));
lean_closure_set(v___x_453_, 2, v_inst_449_);
lean_closure_set(v___x_453_, 3, lean_box(0));
lean_closure_set(v___x_453_, 4, lean_box(0));
lean_closure_set(v___x_453_, 5, v_f_451_);
v___x_454_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v_ma_450_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object* v_00_u03b5_455_, lean_object* v_m_456_, lean_object* v_inst_457_, lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_ma_460_, lean_object* v_f_461_){
_start:
{
lean_object* v_toBind_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_toBind_462_ = lean_ctor_get(v_inst_457_, 1);
lean_inc(v_toBind_462_);
v___x_463_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_463_, 0, lean_box(0));
lean_closure_set(v___x_463_, 1, lean_box(0));
lean_closure_set(v___x_463_, 2, v_inst_457_);
lean_closure_set(v___x_463_, 3, lean_box(0));
lean_closure_set(v___x_463_, 4, lean_box(0));
lean_closure_set(v___x_463_, 5, v_f_461_);
v___x_464_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v_ma_460_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg___lam__0(lean_object* v_toPure_465_, lean_object* v_f_466_, lean_object* v_a_467_){
_start:
{
if (lean_obj_tag(v_a_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_f_466_);
v_a_468_ = lean_ctor_get(v_a_467_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_476_ == 0)
{
v___x_470_ = v_a_467_;
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v_a_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_476_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_475_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; 
v___x_474_ = lean_apply_2(v_toPure_465_, lean_box(0), v___x_473_);
return v___x_474_;
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v_a_477_ = lean_ctor_get(v_a_467_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v_a_467_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v_a_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_apply_1(v_f_466_, v_a_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_apply_2(v_toPure_465_, lean_box(0), v___x_483_);
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg(lean_object* v_inst_487_, lean_object* v_f_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_toApplicative_490_; lean_object* v_toBind_491_; lean_object* v_toPure_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_toApplicative_490_ = lean_ctor_get(v_inst_487_, 0);
lean_inc_ref(v_toApplicative_490_);
v_toBind_491_ = lean_ctor_get(v_inst_487_, 1);
lean_inc(v_toBind_491_);
lean_dec_ref(v_inst_487_);
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
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object* v_00_u03b5_495_, lean_object* v_m_496_, lean_object* v_inst_497_, lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_f_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_toApplicative_502_; lean_object* v_toBind_503_; lean_object* v_toPure_504_; lean_object* v___f_505_; lean_object* v___x_506_; 
v_toApplicative_502_ = lean_ctor_get(v_inst_497_, 0);
lean_inc_ref(v_toApplicative_502_);
v_toBind_503_ = lean_ctor_get(v_inst_497_, 1);
lean_inc(v_toBind_503_);
lean_dec_ref(v_inst_497_);
v_toPure_504_ = lean_ctor_get(v_toApplicative_502_, 1);
lean_inc(v_toPure_504_);
lean_dec_ref(v_toApplicative_502_);
v___f_505_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_505_, 0, v_toPure_504_);
lean_closure_set(v___f_505_, 1, v_f_500_);
v___x_506_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v_x_501_, v___f_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg___lam__0(lean_object* v_a_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_a_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg(lean_object* v_inst_510_, lean_object* v_t_511_){
_start:
{
lean_object* v_toApplicative_512_; lean_object* v_toFunctor_513_; lean_object* v_map_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v_toApplicative_512_ = lean_ctor_get(v_inst_510_, 0);
lean_inc_ref(v_toApplicative_512_);
lean_dec_ref(v_inst_510_);
v_toFunctor_513_ = lean_ctor_get(v_toApplicative_512_, 0);
lean_inc_ref(v_toFunctor_513_);
lean_dec_ref(v_toApplicative_512_);
v_map_514_ = lean_ctor_get(v_toFunctor_513_, 0);
lean_inc(v_map_514_);
lean_dec_ref(v_toFunctor_513_);
v___f_515_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_516_ = lean_apply_4(v_map_514_, lean_box(0), lean_box(0), v___f_515_, v_t_511_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object* v_00_u03b5_517_, lean_object* v_m_518_, lean_object* v_inst_519_, lean_object* v_00_u03b1_520_, lean_object* v_t_521_){
_start:
{
lean_object* v_toApplicative_522_; lean_object* v_toFunctor_523_; lean_object* v_map_524_; lean_object* v___f_525_; lean_object* v___x_526_; 
v_toApplicative_522_ = lean_ctor_get(v_inst_519_, 0);
lean_inc_ref(v_toApplicative_522_);
lean_dec_ref(v_inst_519_);
v_toFunctor_523_ = lean_ctor_get(v_toApplicative_522_, 0);
lean_inc_ref(v_toFunctor_523_);
lean_dec_ref(v_toApplicative_522_);
v_map_524_ = lean_ctor_get(v_toFunctor_523_, 0);
lean_inc(v_map_524_);
lean_dec_ref(v_toFunctor_523_);
v___f_525_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_526_ = lean_apply_4(v_map_524_, lean_box(0), lean_box(0), v___f_525_, v_t_521_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg___lam__0(lean_object* v_toPure_527_, lean_object* v_00_u03b1_528_, lean_object* v_e_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_apply_2(v_toPure_527_, lean_box(0), v_e_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg(lean_object* v_inst_531_){
_start:
{
lean_object* v_toApplicative_532_; lean_object* v_toPure_533_; lean_object* v___f_534_; 
v_toApplicative_532_ = lean_ctor_get(v_inst_531_, 0);
lean_inc_ref(v_toApplicative_532_);
lean_dec_ref(v_inst_531_);
v_toPure_533_ = lean_ctor_get(v_toApplicative_532_, 1);
lean_inc(v_toPure_533_);
lean_dec_ref(v_toApplicative_532_);
v___f_534_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_534_, 0, v_toPure_533_);
return v___f_534_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept(lean_object* v_00_u03b5_535_, lean_object* v_m_536_, lean_object* v_inst_537_){
_start:
{
lean_object* v_toApplicative_538_; lean_object* v_toPure_539_; lean_object* v___f_540_; 
v_toApplicative_538_ = lean_ctor_get(v_inst_537_, 0);
lean_inc_ref(v_toApplicative_538_);
lean_dec_ref(v_inst_537_);
v_toPure_539_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_539_);
lean_dec_ref(v_toApplicative_538_);
v___f_540_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_540_, 0, v_toPure_539_);
return v___f_540_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift___redArg(lean_object* v_inst_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_542_, 0, lean_box(0));
lean_closure_set(v___x_542_, 1, lean_box(0));
lean_closure_set(v___x_542_, 2, v_inst_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift(lean_object* v_00_u03b5_543_, lean_object* v_m_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_546_, 0, lean_box(0));
lean_closure_set(v___x_546_, 1, lean_box(0));
lean_closure_set(v___x_546_, 2, v_inst_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg___lam__0(lean_object* v_handle_547_, lean_object* v_toPure_548_, lean_object* v_res_549_){
_start:
{
if (lean_obj_tag(v_res_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; 
lean_dec(v_toPure_548_);
v_a_550_ = lean_ctor_get(v_res_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v_res_549_, 1);
v___x_551_ = lean_apply_1(v_handle_547_, v_a_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_handle_547_);
v___x_552_ = lean_apply_2(v_toPure_548_, lean_box(0), v_res_549_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg(lean_object* v_inst_553_, lean_object* v_ma_554_, lean_object* v_handle_555_){
_start:
{
lean_object* v_toApplicative_556_; lean_object* v_toBind_557_; lean_object* v_toPure_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v_toApplicative_556_ = lean_ctor_get(v_inst_553_, 0);
lean_inc_ref(v_toApplicative_556_);
v_toBind_557_ = lean_ctor_get(v_inst_553_, 1);
lean_inc(v_toBind_557_);
lean_dec_ref(v_inst_553_);
v_toPure_558_ = lean_ctor_get(v_toApplicative_556_, 1);
lean_inc(v_toPure_558_);
lean_dec_ref(v_toApplicative_556_);
v___f_559_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_559_, 0, v_handle_555_);
lean_closure_set(v___f_559_, 1, v_toPure_558_);
v___x_560_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v_ma_554_, v___f_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object* v_00_u03b5_561_, lean_object* v_m_562_, lean_object* v_inst_563_, lean_object* v_00_u03b1_564_, lean_object* v_ma_565_, lean_object* v_handle_566_){
_start:
{
lean_object* v_toApplicative_567_; lean_object* v_toBind_568_; lean_object* v_toPure_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_toApplicative_567_ = lean_ctor_get(v_inst_563_, 0);
lean_inc_ref(v_toApplicative_567_);
v_toBind_568_ = lean_ctor_get(v_inst_563_, 1);
lean_inc(v_toBind_568_);
lean_dec_ref(v_inst_563_);
v_toPure_569_ = lean_ctor_get(v_toApplicative_567_, 1);
lean_inc(v_toPure_569_);
lean_dec_ref(v_toApplicative_567_);
v___f_570_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_570_, 0, v_handle_566_);
lean_closure_set(v___f_570_, 1, v_toPure_569_);
v___x_571_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v_ma_565_, v___f_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___lam__0(lean_object* v_00_u03b1_572_, lean_object* v_f_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_apply_2(v_f_573_, lean_box(0), v_x_574_);
return v___x_575_;
}
}
lean_object* l_ExceptT_instMonadFunctor___redArg(){
_start:
{
lean_object* v___f_578_; 
v___f_578_ = ((lean_object*)(l_ExceptT_instMonadFunctor___redArg___closed__0));
return v___f_578_;
}
}
LEAN_EXPORT void l_ExceptT_instMonadFunctor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_579_;
v_res_579_ = l_ExceptT_instMonadFunctor___redArg();
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___boxed(lean_object* v___dummy_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_ExceptT_instMonadFunctor___redArg();
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor(lean_object* v_00_u03b5_582_, lean_object* v_m_583_){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = ((lean_object*)(l_ExceptT_instMonadFunctor___redArg___closed__0));
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__0(lean_object* v_toPure_585_, lean_object* v___y_586_, lean_object* v_a_587_){
_start:
{
if (lean_obj_tag(v_a_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___y_586_);
v_a_588_ = lean_ctor_get(v_a_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_a_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v_a_587_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v_a_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_apply_2(v_toPure_585_, lean_box(0), v___x_593_);
return v___x_594_;
}
}
}
else
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_isSharedCheck_604_ = !lean_is_exclusive(v_a_587_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v_a_587_, 0);
lean_dec(v_unused_605_);
v___x_598_ = v_a_587_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_dec(v_a_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___y_586_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___y_586_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_apply_2(v_toPure_585_, lean_box(0), v___x_601_);
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object* v_inst_606_, lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_toApplicative_611_; lean_object* v_toBind_612_; lean_object* v_toPure_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v_toApplicative_611_ = lean_ctor_get(v_inst_606_, 0);
lean_inc_ref(v_toApplicative_611_);
v_toBind_612_ = lean_ctor_get(v_inst_606_, 1);
lean_inc(v_toBind_612_);
lean_dec_ref(v_inst_606_);
v_toPure_613_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_inc(v_toPure_613_);
lean_dec_ref(v_toApplicative_611_);
v___f_614_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_614_, 0, v_toPure_613_);
lean_closure_set(v___f_614_, 1, v___y_609_);
v___x_615_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___y_610_, v___f_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__2(lean_object* v_toPure_616_, lean_object* v_y_617_, lean_object* v_a_618_){
_start:
{
if (lean_obj_tag(v_a_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_y_617_);
v_a_619_ = lean_ctor_get(v_a_618_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_627_ == 0)
{
v___x_621_ = v_a_618_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v_a_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_apply_2(v_toPure_616_, lean_box(0), v___x_624_);
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_637_; 
v_a_628_ = lean_ctor_get(v_a_618_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_637_ == 0)
{
v___x_630_ = v_a_618_;
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v_a_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_apply_1(v_y_617_, v_a_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_636_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_apply_2(v_toPure_616_, lean_box(0), v___x_634_);
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__3(lean_object* v_toApplicative_638_, lean_object* v_x_639_, lean_object* v_toBind_640_, lean_object* v_y_641_){
_start:
{
lean_object* v_toPure_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; 
v_toPure_642_ = lean_ctor_get(v_toApplicative_638_, 1);
lean_inc(v_toPure_642_);
lean_dec_ref(v_toApplicative_638_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_apply_1(v_x_639_, v___x_643_);
v___f_645_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_645_, 0, v_toPure_642_);
lean_closure_set(v___f_645_, 1, v_y_641_);
v___x_646_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_644_, v___f_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object* v_inst_647_, lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_f_650_, lean_object* v_x_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_647_, 0);
v_toBind_653_ = lean_ctor_get(v_inst_647_, 1);
lean_inc_n(v_toBind_653_, 2);
lean_inc_ref(v_toApplicative_652_);
v___f_654_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_654_, 0, v_toApplicative_652_);
lean_closure_set(v___f_654_, 1, v_x_651_);
lean_closure_set(v___f_654_, 2, v_toBind_653_);
v___x_655_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_655_, 0, lean_box(0));
lean_closure_set(v___x_655_, 1, lean_box(0));
lean_closure_set(v___x_655_, 2, v_inst_647_);
lean_closure_set(v___x_655_, 3, lean_box(0));
lean_closure_set(v___x_655_, 4, lean_box(0));
lean_closure_set(v___x_655_, 5, v___f_654_);
v___x_656_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v_f_650_, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5(lean_object* v_toApplicative_657_, lean_object* v_a_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_toPure_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_toPure_660_ = lean_ctor_get(v_toApplicative_657_, 1);
lean_inc(v_toPure_660_);
lean_dec_ref(v_toApplicative_657_);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_a_658_);
v___x_662_ = lean_apply_2(v_toPure_660_, lean_box(0), v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5___boxed(lean_object* v_toApplicative_663_, lean_object* v_a_664_, lean_object* v_x_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_ExceptT_instMonad___redArg___lam__5(v_toApplicative_663_, v_a_664_, v_x_665_);
lean_dec(v_x_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__6(lean_object* v_toApplicative_667_, lean_object* v_y_668_, lean_object* v_inst_669_, lean_object* v_toBind_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___f_672_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_672_, 0, v_toApplicative_667_);
lean_closure_set(v___f_672_, 1, v_a_671_);
v___x_673_ = lean_box(0);
v___x_674_ = lean_apply_1(v_y_668_, v___x_673_);
v___x_675_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_675_, 0, lean_box(0));
lean_closure_set(v___x_675_, 1, lean_box(0));
lean_closure_set(v___x_675_, 2, v_inst_669_);
lean_closure_set(v___x_675_, 3, lean_box(0));
lean_closure_set(v___x_675_, 4, lean_box(0));
lean_closure_set(v___x_675_, 5, v___f_672_);
v___x_676_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_674_, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object* v_inst_677_, lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_y_681_){
_start:
{
lean_object* v_toApplicative_682_; lean_object* v_toBind_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_toApplicative_682_ = lean_ctor_get(v_inst_677_, 0);
v_toBind_683_ = lean_ctor_get(v_inst_677_, 1);
lean_inc_n(v_toBind_683_, 2);
lean_inc_ref(v_inst_677_);
lean_inc_ref(v_toApplicative_682_);
v___f_684_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__6), 5, 4);
lean_closure_set(v___f_684_, 0, v_toApplicative_682_);
lean_closure_set(v___f_684_, 1, v_y_681_);
lean_closure_set(v___f_684_, 2, v_inst_677_);
lean_closure_set(v___f_684_, 3, v_toBind_683_);
v___x_685_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_685_, 0, lean_box(0));
lean_closure_set(v___x_685_, 1, lean_box(0));
lean_closure_set(v___x_685_, 2, v_inst_677_);
lean_closure_set(v___x_685_, 3, lean_box(0));
lean_closure_set(v___x_685_, 4, lean_box(0));
lean_closure_set(v___x_685_, 5, v___f_684_);
v___x_686_ = lean_apply_4(v_toBind_683_, lean_box(0), lean_box(0), v_x_680_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8(lean_object* v_y_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_apply_1(v_y_687_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8___boxed(lean_object* v_y_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_ExceptT_instMonad___redArg___lam__8(v_y_691_, v_x_692_);
lean_dec(v_x_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object* v_inst_694_, lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_y_698_){
_start:
{
lean_object* v_toBind_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_toBind_699_ = lean_ctor_get(v_inst_694_, 1);
lean_inc(v_toBind_699_);
v___f_700_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_700_, 0, v_y_698_);
v___x_701_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_701_, 0, lean_box(0));
lean_closure_set(v___x_701_, 1, lean_box(0));
lean_closure_set(v___x_701_, 2, v_inst_694_);
lean_closure_set(v___x_701_, 3, lean_box(0));
lean_closure_set(v___x_701_, 4, lean_box(0));
lean_closure_set(v___x_701_, 5, v___f_700_);
v___x_702_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v_x_697_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg(lean_object* v_inst_703_){
_start:
{
lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc_ref_n(v_inst_703_, 6);
v___f_704_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_704_, 0, v_inst_703_);
v___f_705_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_705_, 0, v_inst_703_);
v___f_706_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_706_, 0, v_inst_703_);
v___f_707_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_707_, 0, v_inst_703_);
v___x_708_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, lean_box(0));
lean_closure_set(v___x_708_, 2, v_inst_703_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___f_704_);
v___x_710_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_710_, 0, lean_box(0));
lean_closure_set(v___x_710_, 1, lean_box(0));
lean_closure_set(v___x_710_, 2, v_inst_703_);
v___x_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_ctor_set(v___x_711_, 2, v___f_705_);
lean_ctor_set(v___x_711_, 3, v___f_706_);
lean_ctor_set(v___x_711_, 4, v___f_707_);
v___x_712_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_712_, 0, lean_box(0));
lean_closure_set(v___x_712_, 1, lean_box(0));
lean_closure_set(v___x_712_, 2, v_inst_703_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad(lean_object* v_00_u03b5_714_, lean_object* v_m_715_, lean_object* v_inst_716_){
_start:
{
lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref_n(v_inst_716_, 6);
v___f_717_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_717_, 0, v_inst_716_);
v___f_718_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_718_, 0, v_inst_716_);
v___f_719_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_719_, 0, v_inst_716_);
v___f_720_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_720_, 0, v_inst_716_);
v___x_721_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_721_, 0, lean_box(0));
lean_closure_set(v___x_721_, 1, lean_box(0));
lean_closure_set(v___x_721_, 2, v_inst_716_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___f_717_);
v___x_723_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_723_, 0, lean_box(0));
lean_closure_set(v___x_723_, 1, lean_box(0));
lean_closure_set(v___x_723_, 2, v_inst_716_);
v___x_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
lean_ctor_set(v___x_724_, 2, v___f_718_);
lean_ctor_set(v___x_724_, 3, v___f_719_);
lean_ctor_set(v___x_724_, 4, v___f_720_);
v___x_725_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_725_, 0, lean_box(0));
lean_closure_set(v___x_725_, 1, lean_box(0));
lean_closure_set(v___x_725_, 2, v_inst_716_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt___redArg(lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_x_729_){
_start:
{
lean_object* v_toApplicative_730_; lean_object* v_toFunctor_731_; lean_object* v_map_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_toApplicative_730_ = lean_ctor_get(v_inst_727_, 0);
lean_inc_ref(v_toApplicative_730_);
lean_dec_ref(v_inst_727_);
v_toFunctor_731_ = lean_ctor_get(v_toApplicative_730_, 0);
lean_inc_ref(v_toFunctor_731_);
lean_dec_ref(v_toApplicative_730_);
v_map_732_ = lean_ctor_get(v_toFunctor_731_, 0);
lean_inc(v_map_732_);
lean_dec_ref(v_toFunctor_731_);
v___x_733_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_733_, 0, lean_box(0));
lean_closure_set(v___x_733_, 1, lean_box(0));
lean_closure_set(v___x_733_, 2, lean_box(0));
lean_closure_set(v___x_733_, 3, v_f_728_);
v___x_734_ = lean_apply_4(v_map_732_, lean_box(0), lean_box(0), v___x_733_, v_x_729_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object* v_00_u03b5_735_, lean_object* v_m_736_, lean_object* v_inst_737_, lean_object* v_00_u03b5_x27_738_, lean_object* v_00_u03b1_739_, lean_object* v_f_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_toApplicative_742_; lean_object* v_toFunctor_743_; lean_object* v_map_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_toApplicative_742_ = lean_ctor_get(v_inst_737_, 0);
lean_inc_ref(v_toApplicative_742_);
lean_dec_ref(v_inst_737_);
v_toFunctor_743_ = lean_ctor_get(v_toApplicative_742_, 0);
lean_inc_ref(v_toFunctor_743_);
lean_dec_ref(v_toApplicative_742_);
v_map_744_ = lean_ctor_get(v_toFunctor_743_, 0);
lean_inc(v_map_744_);
lean_dec_ref(v_toFunctor_743_);
v___x_745_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, lean_box(0));
lean_closure_set(v___x_745_, 2, lean_box(0));
lean_closure_set(v___x_745_, 3, v_f_740_);
v___x_746_ = lean_apply_4(v_map_744_, lean_box(0), lean_box(0), v___x_745_, v_x_741_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__0(lean_object* v_inst_747_, lean_object* v_00_u03b1_748_, lean_object* v_e_749_){
_start:
{
lean_object* v_throw_750_; lean_object* v___x_751_; 
v_throw_750_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_throw_750_);
lean_dec_ref(v_inst_747_);
v___x_751_ = lean_apply_2(v_throw_750_, lean_box(0), v_e_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__1(lean_object* v_inst_752_, lean_object* v_00_u03b1_753_, lean_object* v_x_754_, lean_object* v_handle_755_){
_start:
{
lean_object* v_tryCatch_756_; lean_object* v___x_757_; 
v_tryCatch_756_ = lean_ctor_get(v_inst_752_, 1);
lean_inc(v_tryCatch_756_);
lean_dec_ref(v_inst_752_);
v___x_757_ = lean_apply_3(v_tryCatch_756_, lean_box(0), v_x_754_, v_handle_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg(lean_object* v_inst_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; 
lean_inc_ref(v_inst_758_);
v___f_759_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_759_, 0, v_inst_758_);
v___f_760_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_760_, 0, v_inst_758_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___f_759_);
lean_ctor_set(v___x_761_, 1, v___f_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object* v_m_762_, lean_object* v_00_u03b5_u2081_763_, lean_object* v_00_u03b5_u2082_764_, lean_object* v_inst_765_){
_start:
{
lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
lean_inc_ref(v_inst_765_);
v___f_766_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_766_, 0, v_inst_765_);
v___f_767_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_767_, 0, v_inst_765_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___f_766_);
lean_ctor_set(v___x_768_, 1, v___f_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object* v_toPure_769_, lean_object* v_00_u03b1_770_, lean_object* v_e_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_e_771_);
v___x_773_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg(lean_object* v_inst_774_){
_start:
{
lean_object* v_toApplicative_775_; lean_object* v_toPure_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_toApplicative_775_ = lean_ctor_get(v_inst_774_, 0);
v_toPure_776_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_776_);
v___f_777_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_777_, 0, v_toPure_776_);
v___x_778_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_778_, 0, lean_box(0));
lean_closure_set(v___x_778_, 1, lean_box(0));
lean_closure_set(v___x_778_, 2, v_inst_774_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___f_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad(lean_object* v_m_780_, lean_object* v_00_u03b5_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v_toApplicative_783_; lean_object* v_toPure_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_toApplicative_783_ = lean_ctor_get(v_inst_782_, 0);
v_toPure_784_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_inc(v_toPure_784_);
v___f_785_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_785_, 0, v_toPure_784_);
v___x_786_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_786_, 0, lean_box(0));
lean_closure_set(v___x_786_, 1, lean_box(0));
lean_closure_set(v___x_786_, 2, v_inst_782_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___f_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad___redArg(lean_object* v_inst_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v_toApplicative_790_; lean_object* v_toPure_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_toApplicative_790_ = lean_ctor_get(v_inst_788_, 0);
lean_inc_ref(v_toApplicative_790_);
lean_dec_ref(v_inst_788_);
v_toPure_791_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_inc(v_toPure_791_);
lean_dec_ref(v_toApplicative_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_inst_789_);
v___x_793_ = lean_apply_2(v_toPure_791_, lean_box(0), v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad(lean_object* v_m_794_, lean_object* v_00_u03b5_795_, lean_object* v_00_u03b1_796_, lean_object* v_inst_797_, lean_object* v_inst_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_instInhabitedExceptTOfMonad___redArg(v_inst_797_, v_inst_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___lam__0(lean_object* v_00_u03b1_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___y_801_);
return v___x_802_;
}
}
lean_object* l_instMonadExceptOfExcept___redArg(){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = ((lean_object*)(l_instMonadExceptOfExcept___redArg___closed__2));
return v___x_809_;
}
}
LEAN_EXPORT void l_instMonadExceptOfExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_810_;
v_res_810_ = l_instMonadExceptOfExcept___redArg();
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___boxed(lean_object* v___dummy_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_instMonadExceptOfExcept___redArg();
return v_res_812_;
}
}
static lean_object* _init_l_instMonadExceptOfExcept___closed__0(void){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_instMonadExceptOfExcept___redArg();
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object* v_00_u03b5_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_instMonadExceptOfExcept___closed__0, &l_instMonadExceptOfExcept___closed__0_once, _init_l_instMonadExceptOfExcept___closed__0);
return v___x_815_;
}
}
lean_object* l_MonadExcept_orelse_x27___redArg___lam__0(uint8_t v_useFirstEx_816_, lean_object* v_throw_817_, lean_object* v_e_u2081_818_, lean_object* v_e_u2082_819_){
_start:
{
if (v_useFirstEx_816_ == 0)
{
lean_object* v___x_820_; 
lean_dec(v_e_u2081_818_);
v___x_820_ = lean_apply_2(v_throw_817_, lean_box(0), v_e_u2082_819_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
lean_dec(v_e_u2082_819_);
v___x_821_ = lean_apply_2(v_throw_817_, lean_box(0), v_e_u2081_818_);
return v___x_821_;
}
}
}
LEAN_EXPORT void l_MonadExcept_orelse_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_useFirstEx_816_ = stack[0].m_num;
lean_object* v_throw_817_ = stack[1].m_obj;
lean_object* v_e_u2081_818_ = stack[2].m_obj;
lean_object* v_e_u2082_819_ = stack[3].m_obj;
lean_object* v_res_822_;
v_res_822_ = l_MonadExcept_orelse_x27___redArg___lam__0(v_useFirstEx_816_, v_throw_817_, v_e_u2081_818_, v_e_u2082_819_);
stack->m_obj
 = v_res_822_;
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0___boxed(lean_object* v_useFirstEx_823_, lean_object* v_throw_824_, lean_object* v_e_u2081_825_, lean_object* v_e_u2082_826_){
_start:
{
uint8_t v_useFirstEx_boxed_827_; lean_object* v_res_828_; 
v_useFirstEx_boxed_827_ = lean_unbox(v_useFirstEx_823_);
v_res_828_ = l_MonadExcept_orelse_x27___redArg___lam__0(v_useFirstEx_boxed_827_, v_throw_824_, v_e_u2081_825_, v_e_u2082_826_);
return v_res_828_;
}
}
lean_object* l_MonadExcept_orelse_x27___redArg___lam__1(uint8_t v_useFirstEx_829_, lean_object* v_throw_830_, lean_object* v_tryCatch_831_, lean_object* v_t_u2082_832_, lean_object* v_e_u2081_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
v___x_834_ = lean_box(v_useFirstEx_829_);
v___f_835_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_835_, 0, v___x_834_);
lean_closure_set(v___f_835_, 1, v_throw_830_);
lean_closure_set(v___f_835_, 2, v_e_u2081_833_);
v___x_836_ = lean_apply_3(v_tryCatch_831_, lean_box(0), v_t_u2082_832_, v___f_835_);
return v___x_836_;
}
}
LEAN_EXPORT void l_MonadExcept_orelse_x27___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_useFirstEx_829_ = stack[0].m_num;
lean_object* v_throw_830_ = stack[1].m_obj;
lean_object* v_tryCatch_831_ = stack[2].m_obj;
lean_object* v_t_u2082_832_ = stack[3].m_obj;
lean_object* v_e_u2081_833_ = stack[4].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_MonadExcept_orelse_x27___redArg___lam__1(v_useFirstEx_829_, v_throw_830_, v_tryCatch_831_, v_t_u2082_832_, v_e_u2081_833_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1___boxed(lean_object* v_useFirstEx_838_, lean_object* v_throw_839_, lean_object* v_tryCatch_840_, lean_object* v_t_u2082_841_, lean_object* v_e_u2081_842_){
_start:
{
uint8_t v_useFirstEx_boxed_843_; lean_object* v_res_844_; 
v_useFirstEx_boxed_843_ = lean_unbox(v_useFirstEx_838_);
v_res_844_ = l_MonadExcept_orelse_x27___redArg___lam__1(v_useFirstEx_boxed_843_, v_throw_839_, v_tryCatch_840_, v_t_u2082_841_, v_e_u2081_842_);
return v_res_844_;
}
}
lean_object* l_MonadExcept_orelse_x27___redArg(lean_object* v_inst_845_, lean_object* v_t_u2081_846_, lean_object* v_t_u2082_847_, uint8_t v_useFirstEx_848_){
_start:
{
lean_object* v_throw_849_; lean_object* v_tryCatch_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___x_853_; 
v_throw_849_ = lean_ctor_get(v_inst_845_, 0);
lean_inc(v_throw_849_);
v_tryCatch_850_ = lean_ctor_get(v_inst_845_, 1);
lean_inc_n(v_tryCatch_850_, 2);
lean_dec_ref(v_inst_845_);
v___x_851_ = lean_box(v_useFirstEx_848_);
v___f_852_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_852_, 0, v___x_851_);
lean_closure_set(v___f_852_, 1, v_throw_849_);
lean_closure_set(v___f_852_, 2, v_tryCatch_850_);
lean_closure_set(v___f_852_, 3, v_t_u2082_847_);
v___x_853_ = lean_apply_3(v_tryCatch_850_, lean_box(0), v_t_u2081_846_, v___f_852_);
return v___x_853_;
}
}
LEAN_EXPORT void l_MonadExcept_orelse_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_845_ = stack[0].m_obj;
lean_object* v_t_u2081_846_ = stack[1].m_obj;
lean_object* v_t_u2082_847_ = stack[2].m_obj;
uint8_t v_useFirstEx_848_ = stack[3].m_num;
lean_object* v_res_854_;
v_res_854_ = l_MonadExcept_orelse_x27___redArg(v_inst_845_, v_t_u2081_846_, v_t_u2082_847_, v_useFirstEx_848_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___boxed(lean_object* v_inst_855_, lean_object* v_t_u2081_856_, lean_object* v_t_u2082_857_, lean_object* v_useFirstEx_858_){
_start:
{
uint8_t v_useFirstEx_boxed_859_; lean_object* v_res_860_; 
v_useFirstEx_boxed_859_ = lean_unbox(v_useFirstEx_858_);
v_res_860_ = l_MonadExcept_orelse_x27___redArg(v_inst_855_, v_t_u2081_856_, v_t_u2082_857_, v_useFirstEx_boxed_859_);
return v_res_860_;
}
}
lean_object* l_MonadExcept_orelse_x27(lean_object* v_00_u03b5_861_, lean_object* v_m_862_, lean_object* v_inst_863_, lean_object* v_00_u03b1_864_, lean_object* v_t_u2081_865_, lean_object* v_t_u2082_866_, uint8_t v_useFirstEx_867_){
_start:
{
lean_object* v_throw_868_; lean_object* v_tryCatch_869_; lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; 
v_throw_868_ = lean_ctor_get(v_inst_863_, 0);
lean_inc(v_throw_868_);
v_tryCatch_869_ = lean_ctor_get(v_inst_863_, 1);
lean_inc_n(v_tryCatch_869_, 2);
lean_dec_ref(v_inst_863_);
v___x_870_ = lean_box(v_useFirstEx_867_);
v___f_871_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_871_, 0, v___x_870_);
lean_closure_set(v___f_871_, 1, v_throw_868_);
lean_closure_set(v___f_871_, 2, v_tryCatch_869_);
lean_closure_set(v___f_871_, 3, v_t_u2082_866_);
v___x_872_ = lean_apply_3(v_tryCatch_869_, lean_box(0), v_t_u2081_865_, v___f_871_);
return v___x_872_;
}
}
LEAN_EXPORT void l_MonadExcept_orelse_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_863_ = stack[2].m_obj;
lean_object* v_t_u2081_865_ = stack[4].m_obj;
lean_object* v_t_u2082_866_ = stack[5].m_obj;
uint8_t v_useFirstEx_867_ = stack[6].m_num;
lean_object* v_res_873_;
v_res_873_ = l_MonadExcept_orelse_x27(lean_box(0), lean_box(0), v_inst_863_, lean_box(0), v_t_u2081_865_, v_t_u2082_866_, v_useFirstEx_867_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___boxed(lean_object* v_00_u03b5_874_, lean_object* v_m_875_, lean_object* v_inst_876_, lean_object* v_00_u03b1_877_, lean_object* v_t_u2081_878_, lean_object* v_t_u2082_879_, lean_object* v_useFirstEx_880_){
_start:
{
uint8_t v_useFirstEx_boxed_881_; lean_object* v_res_882_; 
v_useFirstEx_boxed_881_ = lean_unbox(v_useFirstEx_880_);
v_res_882_ = l_MonadExcept_orelse_x27(v_00_u03b5_874_, v_m_875_, v_inst_876_, v_00_u03b1_877_, v_t_u2081_878_, v_t_u2082_879_, v_useFirstEx_boxed_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__0(lean_object* v_toPure_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_a_884_);
v___x_886_ = lean_apply_2(v_toPure_883_, lean_box(0), v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__1(lean_object* v_toPure_887_, lean_object* v_ex_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_ex_888_);
v___x_890_ = lean_apply_2(v_toPure_887_, lean_box(0), v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg(lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_x_893_){
_start:
{
lean_object* v_toApplicative_894_; lean_object* v_tryCatch_895_; lean_object* v_toBind_896_; lean_object* v_toPure_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_toApplicative_894_ = lean_ctor_get(v_inst_891_, 0);
lean_inc_ref(v_toApplicative_894_);
v_tryCatch_895_ = lean_ctor_get(v_inst_892_, 1);
lean_inc(v_tryCatch_895_);
lean_dec_ref(v_inst_892_);
v_toBind_896_ = lean_ctor_get(v_inst_891_, 1);
lean_inc(v_toBind_896_);
lean_dec_ref(v_inst_891_);
v_toPure_897_ = lean_ctor_get(v_toApplicative_894_, 1);
lean_inc_n(v_toPure_897_, 2);
lean_dec_ref(v_toApplicative_894_);
v___f_898_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_898_, 0, v_toPure_897_);
v___f_899_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_899_, 0, v_toPure_897_);
v___x_900_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v_x_893_, v___f_898_);
v___x_901_ = lean_apply_3(v_tryCatch_895_, lean_box(0), v___x_900_, v___f_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_observing(lean_object* v_00_u03b5_902_, lean_object* v_00_u03b1_903_, lean_object* v_m_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_toApplicative_908_; lean_object* v_tryCatch_909_; lean_object* v_toBind_910_; lean_object* v_toPure_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_toApplicative_908_ = lean_ctor_get(v_inst_905_, 0);
lean_inc_ref(v_toApplicative_908_);
v_tryCatch_909_ = lean_ctor_get(v_inst_906_, 1);
lean_inc(v_tryCatch_909_);
lean_dec_ref(v_inst_906_);
v_toBind_910_ = lean_ctor_get(v_inst_905_, 1);
lean_inc(v_toBind_910_);
lean_dec_ref(v_inst_905_);
v_toPure_911_ = lean_ctor_get(v_toApplicative_908_, 1);
lean_inc_n(v_toPure_911_, 2);
lean_dec_ref(v_toApplicative_908_);
v___f_912_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_912_, 0, v_toPure_911_);
v___f_913_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_913_, 0, v_toPure_911_);
v___x_914_ = lean_apply_4(v_toBind_910_, lean_box(0), lean_box(0), v_x_907_, v___f_912_);
v___x_915_ = lean_apply_3(v_tryCatch_909_, lean_box(0), v___x_914_, v___f_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___redArg(lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_throw_920_; lean_object* v___x_921_; 
lean_dec(v_inst_917_);
v_a_919_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v_x_918_, 1);
v_throw_920_ = lean_ctor_get(v_inst_916_, 0);
lean_inc(v_throw_920_);
lean_dec_ref(v_inst_916_);
v___x_921_ = lean_apply_2(v_throw_920_, lean_box(0), v_a_919_);
return v___x_921_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; 
lean_dec_ref(v_inst_916_);
v_a_922_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v_x_918_, 1);
v___x_923_ = lean_apply_2(v_inst_917_, lean_box(0), v_a_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept(lean_object* v_00_u03b5_924_, lean_object* v_m_925_, lean_object* v_00_u03b1_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_x_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_liftExcept___redArg(v_inst_927_, v_inst_928_, v_x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_931_, lean_object* v_x_932_){
_start:
{
lean_inc(v_x_932_);
return v_x_932_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_instMonadControlExceptTOfMonad___redArg___lam__0(v_00_u03b2_933_, v_x_934_);
lean_dec(v_x_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__2(lean_object* v_inst_936_, lean_object* v___f_937_, lean_object* v___f_938_, lean_object* v_00_u03b1_939_, lean_object* v_f_940_){
_start:
{
lean_object* v_toApplicative_941_; lean_object* v_toFunctor_942_; lean_object* v_map_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_toApplicative_941_ = lean_ctor_get(v_inst_936_, 0);
lean_inc_ref(v_toApplicative_941_);
lean_dec_ref(v_inst_936_);
v_toFunctor_942_ = lean_ctor_get(v_toApplicative_941_, 0);
lean_inc_ref(v_toFunctor_942_);
lean_dec_ref(v_toApplicative_941_);
v_map_943_ = lean_ctor_get(v_toFunctor_942_, 0);
lean_inc(v_map_943_);
lean_dec_ref(v_toFunctor_942_);
v___x_944_ = lean_apply_1(v_f_940_, v___f_937_);
v___x_945_ = lean_apply_4(v_map_943_, lean_box(0), lean_box(0), v___f_938_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_946_, lean_object* v_x_947_){
_start:
{
lean_inc(v_x_947_);
return v_x_947_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_948_, lean_object* v_x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_instMonadControlExceptTOfMonad___redArg___lam__1(v_00_u03b1_948_, v_x_949_);
lean_dec(v_x_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg(lean_object* v_inst_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v___f_954_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__0));
v___f_955_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___f_956_ = lean_alloc_closure((void*)(l_instMonadControlExceptTOfMonad___redArg___lam__2), 5, 3);
lean_closure_set(v___f_956_, 0, v_inst_953_);
lean_closure_set(v___f_956_, 1, v___f_954_);
lean_closure_set(v___f_956_, 2, v___f_955_);
v___f_957_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__1));
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___f_956_);
lean_ctor_set(v___x_958_, 1, v___f_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad(lean_object* v_00_u03b5_959_, lean_object* v_m_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_instMonadControlExceptTOfMonad___redArg(v_inst_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0(lean_object* v_finalizer_963_, lean_object* v_x_964_){
_start:
{
lean_inc(v_finalizer_963_);
return v_finalizer_963_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0___boxed(lean_object* v_finalizer_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_tryFinally___redArg___lam__0(v_finalizer_965_, v_x_966_);
lean_dec(v_x_966_);
lean_dec(v_finalizer_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1(lean_object* v_x_968_){
_start:
{
lean_object* v_fst_969_; 
v_fst_969_ = lean_ctor_get(v_x_968_, 0);
lean_inc(v_fst_969_);
return v_fst_969_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1___boxed(lean_object* v_x_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_tryFinally___redArg___lam__1(v_x_970_);
lean_dec_ref(v_x_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg(lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_x_975_, lean_object* v_finalizer_976_){
_start:
{
lean_object* v_map_977_; lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v_y_980_; lean_object* v___x_981_; 
v_map_977_ = lean_ctor_get(v_inst_974_, 0);
lean_inc(v_map_977_);
lean_dec_ref(v_inst_974_);
v___f_978_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_978_, 0, v_finalizer_976_);
v___f_979_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_980_ = lean_apply_4(v_inst_973_, lean_box(0), lean_box(0), v_x_975_, v___f_978_);
v___x_981_ = lean_apply_4(v_map_977_, lean_box(0), lean_box(0), v___f_979_, v_y_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_tryFinally(lean_object* v_m_982_, lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_x_987_, lean_object* v_finalizer_988_){
_start:
{
lean_object* v_map_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v_y_992_; lean_object* v___x_993_; 
v_map_989_ = lean_ctor_get(v_inst_986_, 0);
lean_inc(v_map_989_);
lean_dec_ref(v_inst_986_);
v___f_990_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_990_, 0, v_finalizer_988_);
v___f_991_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_992_ = lean_apply_4(v_inst_985_, lean_box(0), lean_box(0), v_x_987_, v___f_990_);
v___x_993_ = lean_apply_4(v_map_989_, lean_box(0), lean_box(0), v___f_991_, v_y_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Id_finally___lam__0(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_x_996_, lean_object* v_h_997_){
_start:
{
lean_object* v___x_998_; lean_object* v_b_999_; lean_object* v___x_1000_; 
lean_inc(v_x_996_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_x_996_);
v_b_999_ = lean_apply_1(v_h_997_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_x_996_);
lean_ctor_set(v___x_1000_, 1, v_b_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__0(lean_object* v_toPure_1003_, lean_object* v_r_1004_){
_start:
{
lean_object* v_e_1006_; lean_object* v_fst_1009_; 
v_fst_1009_ = lean_ctor_get(v_r_1004_, 0);
lean_inc(v_fst_1009_);
if (lean_obj_tag(v_fst_1009_) == 0)
{
lean_object* v_snd_1010_; 
v_snd_1010_ = lean_ctor_get(v_r_1004_, 1);
lean_inc(v_snd_1010_);
lean_dec_ref(v_r_1004_);
if (lean_obj_tag(v_snd_1010_) == 0)
{
lean_object* v_a_1011_; 
lean_dec_ref_known(v_fst_1009_, 1);
v_a_1011_ = lean_ctor_get(v_snd_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v_snd_1010_, 1);
v_e_1006_ = v_a_1011_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v_fst_1009_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v_fst_1009_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_snd_1010_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_snd_1010_, 0);
lean_dec(v_unused_1021_);
v___x_1014_ = v_snd_1010_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v_snd_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 0);
lean_ctor_set(v___x_1014_, 0, v_a_1012_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_apply_2(v_toPure_1003_, lean_box(0), v___x_1017_);
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1040_; 
v_snd_1022_ = lean_ctor_get(v_r_1004_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_r_1004_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_r_1004_, 0);
lean_dec(v_unused_1041_);
v___x_1024_ = v_r_1004_;
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_dec(v_r_1004_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1040_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
if (lean_obj_tag(v_snd_1022_) == 0)
{
lean_object* v_a_1026_; 
lean_del_object(v___x_1024_);
lean_dec_ref_known(v_fst_1009_, 1);
v_a_1026_ = lean_ctor_get(v_snd_1022_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_snd_1022_, 1);
v_e_1006_ = v_a_1026_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1039_; 
v_a_1027_ = lean_ctor_get(v_fst_1009_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_fst_1009_, 1);
v_a_1028_ = lean_ctor_get(v_snd_1022_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_snd_1022_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1030_ = v_snd_1022_;
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v_snd_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_a_1028_);
lean_ctor_set(v___x_1024_, 0, v_a_1027_);
v___x_1033_ = v___x_1024_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1027_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_apply_2(v_toPure_1003_, lean_box(0), v___x_1035_);
return v___x_1036_;
}
}
}
}
}
}
v___jp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_e_1006_);
v___x_1008_ = lean_apply_2(v_toPure_1003_, lean_box(0), v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__1(lean_object* v_h_1042_, lean_object* v_e_x3f_1043_){
_start:
{
if (lean_obj_tag(v_e_x3f_1043_) == 0)
{
goto v___jp_1044_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1056_; 
v_val_1047_ = lean_ctor_get(v_e_x3f_1043_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_e_x3f_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1049_ = v_e_x3f_1043_;
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_val_1047_);
lean_dec(v_e_x3f_1043_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
if (lean_obj_tag(v_val_1047_) == 0)
{
lean_dec_ref_known(v_val_1047_, 1);
lean_del_object(v___x_1049_);
goto v___jp_1044_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; 
v_a_1051_ = lean_ctor_get(v_val_1047_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v_val_1047_, 1);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_a_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1051_);
v___x_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_apply_1(v_h_1042_, v___x_1053_);
return v___x_1054_;
}
}
}
}
v___jp_1044_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_apply_1(v_h_1042_, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__2(lean_object* v_inst_1057_, lean_object* v_toBind_1058_, lean_object* v___f_1059_, lean_object* v_00_u03b1_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_x_1062_, lean_object* v_h_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___f_1064_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1064_, 0, v_h_1063_);
v___x_1065_ = lean_apply_4(v_inst_1057_, lean_box(0), lean_box(0), v_x_1062_, v___f_1064_);
v___x_1066_ = lean_apply_4(v_toBind_1058_, lean_box(0), lean_box(0), v___x_1065_, v___f_1059_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg(lean_object* v_inst_1067_, lean_object* v_inst_1068_){
_start:
{
lean_object* v_toApplicative_1069_; lean_object* v_toBind_1070_; lean_object* v_toPure_1071_; lean_object* v___f_1072_; lean_object* v___f_1073_; 
v_toApplicative_1069_ = lean_ctor_get(v_inst_1068_, 0);
lean_inc_ref(v_toApplicative_1069_);
v_toBind_1070_ = lean_ctor_get(v_inst_1068_, 1);
lean_inc(v_toBind_1070_);
lean_dec_ref(v_inst_1068_);
v_toPure_1071_ = lean_ctor_get(v_toApplicative_1069_, 1);
lean_inc(v_toPure_1071_);
lean_dec_ref(v_toApplicative_1069_);
v___f_1072_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1072_, 0, v_toPure_1071_);
v___f_1073_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1073_, 0, v_inst_1067_);
lean_closure_set(v___f_1073_, 1, v_toBind_1070_);
lean_closure_set(v___f_1073_, 2, v___f_1072_);
return v___f_1073_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object* v_m_1074_, lean_object* v_00_u03b5_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v_toApplicative_1078_; lean_object* v_toBind_1079_; lean_object* v_toPure_1080_; lean_object* v___f_1081_; lean_object* v___f_1082_; 
v_toApplicative_1078_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_ref(v_toApplicative_1078_);
v_toBind_1079_ = lean_ctor_get(v_inst_1077_, 1);
lean_inc(v_toBind_1079_);
lean_dec_ref(v_inst_1077_);
v_toPure_1080_ = lean_ctor_get(v_toApplicative_1078_, 1);
lean_inc(v_toPure_1080_);
lean_dec_ref(v_toApplicative_1078_);
v___f_1081_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1081_, 0, v_toPure_1080_);
v___f_1082_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1082_, 0, v_inst_1076_);
lean_closure_set(v___f_1082_, 1, v_toBind_1079_);
lean_closure_set(v___f_1082_, 2, v___f_1081_);
return v___f_1082_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___lam__0(lean_object* v_00_u03b1_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v_x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v_x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v_x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v_x_1084_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v_x_1084_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v_x_1084_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
lean_object* l_instMonadAttachExcept___redArg(){
_start:
{
lean_object* v___f_1103_; 
v___f_1103_ = ((lean_object*)(l_instMonadAttachExcept___redArg___closed__0));
return v___f_1103_;
}
}
LEAN_EXPORT void l_instMonadAttachExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1104_;
v_res_1104_ = l_instMonadAttachExcept___redArg();
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___boxed(lean_object* v___dummy_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_instMonadAttachExcept___redArg();
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept(lean_object* v_00_u03b5_1107_){
_start:
{
lean_object* v___f_1108_; 
v___f_1108_ = ((lean_object*)(l_instMonadAttachExcept___redArg___closed__0));
return v___f_1108_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__0(lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v_x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v_x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v_x_1109_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v_x_1109_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__1(lean_object* v_toFunctor_1126_, lean_object* v_inst_1127_, lean_object* v___f_1128_, lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v_map_1131_; lean_object* v___x_1132_; lean_object* v_this_1133_; 
v_map_1131_ = lean_ctor_get(v_toFunctor_1126_, 0);
lean_inc(v_map_1131_);
lean_dec_ref(v_toFunctor_1126_);
v___x_1132_ = lean_apply_2(v_inst_1127_, lean_box(0), v_x_1130_);
v_this_1133_ = lean_apply_4(v_map_1131_, lean_box(0), lean_box(0), v___f_1128_, v___x_1132_);
return v_this_1133_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg(lean_object* v_inst_1135_, lean_object* v_inst_1136_){
_start:
{
lean_object* v_toApplicative_1137_; lean_object* v_toFunctor_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; 
v_toApplicative_1137_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_ref(v_toApplicative_1137_);
lean_dec_ref(v_inst_1135_);
v_toFunctor_1138_ = lean_ctor_get(v_toApplicative_1137_, 0);
lean_inc_ref(v_toFunctor_1138_);
lean_dec_ref(v_toApplicative_1137_);
v___f_1139_ = ((lean_object*)(l_instMonadAttachExceptTOfMonad___redArg___closed__0));
v___f_1140_ = lean_alloc_closure((void*)(l_instMonadAttachExceptTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1140_, 0, v_toFunctor_1138_);
lean_closure_set(v___f_1140_, 1, v_inst_1136_);
lean_closure_set(v___f_1140_, 2, v___f_1139_);
return v___f_1140_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad(lean_object* v_m_1141_, lean_object* v_00_u03b5_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_instMonadAttachExceptTOfMonad___redArg(v_inst_1143_, v_inst_1144_);
return v___x_1145_;
}
}
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
