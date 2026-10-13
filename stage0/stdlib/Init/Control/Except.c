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
lean_dec_ref_known(v_x_165_, 1);
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
lean_dec_ref_known(v_x_177_, 1);
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
lean_dec_ref_known(v_ma_187_, 1);
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
lean_dec_ref_known(v_ma_193_, 1);
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
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__0(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v___y_216_, lean_object* v___y_217_){
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
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__1(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_f_236_, lean_object* v_x_237_){
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
lean_dec_ref_known(v_f_236_, 1);
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
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_x_268_, lean_object* v_y_269_){
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
lean_dec_ref_known(v___x_271_, 1);
lean_inc_ref(v_x_268_);
return v_x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_x_282_, lean_object* v_y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Except_instMonad___redArg___lam__2(v_00_u03b1_280_, v_00_u03b2_281_, v_x_282_, v_y_283_);
lean_dec_ref(v_x_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___lam__3(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_x_287_, lean_object* v_y_288_){
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
lean_dec_ref_known(v_x_287_, 1);
v___x_297_ = lean_box(0);
v___x_298_ = lean_apply_1(v_y_288_, v___x_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg(){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_Except_instMonad___redArg___closed__9));
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Except_instMonad___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Except_instMonad(lean_object* v_00_u03b5_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Except_instMonad___redArg___closed__9));
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg(lean_object* v_x_324_){
_start:
{
lean_inc(v_x_324_);
return v_x_324_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___redArg___boxed(lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_ExceptT_mk___redArg(v_x_325_);
lean_dec(v_x_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk(lean_object* v_00_u03b5_327_, lean_object* v_m_328_, lean_object* v_00_u03b1_329_, lean_object* v_x_330_){
_start:
{
lean_inc(v_x_330_);
return v_x_330_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_mk___boxed(lean_object* v_00_u03b5_331_, lean_object* v_m_332_, lean_object* v_00_u03b1_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_ExceptT_mk(v_00_u03b5_331_, v_m_332_, v_00_u03b1_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg(lean_object* v_x_336_){
_start:
{
lean_inc(v_x_336_);
return v_x_336_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___redArg___boxed(lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_ExceptT_run___redArg(v_x_337_);
lean_dec(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run(lean_object* v_00_u03b5_339_, lean_object* v_m_340_, lean_object* v_00_u03b1_341_, lean_object* v_x_342_){
_start:
{
lean_inc(v_x_342_);
return v_x_342_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_run___boxed(lean_object* v_00_u03b5_343_, lean_object* v_m_344_, lean_object* v_00_u03b1_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_ExceptT_run(v_00_u03b5_343_, v_m_344_, v_00_u03b1_345_, v_x_346_);
lean_dec(v_x_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg___lam__0(lean_object* v_error_348_, lean_object* v_ok_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; 
lean_dec(v_ok_349_);
v_a_351_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v_x_350_, 1);
v___x_352_ = lean_apply_1(v_error_348_, v_a_351_);
return v___x_352_;
}
else
{
lean_object* v_a_353_; lean_object* v___x_354_; 
lean_dec(v_error_348_);
v_a_353_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v_x_350_, 1);
v___x_354_ = lean_apply_1(v_ok_349_, v_a_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK___redArg(lean_object* v_inst_355_, lean_object* v_x_356_, lean_object* v_ok_357_, lean_object* v_error_358_){
_start:
{
lean_object* v_toBind_359_; lean_object* v___f_360_; lean_object* v___x_361_; 
v_toBind_359_ = lean_ctor_get(v_inst_355_, 1);
lean_inc(v_toBind_359_);
lean_dec_ref(v_inst_355_);
v___f_360_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_360_, 0, v_error_358_);
lean_closure_set(v___f_360_, 1, v_ok_357_);
v___x_361_ = lean_apply_4(v_toBind_359_, lean_box(0), lean_box(0), v_x_356_, v___f_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runK(lean_object* v_m_362_, lean_object* v_00_u03b5_363_, lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_inst_366_, lean_object* v_x_367_, lean_object* v_ok_368_, lean_object* v_error_369_){
_start:
{
lean_object* v_toBind_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
v_toBind_370_ = lean_ctor_get(v_inst_366_, 1);
lean_inc(v_toBind_370_);
lean_dec_ref(v_inst_366_);
v___f_371_ = lean_alloc_closure((void*)(l_ExceptT_runK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_371_, 0, v_error_369_);
lean_closure_set(v___f_371_, 1, v_ok_368_);
v___x_372_ = lean_apply_4(v_toBind_370_, lean_box(0), lean_box(0), v_x_367_, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg___lam__0(lean_object* v_toPure_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v_x_374_);
v___x_376_ = lean_apply_2(v_toPure_373_, lean_box(0), v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch___redArg(lean_object* v_inst_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_toApplicative_379_; lean_object* v_toBind_380_; lean_object* v_toPure_381_; lean_object* v___f_382_; lean_object* v___x_383_; 
v_toApplicative_379_ = lean_ctor_get(v_inst_377_, 0);
lean_inc_ref(v_toApplicative_379_);
v_toBind_380_ = lean_ctor_get(v_inst_377_, 1);
lean_inc(v_toBind_380_);
lean_dec_ref(v_inst_377_);
v_toPure_381_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_381_);
lean_dec_ref(v_toApplicative_379_);
v___f_382_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_382_, 0, v_toPure_381_);
v___x_383_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v_x_378_, v___f_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_runCatch(lean_object* v_m_384_, lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_toApplicative_388_; lean_object* v_toBind_389_; lean_object* v_toPure_390_; lean_object* v___f_391_; lean_object* v___x_392_; 
v_toApplicative_388_ = lean_ctor_get(v_inst_386_, 0);
lean_inc_ref(v_toApplicative_388_);
v_toBind_389_ = lean_ctor_get(v_inst_386_, 1);
lean_inc(v_toBind_389_);
lean_dec_ref(v_inst_386_);
v_toPure_390_ = lean_ctor_get(v_toApplicative_388_, 1);
lean_inc(v_toPure_390_);
lean_dec_ref(v_toApplicative_388_);
v___f_391_ = lean_alloc_closure((void*)(l_ExceptT_runCatch___redArg___lam__0), 2, 1);
lean_closure_set(v___f_391_, 0, v_toPure_390_);
v___x_392_ = lean_apply_4(v_toBind_389_, lean_box(0), lean_box(0), v_x_387_, v___f_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure___redArg(lean_object* v_inst_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_toApplicative_395_; lean_object* v_toPure_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_toApplicative_395_ = lean_ctor_get(v_inst_393_, 0);
lean_inc_ref(v_toApplicative_395_);
lean_dec_ref(v_inst_393_);
v_toPure_396_ = lean_ctor_get(v_toApplicative_395_, 1);
lean_inc(v_toPure_396_);
lean_dec_ref(v_toApplicative_395_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_a_394_);
v___x_398_ = lean_apply_2(v_toPure_396_, lean_box(0), v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_pure(lean_object* v_00_u03b5_399_, lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_00_u03b1_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_toApplicative_404_; lean_object* v_toPure_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_toApplicative_404_ = lean_ctor_get(v_inst_401_, 0);
lean_inc_ref(v_toApplicative_404_);
lean_dec_ref(v_inst_401_);
v_toPure_405_ = lean_ctor_get(v_toApplicative_404_, 1);
lean_inc(v_toPure_405_);
lean_dec_ref(v_toApplicative_404_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_403_);
v___x_407_ = lean_apply_2(v_toPure_405_, lean_box(0), v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___redArg(lean_object* v_inst_408_, lean_object* v_f_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_toApplicative_411_; 
v_toApplicative_411_ = lean_ctor_get(v_inst_408_, 0);
lean_inc_ref(v_toApplicative_411_);
lean_dec_ref(v_inst_408_);
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_toPure_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_f_409_);
v_toPure_412_ = lean_ctor_get(v_toApplicative_411_, 1);
lean_inc(v_toPure_412_);
lean_dec_ref(v_toApplicative_411_);
v_a_413_ = lean_ctor_get(v_x_410_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_apply_2(v_toPure_412_, lean_box(0), v___x_418_);
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_423_; 
lean_dec_ref(v_toApplicative_411_);
v_a_422_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v_x_410_, 1);
v___x_423_ = lean_apply_1(v_f_409_, v_a_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont(lean_object* v_00_u03b5_424_, lean_object* v_m_425_, lean_object* v_inst_426_, lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_f_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_toApplicative_431_; 
v_toApplicative_431_ = lean_ctor_get(v_inst_426_, 0);
lean_inc_ref(v_toApplicative_431_);
lean_dec_ref(v_inst_426_);
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_toPure_432_; lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_f_429_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_431_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_431_);
v_a_433_ = lean_ctor_get(v_x_430_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v_x_430_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v_x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_apply_2(v_toPure_432_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_443_; 
lean_dec_ref(v_toApplicative_431_);
v_a_442_ = lean_ctor_get(v_x_430_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v_x_430_, 1);
v___x_443_ = lean_apply_1(v_f_429_, v_a_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind___redArg(lean_object* v_inst_444_, lean_object* v_ma_445_, lean_object* v_f_446_){
_start:
{
lean_object* v_toBind_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_toBind_447_ = lean_ctor_get(v_inst_444_, 1);
lean_inc(v_toBind_447_);
v___x_448_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_448_, 0, lean_box(0));
lean_closure_set(v___x_448_, 1, lean_box(0));
lean_closure_set(v___x_448_, 2, v_inst_444_);
lean_closure_set(v___x_448_, 3, lean_box(0));
lean_closure_set(v___x_448_, 4, lean_box(0));
lean_closure_set(v___x_448_, 5, v_f_446_);
v___x_449_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v_ma_445_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bind(lean_object* v_00_u03b5_450_, lean_object* v_m_451_, lean_object* v_inst_452_, lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_ma_455_, lean_object* v_f_456_){
_start:
{
lean_object* v_toBind_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_toBind_457_ = lean_ctor_get(v_inst_452_, 1);
lean_inc(v_toBind_457_);
v___x_458_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_458_, 0, lean_box(0));
lean_closure_set(v___x_458_, 1, lean_box(0));
lean_closure_set(v___x_458_, 2, v_inst_452_);
lean_closure_set(v___x_458_, 3, lean_box(0));
lean_closure_set(v___x_458_, 4, lean_box(0));
lean_closure_set(v___x_458_, 5, v_f_456_);
v___x_459_ = lean_apply_4(v_toBind_457_, lean_box(0), lean_box(0), v_ma_455_, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg___lam__0(lean_object* v_toPure_460_, lean_object* v_f_461_, lean_object* v_a_462_){
_start:
{
if (lean_obj_tag(v_a_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_f_461_);
v_a_463_ = lean_ctor_get(v_a_462_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v_a_462_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v_a_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; 
v___x_469_ = lean_apply_2(v_toPure_460_, lean_box(0), v___x_468_);
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_a_472_ = lean_ctor_get(v_a_462_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v_a_462_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v_a_462_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_apply_1(v_f_461_, v_a_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_apply_2(v_toPure_460_, lean_box(0), v___x_478_);
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_map___redArg(lean_object* v_inst_482_, lean_object* v_f_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v_toPure_487_; lean_object* v___f_488_; lean_object* v___x_489_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_482_, 0);
lean_inc_ref(v_toApplicative_485_);
v_toBind_486_ = lean_ctor_get(v_inst_482_, 1);
lean_inc(v_toBind_486_);
lean_dec_ref(v_inst_482_);
v_toPure_487_ = lean_ctor_get(v_toApplicative_485_, 1);
lean_inc(v_toPure_487_);
lean_dec_ref(v_toApplicative_485_);
v___f_488_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_488_, 0, v_toPure_487_);
lean_closure_set(v___f_488_, 1, v_f_483_);
v___x_489_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v_x_484_, v___f_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_map(lean_object* v_00_u03b5_490_, lean_object* v_m_491_, lean_object* v_inst_492_, lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_f_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_toApplicative_497_; lean_object* v_toBind_498_; lean_object* v_toPure_499_; lean_object* v___f_500_; lean_object* v___x_501_; 
v_toApplicative_497_ = lean_ctor_get(v_inst_492_, 0);
lean_inc_ref(v_toApplicative_497_);
v_toBind_498_ = lean_ctor_get(v_inst_492_, 1);
lean_inc(v_toBind_498_);
lean_dec_ref(v_inst_492_);
v_toPure_499_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_inc(v_toPure_499_);
lean_dec_ref(v_toApplicative_497_);
v___f_500_ = lean_alloc_closure((void*)(l_ExceptT_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_500_, 0, v_toPure_499_);
lean_closure_set(v___f_500_, 1, v_f_495_);
v___x_501_ = lean_apply_4(v_toBind_498_, lean_box(0), lean_box(0), v_x_496_, v___f_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg___lam__0(lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift___redArg(lean_object* v_inst_505_, lean_object* v_t_506_){
_start:
{
lean_object* v_toApplicative_507_; lean_object* v_toFunctor_508_; lean_object* v_map_509_; lean_object* v___f_510_; lean_object* v___x_511_; 
v_toApplicative_507_ = lean_ctor_get(v_inst_505_, 0);
lean_inc_ref(v_toApplicative_507_);
lean_dec_ref(v_inst_505_);
v_toFunctor_508_ = lean_ctor_get(v_toApplicative_507_, 0);
lean_inc_ref(v_toFunctor_508_);
lean_dec_ref(v_toApplicative_507_);
v_map_509_ = lean_ctor_get(v_toFunctor_508_, 0);
lean_inc(v_map_509_);
lean_dec_ref(v_toFunctor_508_);
v___f_510_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_511_ = lean_apply_4(v_map_509_, lean_box(0), lean_box(0), v___f_510_, v_t_506_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_lift(lean_object* v_00_u03b5_512_, lean_object* v_m_513_, lean_object* v_inst_514_, lean_object* v_00_u03b1_515_, lean_object* v_t_516_){
_start:
{
lean_object* v_toApplicative_517_; lean_object* v_toFunctor_518_; lean_object* v_map_519_; lean_object* v___f_520_; lean_object* v___x_521_; 
v_toApplicative_517_ = lean_ctor_get(v_inst_514_, 0);
lean_inc_ref(v_toApplicative_517_);
lean_dec_ref(v_inst_514_);
v_toFunctor_518_ = lean_ctor_get(v_toApplicative_517_, 0);
lean_inc_ref(v_toFunctor_518_);
lean_dec_ref(v_toApplicative_517_);
v_map_519_ = lean_ctor_get(v_toFunctor_518_, 0);
lean_inc(v_map_519_);
lean_dec_ref(v_toFunctor_518_);
v___f_520_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___x_521_ = lean_apply_4(v_map_519_, lean_box(0), lean_box(0), v___f_520_, v_t_516_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg___lam__0(lean_object* v_toPure_522_, lean_object* v_00_u03b1_523_, lean_object* v_e_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_apply_2(v_toPure_522_, lean_box(0), v_e_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept___redArg(lean_object* v_inst_526_){
_start:
{
lean_object* v_toApplicative_527_; lean_object* v_toPure_528_; lean_object* v___f_529_; 
v_toApplicative_527_ = lean_ctor_get(v_inst_526_, 0);
lean_inc_ref(v_toApplicative_527_);
lean_dec_ref(v_inst_526_);
v_toPure_528_ = lean_ctor_get(v_toApplicative_527_, 1);
lean_inc(v_toPure_528_);
lean_dec_ref(v_toApplicative_527_);
v___f_529_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_529_, 0, v_toPure_528_);
return v___f_529_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLiftExcept(lean_object* v_00_u03b5_530_, lean_object* v_m_531_, lean_object* v_inst_532_){
_start:
{
lean_object* v_toApplicative_533_; lean_object* v_toPure_534_; lean_object* v___f_535_; 
v_toApplicative_533_ = lean_ctor_get(v_inst_532_, 0);
lean_inc_ref(v_toApplicative_533_);
lean_dec_ref(v_inst_532_);
v_toPure_534_ = lean_ctor_get(v_toApplicative_533_, 1);
lean_inc(v_toPure_534_);
lean_dec_ref(v_toApplicative_533_);
v___f_535_ = lean_alloc_closure((void*)(l_ExceptT_instMonadLiftExcept___redArg___lam__0), 3, 1);
lean_closure_set(v___f_535_, 0, v_toPure_534_);
return v___f_535_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift___redArg(lean_object* v_inst_536_){
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
LEAN_EXPORT lean_object* l_ExceptT_instMonadLift(lean_object* v_00_u03b5_538_, lean_object* v_m_539_, lean_object* v_inst_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_541_, 0, lean_box(0));
lean_closure_set(v___x_541_, 1, lean_box(0));
lean_closure_set(v___x_541_, 2, v_inst_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg___lam__0(lean_object* v_handle_542_, lean_object* v_toPure_543_, lean_object* v_res_544_){
_start:
{
if (lean_obj_tag(v_res_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; 
lean_dec(v_toPure_543_);
v_a_545_ = lean_ctor_get(v_res_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v_res_544_, 1);
v___x_546_ = lean_apply_1(v_handle_542_, v_a_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
lean_dec(v_handle_542_);
v___x_547_ = lean_apply_2(v_toPure_543_, lean_box(0), v_res_544_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch___redArg(lean_object* v_inst_548_, lean_object* v_ma_549_, lean_object* v_handle_550_){
_start:
{
lean_object* v_toApplicative_551_; lean_object* v_toBind_552_; lean_object* v_toPure_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
v_toApplicative_551_ = lean_ctor_get(v_inst_548_, 0);
lean_inc_ref(v_toApplicative_551_);
v_toBind_552_ = lean_ctor_get(v_inst_548_, 1);
lean_inc(v_toBind_552_);
lean_dec_ref(v_inst_548_);
v_toPure_553_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_inc(v_toPure_553_);
lean_dec_ref(v_toApplicative_551_);
v___f_554_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_554_, 0, v_handle_550_);
lean_closure_set(v___f_554_, 1, v_toPure_553_);
v___x_555_ = lean_apply_4(v_toBind_552_, lean_box(0), lean_box(0), v_ma_549_, v___f_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_tryCatch(lean_object* v_00_u03b5_556_, lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_00_u03b1_559_, lean_object* v_ma_560_, lean_object* v_handle_561_){
_start:
{
lean_object* v_toApplicative_562_; lean_object* v_toBind_563_; lean_object* v_toPure_564_; lean_object* v___f_565_; lean_object* v___x_566_; 
v_toApplicative_562_ = lean_ctor_get(v_inst_558_, 0);
lean_inc_ref(v_toApplicative_562_);
v_toBind_563_ = lean_ctor_get(v_inst_558_, 1);
lean_inc(v_toBind_563_);
lean_dec_ref(v_inst_558_);
v_toPure_564_ = lean_ctor_get(v_toApplicative_562_, 1);
lean_inc(v_toPure_564_);
lean_dec_ref(v_toApplicative_562_);
v___f_565_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch___redArg___lam__0), 3, 2);
lean_closure_set(v___f_565_, 0, v_handle_561_);
lean_closure_set(v___f_565_, 1, v_toPure_564_);
v___x_566_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v_ma_560_, v___f_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___lam__0(lean_object* v_00_u03b1_567_, lean_object* v_f_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_apply_2(v_f_568_, lean_box(0), v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg(){
_start:
{
lean_object* v___f_573_; 
v___f_573_ = ((lean_object*)(l_ExceptT_instMonadFunctor___redArg___closed__0));
return v___f_573_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor___redArg___boxed(lean_object* v___dummy_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_ExceptT_instMonadFunctor___redArg();
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonadFunctor(lean_object* v_00_u03b5_576_, lean_object* v_m_577_){
_start:
{
lean_object* v___f_578_; 
v___f_578_ = ((lean_object*)(l_ExceptT_instMonadFunctor___redArg___closed__0));
return v___f_578_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__0(lean_object* v_toPure_579_, lean_object* v___y_580_, lean_object* v_a_581_){
_start:
{
if (lean_obj_tag(v_a_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
lean_dec(v___y_580_);
v_a_582_ = lean_ctor_get(v_a_581_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_a_581_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v_a_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = lean_apply_2(v_toPure_579_, lean_box(0), v___x_587_);
return v___x_588_;
}
}
}
else
{
lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_a_581_, 0);
lean_dec(v_unused_599_);
v___x_592_ = v_a_581_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_dec(v_a_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___y_580_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___y_580_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_apply_2(v_toPure_579_, lean_box(0), v___x_595_);
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object* v_inst_600_, lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_toApplicative_605_; lean_object* v_toBind_606_; lean_object* v_toPure_607_; lean_object* v___f_608_; lean_object* v___x_609_; 
v_toApplicative_605_ = lean_ctor_get(v_inst_600_, 0);
lean_inc_ref(v_toApplicative_605_);
v_toBind_606_ = lean_ctor_get(v_inst_600_, 1);
lean_inc(v_toBind_606_);
lean_dec_ref(v_inst_600_);
v_toPure_607_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc(v_toPure_607_);
lean_dec_ref(v_toApplicative_605_);
v___f_608_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_608_, 0, v_toPure_607_);
lean_closure_set(v___f_608_, 1, v___y_603_);
v___x_609_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v___y_604_, v___f_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__2(lean_object* v_toPure_610_, lean_object* v_y_611_, lean_object* v_a_612_){
_start:
{
if (lean_obj_tag(v_a_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_y_611_);
v_a_613_ = lean_ctor_get(v_a_612_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_621_ == 0)
{
v___x_615_ = v_a_612_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v_a_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_620_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = lean_apply_2(v_toPure_610_, lean_box(0), v___x_618_);
return v___x_619_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_631_; 
v_a_622_ = lean_ctor_get(v_a_612_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_631_ == 0)
{
v___x_624_ = v_a_612_;
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v_a_612_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_apply_1(v_y_611_, v_a_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_apply_2(v_toPure_610_, lean_box(0), v___x_628_);
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__3(lean_object* v_toApplicative_632_, lean_object* v_x_633_, lean_object* v_toBind_634_, lean_object* v_y_635_){
_start:
{
lean_object* v_toPure_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___x_640_; 
v_toPure_636_ = lean_ctor_get(v_toApplicative_632_, 1);
lean_inc(v_toPure_636_);
lean_dec_ref(v_toApplicative_632_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_apply_1(v_x_633_, v___x_637_);
v___f_639_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_639_, 0, v_toPure_636_);
lean_closure_set(v___f_639_, 1, v_y_635_);
v___x_640_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_638_, v___f_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object* v_inst_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_f_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_641_, 0);
v_toBind_647_ = lean_ctor_get(v_inst_641_, 1);
lean_inc_n(v_toBind_647_, 2);
lean_inc_ref(v_toApplicative_646_);
v___f_648_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_648_, 0, v_toApplicative_646_);
lean_closure_set(v___f_648_, 1, v_x_645_);
lean_closure_set(v___f_648_, 2, v_toBind_647_);
v___x_649_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_649_, 0, lean_box(0));
lean_closure_set(v___x_649_, 1, lean_box(0));
lean_closure_set(v___x_649_, 2, v_inst_641_);
lean_closure_set(v___x_649_, 3, lean_box(0));
lean_closure_set(v___x_649_, 4, lean_box(0));
lean_closure_set(v___x_649_, 5, v___f_648_);
v___x_650_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v_f_644_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5(lean_object* v_toApplicative_651_, lean_object* v_a_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_toPure_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toPure_654_ = lean_ctor_get(v_toApplicative_651_, 1);
lean_inc(v_toPure_654_);
lean_dec_ref(v_toApplicative_651_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_a_652_);
v___x_656_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__5___boxed(lean_object* v_toApplicative_657_, lean_object* v_a_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_ExceptT_instMonad___redArg___lam__5(v_toApplicative_657_, v_a_658_, v_x_659_);
lean_dec(v_x_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__6(lean_object* v_toApplicative_661_, lean_object* v_y_662_, lean_object* v_inst_663_, lean_object* v_toBind_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___f_666_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_666_, 0, v_toApplicative_661_);
lean_closure_set(v___f_666_, 1, v_a_665_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_apply_1(v_y_662_, v___x_667_);
v___x_669_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_669_, 0, lean_box(0));
lean_closure_set(v___x_669_, 1, lean_box(0));
lean_closure_set(v___x_669_, 2, v_inst_663_);
lean_closure_set(v___x_669_, 3, lean_box(0));
lean_closure_set(v___x_669_, 4, lean_box(0));
lean_closure_set(v___x_669_, 5, v___f_666_);
v___x_670_ = lean_apply_4(v_toBind_664_, lean_box(0), lean_box(0), v___x_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object* v_inst_671_, lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_x_674_, lean_object* v_y_675_){
_start:
{
lean_object* v_toApplicative_676_; lean_object* v_toBind_677_; lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_toApplicative_676_ = lean_ctor_get(v_inst_671_, 0);
v_toBind_677_ = lean_ctor_get(v_inst_671_, 1);
lean_inc_n(v_toBind_677_, 2);
lean_inc_ref(v_inst_671_);
lean_inc_ref(v_toApplicative_676_);
v___f_678_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__6), 5, 4);
lean_closure_set(v___f_678_, 0, v_toApplicative_676_);
lean_closure_set(v___f_678_, 1, v_y_675_);
lean_closure_set(v___f_678_, 2, v_inst_671_);
lean_closure_set(v___f_678_, 3, v_toBind_677_);
v___x_679_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_679_, 0, lean_box(0));
lean_closure_set(v___x_679_, 1, lean_box(0));
lean_closure_set(v___x_679_, 2, v_inst_671_);
lean_closure_set(v___x_679_, 3, lean_box(0));
lean_closure_set(v___x_679_, 4, lean_box(0));
lean_closure_set(v___x_679_, 5, v___f_678_);
v___x_680_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v_x_674_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8(lean_object* v_y_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_apply_1(v_y_681_, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__8___boxed(lean_object* v_y_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_ExceptT_instMonad___redArg___lam__8(v_y_685_, v_x_686_);
lean_dec(v_x_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object* v_inst_688_, lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_y_692_){
_start:
{
lean_object* v_toBind_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_toBind_693_ = lean_ctor_get(v_inst_688_, 1);
lean_inc(v_toBind_693_);
v___f_694_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_694_, 0, v_y_692_);
v___x_695_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_695_, 0, lean_box(0));
lean_closure_set(v___x_695_, 1, lean_box(0));
lean_closure_set(v___x_695_, 2, v_inst_688_);
lean_closure_set(v___x_695_, 3, lean_box(0));
lean_closure_set(v___x_695_, 4, lean_box(0));
lean_closure_set(v___x_695_, 5, v___f_694_);
v___x_696_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v_x_691_, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad___redArg(lean_object* v_inst_697_){
_start:
{
lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref_n(v_inst_697_, 6);
v___f_698_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_698_, 0, v_inst_697_);
v___f_699_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_699_, 0, v_inst_697_);
v___f_700_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_700_, 0, v_inst_697_);
v___f_701_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_701_, 0, v_inst_697_);
v___x_702_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_702_, 0, lean_box(0));
lean_closure_set(v___x_702_, 1, lean_box(0));
lean_closure_set(v___x_702_, 2, v_inst_697_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___f_698_);
v___x_704_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_704_, 0, lean_box(0));
lean_closure_set(v___x_704_, 1, lean_box(0));
lean_closure_set(v___x_704_, 2, v_inst_697_);
v___x_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_ctor_set(v___x_705_, 2, v___f_699_);
lean_ctor_set(v___x_705_, 3, v___f_700_);
lean_ctor_set(v___x_705_, 4, v___f_701_);
v___x_706_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, lean_box(0));
lean_closure_set(v___x_706_, 2, v_inst_697_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_instMonad(lean_object* v_00_u03b5_708_, lean_object* v_m_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_inc_ref_n(v_inst_710_, 6);
v___f_711_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_711_, 0, v_inst_710_);
v___f_712_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_712_, 0, v_inst_710_);
v___f_713_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_713_, 0, v_inst_710_);
v___f_714_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_714_, 0, v_inst_710_);
v___x_715_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_715_, 0, lean_box(0));
lean_closure_set(v___x_715_, 1, lean_box(0));
lean_closure_set(v___x_715_, 2, v_inst_710_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___f_711_);
v___x_717_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_717_, 0, lean_box(0));
lean_closure_set(v___x_717_, 1, lean_box(0));
lean_closure_set(v___x_717_, 2, v_inst_710_);
v___x_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
lean_ctor_set(v___x_718_, 2, v___f_712_);
lean_ctor_set(v___x_718_, 3, v___f_713_);
lean_ctor_set(v___x_718_, 4, v___f_714_);
v___x_719_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_719_, 0, lean_box(0));
lean_closure_set(v___x_719_, 1, lean_box(0));
lean_closure_set(v___x_719_, 2, v_inst_710_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt___redArg(lean_object* v_inst_721_, lean_object* v_f_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_toApplicative_724_; lean_object* v_toFunctor_725_; lean_object* v_map_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_toApplicative_724_ = lean_ctor_get(v_inst_721_, 0);
lean_inc_ref(v_toApplicative_724_);
lean_dec_ref(v_inst_721_);
v_toFunctor_725_ = lean_ctor_get(v_toApplicative_724_, 0);
lean_inc_ref(v_toFunctor_725_);
lean_dec_ref(v_toApplicative_724_);
v_map_726_ = lean_ctor_get(v_toFunctor_725_, 0);
lean_inc(v_map_726_);
lean_dec_ref(v_toFunctor_725_);
v___x_727_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_727_, 0, lean_box(0));
lean_closure_set(v___x_727_, 1, lean_box(0));
lean_closure_set(v___x_727_, 2, lean_box(0));
lean_closure_set(v___x_727_, 3, v_f_722_);
v___x_728_ = lean_apply_4(v_map_726_, lean_box(0), lean_box(0), v___x_727_, v_x_723_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_adapt(lean_object* v_00_u03b5_729_, lean_object* v_m_730_, lean_object* v_inst_731_, lean_object* v_00_u03b5_x27_732_, lean_object* v_00_u03b1_733_, lean_object* v_f_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_toFunctor_737_; lean_object* v_map_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_731_, 0);
lean_inc_ref(v_toApplicative_736_);
lean_dec_ref(v_inst_731_);
v_toFunctor_737_ = lean_ctor_get(v_toApplicative_736_, 0);
lean_inc_ref(v_toFunctor_737_);
lean_dec_ref(v_toApplicative_736_);
v_map_738_ = lean_ctor_get(v_toFunctor_737_, 0);
lean_inc(v_map_738_);
lean_dec_ref(v_toFunctor_737_);
v___x_739_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_739_, 0, lean_box(0));
lean_closure_set(v___x_739_, 1, lean_box(0));
lean_closure_set(v___x_739_, 2, lean_box(0));
lean_closure_set(v___x_739_, 3, v_f_734_);
v___x_740_ = lean_apply_4(v_map_738_, lean_box(0), lean_box(0), v___x_739_, v_x_735_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__0(lean_object* v_inst_741_, lean_object* v_00_u03b1_742_, lean_object* v_e_743_){
_start:
{
lean_object* v_throw_744_; lean_object* v___x_745_; 
v_throw_744_ = lean_ctor_get(v_inst_741_, 0);
lean_inc(v_throw_744_);
lean_dec_ref(v_inst_741_);
v___x_745_ = lean_apply_2(v_throw_744_, lean_box(0), v_e_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg___lam__1(lean_object* v_inst_746_, lean_object* v_00_u03b1_747_, lean_object* v_x_748_, lean_object* v_handle_749_){
_start:
{
lean_object* v_tryCatch_750_; lean_object* v___x_751_; 
v_tryCatch_750_ = lean_ctor_get(v_inst_746_, 1);
lean_inc(v_tryCatch_750_);
lean_dec_ref(v_inst_746_);
v___x_751_ = lean_apply_3(v_tryCatch_750_, lean_box(0), v_x_748_, v_handle_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT___redArg(lean_object* v_inst_752_){
_start:
{
lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
lean_inc_ref(v_inst_752_);
v___f_753_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_753_, 0, v_inst_752_);
v___f_754_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_754_, 0, v_inst_752_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___f_753_);
lean_ctor_set(v___x_755_, 1, v___f_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptT(lean_object* v_m_756_, lean_object* v_00_u03b5_u2081_757_, lean_object* v_00_u03b5_u2082_758_, lean_object* v_inst_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
lean_inc_ref(v_inst_759_);
v___f_760_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_760_, 0, v_inst_759_);
v___f_761_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_761_, 0, v_inst_759_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___f_760_);
lean_ctor_set(v___x_762_, 1, v___f_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object* v_toPure_763_, lean_object* v_00_u03b1_764_, lean_object* v_e_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_e_765_);
v___x_767_ = lean_apply_2(v_toPure_763_, lean_box(0), v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad___redArg(lean_object* v_inst_768_){
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
LEAN_EXPORT lean_object* l_instMonadExceptOfExceptTOfMonad(lean_object* v_m_774_, lean_object* v_00_u03b5_775_, lean_object* v_inst_776_){
_start:
{
lean_object* v_toApplicative_777_; lean_object* v_toPure_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_toApplicative_777_ = lean_ctor_get(v_inst_776_, 0);
v_toPure_778_ = lean_ctor_get(v_toApplicative_777_, 1);
lean_inc(v_toPure_778_);
v___f_779_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_779_, 0, v_toPure_778_);
v___x_780_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_780_, 0, lean_box(0));
lean_closure_set(v___x_780_, 1, lean_box(0));
lean_closure_set(v___x_780_, 2, v_inst_776_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___f_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad___redArg(lean_object* v_inst_782_, lean_object* v_inst_783_){
_start:
{
lean_object* v_toApplicative_784_; lean_object* v_toPure_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_toApplicative_784_ = lean_ctor_get(v_inst_782_, 0);
lean_inc_ref(v_toApplicative_784_);
lean_dec_ref(v_inst_782_);
v_toPure_785_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_inc(v_toPure_785_);
lean_dec_ref(v_toApplicative_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_inst_783_);
v___x_787_ = lean_apply_2(v_toPure_785_, lean_box(0), v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedExceptTOfMonad(lean_object* v_m_788_, lean_object* v_00_u03b5_789_, lean_object* v_00_u03b1_790_, lean_object* v_inst_791_, lean_object* v_inst_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_instInhabitedExceptTOfMonad___redArg(v_inst_791_, v_inst_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___lam__0(lean_object* v_00_u03b1_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___y_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg(){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = ((lean_object*)(l_instMonadExceptOfExcept___redArg___closed__2));
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept___redArg___boxed(lean_object* v___dummy_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_instMonadExceptOfExcept___redArg();
return v_res_805_;
}
}
static lean_object* _init_l_instMonadExceptOfExcept___closed__0(void){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_instMonadExceptOfExcept___redArg();
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfExcept(lean_object* v_00_u03b5_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_instMonadExceptOfExcept___closed__0, &l_instMonadExceptOfExcept___closed__0_once, _init_l_instMonadExceptOfExcept___closed__0);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0(uint8_t v_useFirstEx_809_, lean_object* v_throw_810_, lean_object* v_e_u2081_811_, lean_object* v_e_u2082_812_){
_start:
{
if (v_useFirstEx_809_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_e_u2081_811_);
v___x_813_ = lean_apply_2(v_throw_810_, lean_box(0), v_e_u2082_812_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; 
lean_dec(v_e_u2082_812_);
v___x_814_ = lean_apply_2(v_throw_810_, lean_box(0), v_e_u2081_811_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__0___boxed(lean_object* v_useFirstEx_815_, lean_object* v_throw_816_, lean_object* v_e_u2081_817_, lean_object* v_e_u2082_818_){
_start:
{
uint8_t v_useFirstEx_boxed_819_; lean_object* v_res_820_; 
v_useFirstEx_boxed_819_ = lean_unbox(v_useFirstEx_815_);
v_res_820_ = l_MonadExcept_orelse_x27___redArg___lam__0(v_useFirstEx_boxed_819_, v_throw_816_, v_e_u2081_817_, v_e_u2082_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1(uint8_t v_useFirstEx_821_, lean_object* v_throw_822_, lean_object* v_tryCatch_823_, lean_object* v_t_u2082_824_, lean_object* v_e_u2081_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___f_827_; lean_object* v___x_828_; 
v___x_826_ = lean_box(v_useFirstEx_821_);
v___f_827_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_827_, 0, v___x_826_);
lean_closure_set(v___f_827_, 1, v_throw_822_);
lean_closure_set(v___f_827_, 2, v_e_u2081_825_);
v___x_828_ = lean_apply_3(v_tryCatch_823_, lean_box(0), v_t_u2082_824_, v___f_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___lam__1___boxed(lean_object* v_useFirstEx_829_, lean_object* v_throw_830_, lean_object* v_tryCatch_831_, lean_object* v_t_u2082_832_, lean_object* v_e_u2081_833_){
_start:
{
uint8_t v_useFirstEx_boxed_834_; lean_object* v_res_835_; 
v_useFirstEx_boxed_834_ = lean_unbox(v_useFirstEx_829_);
v_res_835_ = l_MonadExcept_orelse_x27___redArg___lam__1(v_useFirstEx_boxed_834_, v_throw_830_, v_tryCatch_831_, v_t_u2082_832_, v_e_u2081_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg(lean_object* v_inst_836_, lean_object* v_t_u2081_837_, lean_object* v_t_u2082_838_, uint8_t v_useFirstEx_839_){
_start:
{
lean_object* v_throw_840_; lean_object* v_tryCatch_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; 
v_throw_840_ = lean_ctor_get(v_inst_836_, 0);
lean_inc(v_throw_840_);
v_tryCatch_841_ = lean_ctor_get(v_inst_836_, 1);
lean_inc_n(v_tryCatch_841_, 2);
lean_dec_ref(v_inst_836_);
v___x_842_ = lean_box(v_useFirstEx_839_);
v___f_843_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_843_, 0, v___x_842_);
lean_closure_set(v___f_843_, 1, v_throw_840_);
lean_closure_set(v___f_843_, 2, v_tryCatch_841_);
lean_closure_set(v___f_843_, 3, v_t_u2082_838_);
v___x_844_ = lean_apply_3(v_tryCatch_841_, lean_box(0), v_t_u2081_837_, v___f_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___redArg___boxed(lean_object* v_inst_845_, lean_object* v_t_u2081_846_, lean_object* v_t_u2082_847_, lean_object* v_useFirstEx_848_){
_start:
{
uint8_t v_useFirstEx_boxed_849_; lean_object* v_res_850_; 
v_useFirstEx_boxed_849_ = lean_unbox(v_useFirstEx_848_);
v_res_850_ = l_MonadExcept_orelse_x27___redArg(v_inst_845_, v_t_u2081_846_, v_t_u2082_847_, v_useFirstEx_boxed_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27(lean_object* v_00_u03b5_851_, lean_object* v_m_852_, lean_object* v_inst_853_, lean_object* v_00_u03b1_854_, lean_object* v_t_u2081_855_, lean_object* v_t_u2082_856_, uint8_t v_useFirstEx_857_){
_start:
{
lean_object* v_throw_858_; lean_object* v_tryCatch_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___x_862_; 
v_throw_858_ = lean_ctor_get(v_inst_853_, 0);
lean_inc(v_throw_858_);
v_tryCatch_859_ = lean_ctor_get(v_inst_853_, 1);
lean_inc_n(v_tryCatch_859_, 2);
lean_dec_ref(v_inst_853_);
v___x_860_ = lean_box(v_useFirstEx_857_);
v___f_861_ = lean_alloc_closure((void*)(l_MonadExcept_orelse_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_861_, 0, v___x_860_);
lean_closure_set(v___f_861_, 1, v_throw_858_);
lean_closure_set(v___f_861_, 2, v_tryCatch_859_);
lean_closure_set(v___f_861_, 3, v_t_u2082_856_);
v___x_862_ = lean_apply_3(v_tryCatch_859_, lean_box(0), v_t_u2081_855_, v___f_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orelse_x27___boxed(lean_object* v_00_u03b5_863_, lean_object* v_m_864_, lean_object* v_inst_865_, lean_object* v_00_u03b1_866_, lean_object* v_t_u2081_867_, lean_object* v_t_u2082_868_, lean_object* v_useFirstEx_869_){
_start:
{
uint8_t v_useFirstEx_boxed_870_; lean_object* v_res_871_; 
v_useFirstEx_boxed_870_ = lean_unbox(v_useFirstEx_869_);
v_res_871_ = l_MonadExcept_orelse_x27(v_00_u03b5_863_, v_m_864_, v_inst_865_, v_00_u03b1_866_, v_t_u2081_867_, v_t_u2082_868_, v_useFirstEx_boxed_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__0(lean_object* v_toPure_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v_a_873_);
v___x_875_ = lean_apply_2(v_toPure_872_, lean_box(0), v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg___lam__1(lean_object* v_toPure_876_, lean_object* v_ex_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_ex_877_);
v___x_879_ = lean_apply_2(v_toPure_876_, lean_box(0), v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_observing___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_x_882_){
_start:
{
lean_object* v_toApplicative_883_; lean_object* v_tryCatch_884_; lean_object* v_toBind_885_; lean_object* v_toPure_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_toApplicative_883_ = lean_ctor_get(v_inst_880_, 0);
lean_inc_ref(v_toApplicative_883_);
v_tryCatch_884_ = lean_ctor_get(v_inst_881_, 1);
lean_inc(v_tryCatch_884_);
lean_dec_ref(v_inst_881_);
v_toBind_885_ = lean_ctor_get(v_inst_880_, 1);
lean_inc(v_toBind_885_);
lean_dec_ref(v_inst_880_);
v_toPure_886_ = lean_ctor_get(v_toApplicative_883_, 1);
lean_inc_n(v_toPure_886_, 2);
lean_dec_ref(v_toApplicative_883_);
v___f_887_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_887_, 0, v_toPure_886_);
v___f_888_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_888_, 0, v_toPure_886_);
v___x_889_ = lean_apply_4(v_toBind_885_, lean_box(0), lean_box(0), v_x_882_, v___f_887_);
v___x_890_ = lean_apply_3(v_tryCatch_884_, lean_box(0), v___x_889_, v___f_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_observing(lean_object* v_00_u03b5_891_, lean_object* v_00_u03b1_892_, lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_x_896_){
_start:
{
lean_object* v_toApplicative_897_; lean_object* v_tryCatch_898_; lean_object* v_toBind_899_; lean_object* v_toPure_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_toApplicative_897_ = lean_ctor_get(v_inst_894_, 0);
lean_inc_ref(v_toApplicative_897_);
v_tryCatch_898_ = lean_ctor_get(v_inst_895_, 1);
lean_inc(v_tryCatch_898_);
lean_dec_ref(v_inst_895_);
v_toBind_899_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_toBind_899_);
lean_dec_ref(v_inst_894_);
v_toPure_900_ = lean_ctor_get(v_toApplicative_897_, 1);
lean_inc_n(v_toPure_900_, 2);
lean_dec_ref(v_toApplicative_897_);
v___f_901_ = lean_alloc_closure((void*)(l_observing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_901_, 0, v_toPure_900_);
v___f_902_ = lean_alloc_closure((void*)(l_observing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_902_, 0, v_toPure_900_);
v___x_903_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v_x_896_, v___f_901_);
v___x_904_ = lean_apply_3(v_tryCatch_898_, lean_box(0), v___x_903_, v___f_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___redArg(lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_throw_909_; lean_object* v___x_910_; 
lean_dec(v_inst_906_);
v_a_908_ = lean_ctor_get(v_x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v_x_907_, 1);
v_throw_909_ = lean_ctor_get(v_inst_905_, 0);
lean_inc(v_throw_909_);
lean_dec_ref(v_inst_905_);
v___x_910_ = lean_apply_2(v_throw_909_, lean_box(0), v_a_908_);
return v___x_910_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_912_; 
lean_dec_ref(v_inst_905_);
v_a_911_ = lean_ctor_get(v_x_907_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v_x_907_, 1);
v___x_912_ = lean_apply_2(v_inst_906_, lean_box(0), v_a_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept(lean_object* v_00_u03b5_913_, lean_object* v_m_914_, lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_x_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_liftExcept___redArg(v_inst_916_, v_inst_917_, v_x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0(lean_object* v_00_u03b2_920_, lean_object* v_x_921_){
_start:
{
lean_inc(v_x_921_);
return v_x_921_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b2_922_, lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_instMonadControlExceptTOfMonad___redArg___lam__0(v_00_u03b2_922_, v_x_923_);
lean_dec(v_x_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__2(lean_object* v_inst_925_, lean_object* v___f_926_, lean_object* v___f_927_, lean_object* v_00_u03b1_928_, lean_object* v_f_929_){
_start:
{
lean_object* v_toApplicative_930_; lean_object* v_toFunctor_931_; lean_object* v_map_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_toApplicative_930_ = lean_ctor_get(v_inst_925_, 0);
lean_inc_ref(v_toApplicative_930_);
lean_dec_ref(v_inst_925_);
v_toFunctor_931_ = lean_ctor_get(v_toApplicative_930_, 0);
lean_inc_ref(v_toFunctor_931_);
lean_dec_ref(v_toApplicative_930_);
v_map_932_ = lean_ctor_get(v_toFunctor_931_, 0);
lean_inc(v_map_932_);
lean_dec_ref(v_toFunctor_931_);
v___x_933_ = lean_apply_1(v_f_929_, v___f_926_);
v___x_934_ = lean_apply_4(v_map_932_, lean_box(0), lean_box(0), v___f_927_, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1(lean_object* v_00_u03b1_935_, lean_object* v_x_936_){
_start:
{
lean_inc(v_x_936_);
return v_x_936_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(lean_object* v_00_u03b1_937_, lean_object* v_x_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_instMonadControlExceptTOfMonad___redArg___lam__1(v_00_u03b1_937_, v_x_938_);
lean_dec(v_x_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad___redArg(lean_object* v_inst_942_){
_start:
{
lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___x_947_; 
v___f_943_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__0));
v___f_944_ = ((lean_object*)(l_ExceptT_lift___redArg___closed__0));
v___f_945_ = lean_alloc_closure((void*)(l_instMonadControlExceptTOfMonad___redArg___lam__2), 5, 3);
lean_closure_set(v___f_945_, 0, v_inst_942_);
lean_closure_set(v___f_945_, 1, v___f_943_);
lean_closure_set(v___f_945_, 2, v___f_944_);
v___f_946_ = ((lean_object*)(l_instMonadControlExceptTOfMonad___redArg___closed__1));
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___f_945_);
lean_ctor_set(v___x_947_, 1, v___f_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlExceptTOfMonad(lean_object* v_00_u03b5_948_, lean_object* v_m_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_instMonadControlExceptTOfMonad___redArg(v_inst_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0(lean_object* v_finalizer_952_, lean_object* v_x_953_){
_start:
{
lean_inc(v_finalizer_952_);
return v_finalizer_952_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__0___boxed(lean_object* v_finalizer_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_tryFinally___redArg___lam__0(v_finalizer_954_, v_x_955_);
lean_dec(v_x_955_);
lean_dec(v_finalizer_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1(lean_object* v_x_957_){
_start:
{
lean_object* v_fst_958_; 
v_fst_958_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_fst_958_);
return v_fst_958_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg___lam__1___boxed(lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_tryFinally___redArg___lam__1(v_x_959_);
lean_dec_ref(v_x_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_tryFinally___redArg(lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_x_964_, lean_object* v_finalizer_965_){
_start:
{
lean_object* v_map_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v_y_969_; lean_object* v___x_970_; 
v_map_966_ = lean_ctor_get(v_inst_963_, 0);
lean_inc(v_map_966_);
lean_dec_ref(v_inst_963_);
v___f_967_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_967_, 0, v_finalizer_965_);
v___f_968_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_969_ = lean_apply_4(v_inst_962_, lean_box(0), lean_box(0), v_x_964_, v___f_967_);
v___x_970_ = lean_apply_4(v_map_966_, lean_box(0), lean_box(0), v___f_968_, v_y_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_tryFinally(lean_object* v_m_971_, lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_x_976_, lean_object* v_finalizer_977_){
_start:
{
lean_object* v_map_978_; lean_object* v___f_979_; lean_object* v___f_980_; lean_object* v_y_981_; lean_object* v___x_982_; 
v_map_978_ = lean_ctor_get(v_inst_975_, 0);
lean_inc(v_map_978_);
lean_dec_ref(v_inst_975_);
v___f_979_ = lean_alloc_closure((void*)(l_tryFinally___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_979_, 0, v_finalizer_977_);
v___f_980_ = ((lean_object*)(l_tryFinally___redArg___closed__0));
v_y_981_ = lean_apply_4(v_inst_974_, lean_box(0), lean_box(0), v_x_976_, v___f_979_);
v___x_982_ = lean_apply_4(v_map_978_, lean_box(0), lean_box(0), v___f_980_, v_y_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Id_finally___lam__0(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_h_986_){
_start:
{
lean_object* v___x_987_; lean_object* v_b_988_; lean_object* v___x_989_; 
lean_inc(v_x_985_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v_x_985_);
v_b_988_ = lean_apply_1(v_h_986_, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_x_985_);
lean_ctor_set(v___x_989_, 1, v_b_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__0(lean_object* v_toPure_992_, lean_object* v_r_993_){
_start:
{
lean_object* v_e_995_; lean_object* v_fst_998_; 
v_fst_998_ = lean_ctor_get(v_r_993_, 0);
lean_inc(v_fst_998_);
if (lean_obj_tag(v_fst_998_) == 0)
{
lean_object* v_snd_999_; 
v_snd_999_ = lean_ctor_get(v_r_993_, 1);
lean_inc(v_snd_999_);
lean_dec_ref(v_r_993_);
if (lean_obj_tag(v_snd_999_) == 0)
{
lean_object* v_a_1000_; 
lean_dec_ref_known(v_fst_998_, 1);
v_a_1000_ = lean_ctor_get(v_snd_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v_snd_999_, 1);
v_e_995_ = v_a_1000_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v_a_1001_ = lean_ctor_get(v_fst_998_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v_fst_998_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_snd_999_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_snd_999_, 0);
lean_dec(v_unused_1010_);
v___x_1003_ = v_snd_999_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v_snd_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
lean_ctor_set(v___x_1003_, 0, v_a_1001_);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_apply_2(v_toPure_992_, lean_box(0), v___x_1006_);
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_snd_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1029_; 
v_snd_1011_ = lean_ctor_get(v_r_993_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_r_993_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_r_993_, 0);
lean_dec(v_unused_1030_);
v___x_1013_ = v_r_993_;
v_isShared_1014_ = v_isSharedCheck_1029_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snd_1011_);
lean_dec(v_r_993_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1029_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
if (lean_obj_tag(v_snd_1011_) == 0)
{
lean_object* v_a_1015_; 
lean_del_object(v___x_1013_);
lean_dec_ref_known(v_fst_998_, 1);
v_a_1015_ = lean_ctor_get(v_snd_1011_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v_snd_1011_, 1);
v_e_995_ = v_a_1015_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1028_; 
v_a_1016_ = lean_ctor_get(v_fst_998_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v_fst_998_, 1);
v_a_1017_ = lean_ctor_get(v_snd_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_snd_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1019_ = v_snd_1011_;
v_isShared_1020_ = v_isSharedCheck_1028_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v_snd_1011_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1028_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1017_);
lean_ctor_set(v___x_1013_, 0, v_a_1016_);
v___x_1022_ = v___x_1013_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1016_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1022_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_apply_2(v_toPure_992_, lean_box(0), v___x_1024_);
return v___x_1025_;
}
}
}
}
}
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_e_995_);
v___x_997_ = lean_apply_2(v_toPure_992_, lean_box(0), v___x_996_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__1(lean_object* v_h_1031_, lean_object* v_e_x3f_1032_){
_start:
{
if (lean_obj_tag(v_e_x3f_1032_) == 0)
{
goto v___jp_1033_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1045_; 
v_val_1036_ = lean_ctor_get(v_e_x3f_1032_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_e_x3f_1032_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1038_ = v_e_x3f_1032_;
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v_e_x3f_1032_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
if (lean_obj_tag(v_val_1036_) == 0)
{
lean_dec_ref_known(v_val_1036_, 1);
lean_del_object(v___x_1038_);
goto v___jp_1033_;
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; 
v_a_1040_ = lean_ctor_get(v_val_1036_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_val_1036_, 1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_a_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1040_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_1(v_h_1031_, v___x_1042_);
return v___x_1043_;
}
}
}
}
v___jp_1033_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_apply_1(v_h_1031_, v___x_1034_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg___lam__2(lean_object* v_inst_1046_, lean_object* v_toBind_1047_, lean_object* v___f_1048_, lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_h_1052_){
_start:
{
lean_object* v___f_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___f_1053_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1053_, 0, v_h_1052_);
v___x_1054_ = lean_apply_4(v_inst_1046_, lean_box(0), lean_box(0), v_x_1051_, v___f_1053_);
v___x_1055_ = lean_apply_4(v_toBind_1047_, lean_box(0), lean_box(0), v___x_1054_, v___f_1048_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally___redArg(lean_object* v_inst_1056_, lean_object* v_inst_1057_){
_start:
{
lean_object* v_toApplicative_1058_; lean_object* v_toBind_1059_; lean_object* v_toPure_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; 
v_toApplicative_1058_ = lean_ctor_get(v_inst_1057_, 0);
lean_inc_ref(v_toApplicative_1058_);
v_toBind_1059_ = lean_ctor_get(v_inst_1057_, 1);
lean_inc(v_toBind_1059_);
lean_dec_ref(v_inst_1057_);
v_toPure_1060_ = lean_ctor_get(v_toApplicative_1058_, 1);
lean_inc(v_toPure_1060_);
lean_dec_ref(v_toApplicative_1058_);
v___f_1061_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1061_, 0, v_toPure_1060_);
v___f_1062_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1062_, 0, v_inst_1056_);
lean_closure_set(v___f_1062_, 1, v_toBind_1059_);
lean_closure_set(v___f_1062_, 2, v___f_1061_);
return v___f_1062_;
}
}
LEAN_EXPORT lean_object* l_ExceptT_finally(lean_object* v_m_1063_, lean_object* v_00_u03b5_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v_toApplicative_1067_; lean_object* v_toBind_1068_; lean_object* v_toPure_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; 
v_toApplicative_1067_ = lean_ctor_get(v_inst_1066_, 0);
lean_inc_ref(v_toApplicative_1067_);
v_toBind_1068_ = lean_ctor_get(v_inst_1066_, 1);
lean_inc(v_toBind_1068_);
lean_dec_ref(v_inst_1066_);
v_toPure_1069_ = lean_ctor_get(v_toApplicative_1067_, 1);
lean_inc(v_toPure_1069_);
lean_dec_ref(v_toApplicative_1067_);
v___f_1070_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1070_, 0, v_toPure_1069_);
v___f_1071_ = lean_alloc_closure((void*)(l_ExceptT_finally___redArg___lam__2), 7, 3);
lean_closure_set(v___f_1071_, 0, v_inst_1065_);
lean_closure_set(v___f_1071_, 1, v_toBind_1068_);
lean_closure_set(v___f_1071_, 2, v___f_1070_);
return v___f_1071_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___lam__0(lean_object* v_00_u03b1_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v_x_1073_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v_x_1073_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v_x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v_x_1073_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v_x_1073_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v_x_1073_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg(){
_start:
{
lean_object* v___f_1092_; 
v___f_1092_ = ((lean_object*)(l_instMonadAttachExcept___redArg___closed__0));
return v___f_1092_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept___redArg___boxed(lean_object* v___dummy_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_instMonadAttachExcept___redArg();
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExcept(lean_object* v_00_u03b5_1095_){
_start:
{
lean_object* v___f_1096_; 
v___f_1096_ = ((lean_object*)(l_instMonadAttachExcept___redArg___closed__0));
return v___f_1096_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__0(lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v_x_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v_x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v_x_1097_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v_x_1097_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg___lam__1(lean_object* v_toFunctor_1114_, lean_object* v_inst_1115_, lean_object* v___f_1116_, lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_map_1119_; lean_object* v___x_1120_; lean_object* v_this_1121_; 
v_map_1119_ = lean_ctor_get(v_toFunctor_1114_, 0);
lean_inc(v_map_1119_);
lean_dec_ref(v_toFunctor_1114_);
v___x_1120_ = lean_apply_2(v_inst_1115_, lean_box(0), v_x_1118_);
v_this_1121_ = lean_apply_4(v_map_1119_, lean_box(0), lean_box(0), v___f_1116_, v___x_1120_);
return v_this_1121_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad___redArg(lean_object* v_inst_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v_toApplicative_1125_; lean_object* v_toFunctor_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; 
v_toApplicative_1125_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1125_);
lean_dec_ref(v_inst_1123_);
v_toFunctor_1126_ = lean_ctor_get(v_toApplicative_1125_, 0);
lean_inc_ref(v_toFunctor_1126_);
lean_dec_ref(v_toApplicative_1125_);
v___f_1127_ = ((lean_object*)(l_instMonadAttachExceptTOfMonad___redArg___closed__0));
v___f_1128_ = lean_alloc_closure((void*)(l_instMonadAttachExceptTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1128_, 0, v_toFunctor_1126_);
lean_closure_set(v___f_1128_, 1, v_inst_1124_);
lean_closure_set(v___f_1128_, 2, v___f_1127_);
return v___f_1128_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachExceptTOfMonad(lean_object* v_m_1129_, lean_object* v_00_u03b5_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_instMonadAttachExceptTOfMonad___redArg(v_inst_1131_, v_inst_1132_);
return v___x_1133_;
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
