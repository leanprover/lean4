// Lean compiler output
// Module: Lean.Util.MonadCache
// Imports: public import Std.Data.HashMap.Basic
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
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0 = (const lean_object*)&l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value;
static const lean_closure_object l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1 = (const lean_object*)&l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__3(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MonadCacheT_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadCacheT_run___redArg___closed__0;
static lean_once_cell_t l_Lean_MonadCacheT_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadCacheT_run___redArg___closed__1;
static lean_once_cell_t l_Lean_MonadCacheT_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadCacheT_run___redArg___closed__2;
static lean_once_cell_t l_Lean_MonadCacheT_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadCacheT_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MonadStateCacheT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MonadStateCacheT_run___redArg___closed__0 = (const lean_object*)&l_Lean_MonadStateCacheT_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_b_2_, lean_object* v_____r_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v_b_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__1(lean_object* v_toPure_5_, lean_object* v_cache_6_, lean_object* v_a_7_, lean_object* v_toBind_8_, lean_object* v_b_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_b_9_);
v___f_10_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v_toPure_5_);
lean_closure_set(v___f_10_, 1, v_b_9_);
v___x_11_ = lean_apply_2(v_cache_6_, v_a_7_, v_b_9_);
v___x_12_ = lean_apply_4(v_toBind_8_, lean_box(0), lean_box(0), v___x_11_, v___f_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg___lam__2(lean_object* v_f_13_, lean_object* v_toBind_14_, lean_object* v___f_15_, lean_object* v_toPure_16_, lean_object* v_____do__lift_17_){
_start:
{
if (lean_obj_tag(v_____do__lift_17_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_toPure_16_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_f_13_, v___x_18_);
v___x_20_ = lean_apply_4(v_toBind_14_, lean_box(0), lean_box(0), v___x_19_, v___f_15_);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_22_; 
lean_dec(v___f_15_);
lean_dec(v_toBind_14_);
lean_dec(v_f_13_);
v_val_21_ = lean_ctor_get(v_____do__lift_17_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_____do__lift_17_, 1);
v___x_22_ = lean_apply_2(v_toPure_16_, lean_box(0), v_val_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkCache___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_a_25_, lean_object* v_f_26_){
_start:
{
lean_object* v_toApplicative_27_; lean_object* v_toBind_28_; lean_object* v_findCached_x3f_29_; lean_object* v_cache_30_; lean_object* v_toPure_31_; lean_object* v___x_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; 
v_toApplicative_27_ = lean_ctor_get(v_inst_24_, 0);
lean_inc_ref(v_toApplicative_27_);
v_toBind_28_ = lean_ctor_get(v_inst_24_, 1);
lean_inc_n(v_toBind_28_, 3);
lean_dec_ref(v_inst_24_);
v_findCached_x3f_29_ = lean_ctor_get(v_inst_23_, 0);
lean_inc(v_findCached_x3f_29_);
v_cache_30_ = lean_ctor_get(v_inst_23_, 1);
lean_inc(v_cache_30_);
lean_dec_ref(v_inst_23_);
v_toPure_31_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc_n(v_toPure_31_, 2);
lean_dec_ref(v_toApplicative_27_);
lean_inc(v_a_25_);
v___x_32_ = lean_apply_1(v_findCached_x3f_29_, v_a_25_);
v___f_33_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__1), 5, 4);
lean_closure_set(v___f_33_, 0, v_toPure_31_);
lean_closure_set(v___f_33_, 1, v_cache_30_);
lean_closure_set(v___f_33_, 2, v_a_25_);
lean_closure_set(v___f_33_, 3, v_toBind_28_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__2), 5, 4);
lean_closure_set(v___f_34_, 0, v_f_26_);
lean_closure_set(v___f_34_, 1, v_toBind_28_);
lean_closure_set(v___f_34_, 2, v___f_33_);
lean_closure_set(v___f_34_, 3, v_toPure_31_);
v___x_35_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v___x_32_, v___f_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkCache(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_m_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_a_41_, lean_object* v_f_42_){
_start:
{
lean_object* v_toApplicative_43_; lean_object* v_toBind_44_; lean_object* v_findCached_x3f_45_; lean_object* v_cache_46_; lean_object* v_toPure_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v_toApplicative_43_ = lean_ctor_get(v_inst_40_, 0);
lean_inc_ref(v_toApplicative_43_);
v_toBind_44_ = lean_ctor_get(v_inst_40_, 1);
lean_inc_n(v_toBind_44_, 3);
lean_dec_ref(v_inst_40_);
v_findCached_x3f_45_ = lean_ctor_get(v_inst_39_, 0);
lean_inc(v_findCached_x3f_45_);
v_cache_46_ = lean_ctor_get(v_inst_39_, 1);
lean_inc(v_cache_46_);
lean_dec_ref(v_inst_39_);
v_toPure_47_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc_n(v_toPure_47_, 2);
lean_dec_ref(v_toApplicative_43_);
lean_inc(v_a_41_);
v___x_48_ = lean_apply_1(v_findCached_x3f_45_, v_a_41_);
v___f_49_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__1), 5, 4);
lean_closure_set(v___f_49_, 0, v_toPure_47_);
lean_closure_set(v___f_49_, 1, v_cache_46_);
lean_closure_set(v___f_49_, 2, v_a_41_);
lean_closure_set(v___f_49_, 3, v_toBind_44_);
v___f_50_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__2), 5, 4);
lean_closure_set(v___f_50_, 0, v_f_42_);
lean_closure_set(v___f_50_, 1, v_toBind_44_);
lean_closure_set(v___f_50_, 2, v___f_49_);
lean_closure_set(v___f_50_, 3, v_toPure_47_);
v___x_51_ = lean_apply_4(v_toBind_44_, lean_box(0), lean_box(0), v___x_48_, v___f_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__0(lean_object* v_inst_52_, lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_findCached_x3f_55_; lean_object* v___x_56_; 
v_findCached_x3f_55_ = lean_ctor_get(v_inst_52_, 0);
lean_inc(v_findCached_x3f_55_);
lean_dec_ref(v_inst_52_);
v___x_56_ = lean_apply_1(v_findCached_x3f_55_, v_a_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed(lean_object* v_inst_57_, lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_instMonadCacheReaderT___redArg___lam__0(v_inst_57_, v_a_58_, v_x_59_);
lean_dec(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__1(lean_object* v_inst_61_, lean_object* v_a_62_, lean_object* v_b_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_cache_65_; lean_object* v___x_66_; 
v_cache_65_ = lean_ctor_get(v_inst_61_, 1);
lean_inc(v_cache_65_);
lean_dec_ref(v_inst_61_);
v___x_66_ = lean_apply_2(v_cache_65_, v_a_62_, v_b_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed(lean_object* v_inst_67_, lean_object* v_a_68_, lean_object* v_b_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_instMonadCacheReaderT___redArg___lam__1(v_inst_67_, v_a_68_, v_b_69_, v_x_70_);
lean_dec(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT___redArg(lean_object* v_inst_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; 
lean_inc_ref(v_inst_72_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_73_, 0, v_inst_72_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_74_, 0, v_inst_72_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___f_73_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheReaderT(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_00_u03c1_78_, lean_object* v_m_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_instMonadCacheReaderT___redArg(v_inst_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0(lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v_a_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v___f_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_toApplicative_88_; lean_object* v_toFunctor_89_; lean_object* v_findCached_x3f_90_; lean_object* v_map_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_toApplicative_88_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toApplicative_88_);
lean_dec_ref(v_inst_85_);
v_toFunctor_89_ = lean_ctor_get(v_toApplicative_88_, 0);
lean_inc_ref(v_toFunctor_89_);
lean_dec_ref(v_toApplicative_88_);
v_findCached_x3f_90_ = lean_ctor_get(v_inst_84_, 0);
lean_inc(v_findCached_x3f_90_);
lean_dec_ref(v_inst_84_);
v_map_91_ = lean_ctor_get(v_toFunctor_89_, 0);
lean_inc(v_map_91_);
lean_dec_ref(v_toFunctor_89_);
v___x_92_ = lean_apply_1(v_findCached_x3f_90_, v_a_87_);
v___x_93_ = lean_apply_4(v_map_91_, lean_box(0), lean_box(0), v___f_86_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2(lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_a_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3(lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v___f_98_, lean_object* v_a_99_, lean_object* v_b_100_){
_start:
{
lean_object* v_toApplicative_101_; lean_object* v_toFunctor_102_; lean_object* v_cache_103_; lean_object* v_map_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_toApplicative_101_ = lean_ctor_get(v_inst_97_, 0);
lean_inc_ref(v_toApplicative_101_);
lean_dec_ref(v_inst_97_);
v_toFunctor_102_ = lean_ctor_get(v_toApplicative_101_, 0);
lean_inc_ref(v_toFunctor_102_);
lean_dec_ref(v_toApplicative_101_);
v_cache_103_ = lean_ctor_get(v_inst_96_, 1);
lean_inc(v_cache_103_);
lean_dec_ref(v_inst_96_);
v_map_104_ = lean_ctor_get(v_toFunctor_102_, 0);
lean_inc(v_map_104_);
lean_dec_ref(v_toFunctor_102_);
v___x_105_ = lean_apply_2(v_cache_103_, v_a_99_, v_b_100_);
v___x_106_ = lean_apply_4(v_map_104_, lean_box(0), lean_box(0), v___f_98_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad___redArg(lean_object* v_inst_109_, lean_object* v_inst_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v___f_111_ = ((lean_object*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0));
lean_inc_ref(v_inst_110_);
lean_inc_ref(v_inst_109_);
v___f_112_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_112_, 0, v_inst_109_);
lean_closure_set(v___f_112_, 1, v_inst_110_);
lean_closure_set(v___f_112_, 2, v___f_111_);
v___f_113_ = ((lean_object*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1));
v___f_114_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3), 5, 3);
lean_closure_set(v___f_114_, 0, v_inst_109_);
lean_closure_set(v___f_114_, 1, v_inst_110_);
lean_closure_set(v___f_114_, 2, v___f_113_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___f_112_);
lean_ctor_set(v___x_115_, 1, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadCacheExceptTOfMonad(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_00_u03b5_118_, lean_object* v_m_119_, lean_object* v_inst_120_, lean_object* v_inst_121_){
_start:
{
lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
v___f_122_ = ((lean_object*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0));
lean_inc_ref(v_inst_121_);
lean_inc_ref(v_inst_120_);
v___f_123_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_123_, 0, v_inst_120_);
lean_closure_set(v___f_123_, 1, v_inst_121_);
lean_closure_set(v___f_123_, 2, v___f_122_);
v___f_124_ = ((lean_object*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1));
v___f_125_ = lean_alloc_closure((void*)(l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3), 5, 3);
lean_closure_set(v___f_125_, 0, v_inst_120_);
lean_closure_set(v___f_125_, 1, v_inst_121_);
lean_closure_set(v___f_125_, 2, v___f_124_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___f_123_);
lean_ctor_set(v___x_126_, 1, v___f_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_a_129_, lean_object* v_toPure_130_, lean_object* v_c_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_127_, v_inst_128_, v_c_131_, v_a_129_);
v___x_133_ = lean_apply_2(v_toPure_130_, lean_box(0), v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_a_136_, lean_object* v_toPure_137_, lean_object* v_c_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(v_inst_134_, v_inst_135_, v_a_136_, v_toPure_137_, v_c_138_);
lean_dec_ref(v_c_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_toApplicative_145_; lean_object* v_toBind_146_; lean_object* v_getCache_147_; lean_object* v_toPure_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v_toApplicative_145_ = lean_ctor_get(v_inst_142_, 0);
lean_inc_ref(v_toApplicative_145_);
v_toBind_146_ = lean_ctor_get(v_inst_142_, 1);
lean_inc(v_toBind_146_);
lean_dec_ref(v_inst_142_);
v_getCache_147_ = lean_ctor_get(v_inst_143_, 0);
lean_inc(v_getCache_147_);
lean_dec_ref(v_inst_143_);
v_toPure_148_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_inc(v_toPure_148_);
lean_dec_ref(v_toApplicative_145_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_149_, 0, v_inst_140_);
lean_closure_set(v___f_149_, 1, v_inst_141_);
lean_closure_set(v___f_149_, 2, v_a_144_);
lean_closure_set(v___f_149_, 3, v_toPure_148_);
v___x_150_ = lean_apply_4(v_toBind_146_, lean_box(0), lean_box(0), v_getCache_147_, v___f_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_findCached_x3f(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_m_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_toApplicative_159_; lean_object* v_toBind_160_; lean_object* v_getCache_161_; lean_object* v_toPure_162_; lean_object* v___f_163_; lean_object* v___x_164_; 
v_toApplicative_159_ = lean_ctor_get(v_inst_156_, 0);
lean_inc_ref(v_toApplicative_159_);
v_toBind_160_ = lean_ctor_get(v_inst_156_, 1);
lean_inc(v_toBind_160_);
lean_dec_ref(v_inst_156_);
v_getCache_161_ = lean_ctor_get(v_inst_157_, 0);
lean_inc(v_getCache_161_);
lean_dec_ref(v_inst_157_);
v_toPure_162_ = lean_ctor_get(v_toApplicative_159_, 1);
lean_inc(v_toPure_162_);
lean_dec_ref(v_toApplicative_159_);
v___f_163_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_163_, 0, v_inst_154_);
lean_closure_set(v___f_163_, 1, v_inst_155_);
lean_closure_set(v___f_163_, 2, v_a_158_);
lean_closure_set(v___f_163_, 3, v_toPure_162_);
v___x_164_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v_getCache_161_, v___f_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_a_167_, lean_object* v_b_168_, lean_object* v_s_169_){
_start:
{
lean_object* v___y_171_; lean_object* v_i_172_; lean_object* v___y_188_; lean_object* v_i_189_; lean_object* v___y_195_; lean_object* v___x_204_; 
lean_inc(v_a_167_);
lean_inc_ref(v_inst_166_);
lean_inc_ref(v_inst_165_);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_165_, v_inst_166_, v_s_169_, v_a_167_);
switch(lean_obj_tag(v___x_204_))
{
case 0:
{
lean_object* v_index_205_; lean_object* v_size_206_; lean_object* v___x_207_; 
lean_dec_ref(v_inst_166_);
lean_dec_ref(v_inst_165_);
v_index_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_205_);
lean_dec_ref_known(v___x_204_, 3);
v_size_206_ = lean_ctor_get(v_s_169_, 0);
lean_inc(v_size_206_);
v___x_207_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_169_, v_size_206_, v_index_205_, v_a_167_, v_b_168_);
lean_dec(v_index_205_);
return v___x_207_;
}
case 1:
{
lean_object* v_index_208_; lean_object* v_size_209_; lean_object* v_keyArray_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_index_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_204_, 1);
v_size_209_ = lean_ctor_get(v_s_169_, 0);
v_keyArray_210_ = lean_ctor_get(v_s_169_, 1);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_size_209_, v___x_211_);
v___x_213_ = lean_array_get_size(v_keyArray_210_);
v___x_214_ = lean_nat_dec_lt(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v___x_212_);
lean_dec(v_index_208_);
goto v___jp_177_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_215_ = lean_unsigned_to_nat(4u);
v___x_216_ = lean_nat_mul(v___x_212_, v___x_215_);
v___x_217_ = lean_unsigned_to_nat(3u);
v___x_218_ = lean_nat_mul(v___x_213_, v___x_217_);
v___x_219_ = lean_nat_dec_le(v___x_216_, v___x_218_);
lean_dec(v___x_218_);
lean_dec(v___x_216_);
if (v___x_219_ == 0)
{
lean_dec(v___x_212_);
lean_dec(v_index_208_);
goto v___jp_177_;
}
else
{
lean_object* v___x_220_; 
lean_dec_ref(v_inst_166_);
lean_dec_ref(v_inst_165_);
v___x_220_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_169_, v___x_212_, v_index_208_, v_a_167_, v_b_168_);
lean_dec(v_index_208_);
return v___x_220_;
}
}
}
default: 
{
lean_object* v_size_221_; lean_object* v_keyArray_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_size_221_ = lean_ctor_get(v_s_169_, 0);
v_keyArray_222_ = lean_ctor_get(v_s_169_, 1);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_size_221_, v___x_223_);
v___x_225_ = lean_array_get_size(v_keyArray_222_);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v___x_224_);
lean_inc_ref(v_inst_166_);
lean_inc_ref(v_inst_165_);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_165_, v_inst_166_, v_s_169_);
v___y_195_ = v___x_227_;
goto v___jp_194_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = lean_nat_mul(v___x_224_, v___x_228_);
lean_dec(v___x_224_);
v___x_230_ = lean_unsigned_to_nat(3u);
v___x_231_ = lean_nat_mul(v___x_225_, v___x_230_);
v___x_232_ = lean_nat_dec_le(v___x_229_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v___x_229_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_inc_ref(v_inst_166_);
lean_inc_ref(v_inst_165_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_165_, v_inst_166_, v_s_169_);
v___y_195_ = v___x_233_;
goto v___jp_194_;
}
else
{
v___y_195_ = v_s_169_;
goto v___jp_194_;
}
}
}
}
v___jp_170_:
{
lean_object* v_size_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_size_173_ = lean_ctor_get(v___y_171_, 0);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_size_173_, v___x_174_);
v___x_176_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_171_, v___x_175_, v_i_172_, v_a_167_, v_b_168_);
lean_dec(v_i_172_);
return v___x_176_;
}
v___jp_177_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref(v_inst_166_);
lean_inc_ref(v_inst_165_);
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_165_, v_inst_166_, v_s_169_);
lean_inc(v_a_167_);
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_165_, v_inst_166_, v___x_178_, v_a_167_);
switch(lean_obj_tag(v___x_179_))
{
case 0:
{
lean_object* v_index_180_; lean_object* v_size_181_; lean_object* v___x_182_; 
v_index_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_index_180_);
lean_dec_ref_known(v___x_179_, 3);
v_size_181_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_size_181_);
v___x_182_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_178_, v_size_181_, v_index_180_, v_a_167_, v_b_168_);
lean_dec(v_index_180_);
return v___x_182_;
}
case 1:
{
lean_object* v_index_183_; 
v_index_183_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_index_183_);
lean_dec_ref_known(v___x_179_, 1);
v___y_171_ = v___x_178_;
v_i_172_ = v_index_183_;
goto v___jp_170_;
}
default: 
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_178_, v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_index_186_; 
v_index_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_index_186_);
lean_dec_ref_known(v___x_185_, 1);
v___y_171_ = v___x_178_;
v_i_172_ = v_index_186_;
goto v___jp_170_;
}
else
{
lean_dec(v_b_168_);
lean_dec(v_a_167_);
return v___x_178_;
}
}
}
}
v___jp_187_:
{
lean_object* v_size_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_size_190_ = lean_ctor_get(v___y_188_, 0);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_size_190_, v___x_191_);
v___x_193_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_188_, v___x_192_, v_i_189_, v_a_167_, v_b_168_);
lean_dec(v_i_189_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; 
lean_inc(v_a_167_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_165_, v_inst_166_, v___y_195_, v_a_167_);
switch(lean_obj_tag(v___x_196_))
{
case 0:
{
lean_object* v_index_197_; lean_object* v_size_198_; lean_object* v___x_199_; 
v_index_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_196_, 3);
v_size_198_ = lean_ctor_get(v___y_195_, 0);
lean_inc(v_size_198_);
v___x_199_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_195_, v_size_198_, v_index_197_, v_a_167_, v_b_168_);
lean_dec(v_index_197_);
return v___x_199_;
}
case 1:
{
lean_object* v_index_200_; 
v_index_200_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_196_, 1);
v___y_188_ = v___y_195_;
v_i_189_ = v_index_200_;
goto v___jp_187_;
}
default: 
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_195_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_202_, 1);
v___y_188_ = v___y_195_;
v_i_189_ = v_index_203_;
goto v___jp_187_;
}
else
{
lean_dec(v_b_168_);
lean_dec(v_a_167_);
return v___y_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_modifyCache_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v_modifyCache_239_ = lean_ctor_get(v_inst_236_, 1);
lean_inc(v_modifyCache_239_);
lean_dec_ref(v_inst_236_);
v___f_240_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0), 5, 4);
lean_closure_set(v___f_240_, 0, v_inst_234_);
lean_closure_set(v___f_240_, 1, v_inst_235_);
lean_closure_set(v___f_240_, 2, v_a_237_);
lean_closure_set(v___f_240_, 3, v_b_238_);
v___x_241_ = lean_apply_1(v_modifyCache_239_, v___f_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_m_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
lean_object* v_modifyCache_250_; lean_object* v___f_251_; lean_object* v___x_252_; 
v_modifyCache_250_ = lean_ctor_get(v_inst_247_, 1);
lean_inc(v_modifyCache_250_);
lean_dec_ref(v_inst_247_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0), 5, 4);
lean_closure_set(v___f_251_, 0, v_inst_245_);
lean_closure_set(v___f_251_, 1, v_inst_246_);
lean_closure_set(v___f_251_, 2, v_a_248_);
lean_closure_set(v___f_251_, 3, v_b_249_);
v___x_252_ = lean_apply_1(v_modifyCache_250_, v___f_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_inc_ref(v_inst_256_);
lean_inc_ref(v_inst_254_);
lean_inc_ref(v_inst_253_);
v___x_257_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_findCached_x3f), 8, 7);
lean_closure_set(v___x_257_, 0, lean_box(0));
lean_closure_set(v___x_257_, 1, lean_box(0));
lean_closure_set(v___x_257_, 2, lean_box(0));
lean_closure_set(v___x_257_, 3, v_inst_253_);
lean_closure_set(v___x_257_, 4, v_inst_254_);
lean_closure_set(v___x_257_, 5, v_inst_255_);
lean_closure_set(v___x_257_, 6, v_inst_256_);
v___x_258_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache), 8, 6);
lean_closure_set(v___x_258_, 0, lean_box(0));
lean_closure_set(v___x_258_, 1, lean_box(0));
lean_closure_set(v___x_258_, 2, lean_box(0));
lean_closure_set(v___x_258_, 3, v_inst_253_);
lean_closure_set(v___x_258_, 4, v_inst_254_);
lean_closure_set(v___x_258_, 5, v_inst_256_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(lean_object* v_00_u03b1_260_, lean_object* v_00_u03b2_261_, lean_object* v_m_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(v_inst_263_, v_inst_264_, v_inst_265_, v_inst_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_f_268_, lean_object* v_s_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_f_268_, v_s_269_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(lean_object* v_inst_273_, lean_object* v_f_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 2, 1);
lean_closure_set(v___f_276_, 0, v_f_274_);
lean_inc(v___y_275_);
v___x_277_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_277_, 0, lean_box(0));
lean_closure_set(v___x_277_, 1, lean_box(0));
lean_closure_set(v___x_277_, 2, lean_box(0));
lean_closure_set(v___x_277_, 3, v___y_275_);
lean_closure_set(v___x_277_, 4, v___f_276_);
v___x_278_ = lean_apply_2(v_inst_273_, lean_box(0), v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(lean_object* v_inst_279_, lean_object* v_f_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(v_inst_279_, v_f_280_, v___y_281_);
lean_dec(v___y_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_283_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc(v_inst_283_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_284_, 0, v_inst_283_);
v___x_285_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_285_, 0, lean_box(0));
lean_closure_set(v___x_285_, 1, lean_box(0));
lean_closure_set(v___x_285_, 2, lean_box(0));
lean_closure_set(v___x_285_, 3, v_inst_283_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___f_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03c9_287_, lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_m_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03c9_296_, lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_m_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(v_00_u03c9_296_, v_00_u03b1_297_, v_00_u03b2_298_, v_m_299_, v_inst_300_, v_inst_301_, v_inst_302_, v_inst_303_);
lean_dec_ref(v_inst_302_);
lean_dec_ref(v_inst_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__0(lean_object* v_a_305_, lean_object* v_toPure_306_, lean_object* v_s_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_a_305_);
lean_ctor_set(v___x_308_, 1, v_s_307_);
v___x_309_ = lean_apply_2(v_toPure_306_, lean_box(0), v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__1(lean_object* v_toPure_310_, lean_object* v_ref_311_, lean_object* v_inst_312_, lean_object* v_toBind_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___f_315_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_315_, 0, v_a_314_);
lean_closure_set(v___f_315_, 1, v_toPure_310_);
v___x_316_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_316_, 0, lean_box(0));
lean_closure_set(v___x_316_, 1, lean_box(0));
lean_closure_set(v___x_316_, 2, v_ref_311_);
v___x_317_ = lean_apply_2(v_inst_312_, lean_box(0), v___x_316_);
v___x_318_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_317_, v___f_315_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__2(lean_object* v_toPure_319_, lean_object* v_inst_320_, lean_object* v_toBind_321_, lean_object* v_x_322_, lean_object* v_ref_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_inc(v_toBind_321_);
lean_inc(v_ref_323_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_324_, 0, v_toPure_319_);
lean_closure_set(v___f_324_, 1, v_ref_323_);
lean_closure_set(v___f_324_, 2, v_inst_320_);
lean_closure_set(v___f_324_, 3, v_toBind_321_);
v___x_325_ = lean_apply_1(v_x_322_, v_ref_323_);
v___x_326_ = lean_apply_4(v_toBind_321_, lean_box(0), lean_box(0), v___x_325_, v___f_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__3(lean_object* v_toPure_327_, lean_object* v_____x_328_){
_start:
{
lean_object* v_fst_329_; lean_object* v___x_330_; 
v_fst_329_ = lean_ctor_get(v_____x_328_, 0);
lean_inc(v_fst_329_);
lean_dec_ref(v_____x_328_);
v___x_330_ = lean_apply_2(v_toPure_327_, lean_box(0), v_fst_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_331_; lean_object* v___x_332_; 
v_cellCount_331_ = lean_unsigned_to_nat(16u);
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_333_; lean_object* v___x_334_; 
v_cellCount_333_ = lean_unsigned_to_nat(16u);
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_336_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__0, &l_Lean_MonadCacheT_run___redArg___closed__0_once, _init_l_Lean_MonadCacheT_run___redArg___closed__0);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_335_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
v___x_340_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_340_, 0, lean_box(0));
lean_closure_set(v___x_340_, 1, lean_box(0));
lean_closure_set(v___x_340_, 2, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_toApplicative_344_; lean_object* v_toBind_345_; lean_object* v_toPure_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_toApplicative_344_ = lean_ctor_get(v_inst_342_, 0);
lean_inc_ref(v_toApplicative_344_);
v_toBind_345_ = lean_ctor_get(v_inst_342_, 1);
lean_inc_n(v_toBind_345_, 3);
lean_dec_ref(v_inst_342_);
v_toPure_346_ = lean_ctor_get(v_toApplicative_344_, 1);
lean_inc_n(v_toPure_346_, 2);
lean_dec_ref(v_toApplicative_344_);
v___x_347_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__3, &l_Lean_MonadCacheT_run___redArg___closed__3_once, _init_l_Lean_MonadCacheT_run___redArg___closed__3);
lean_inc(v_inst_341_);
v___x_348_ = lean_apply_2(v_inst_341_, lean_box(0), v___x_347_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_349_, 0, v_toPure_346_);
lean_closure_set(v___f_349_, 1, v_inst_341_);
lean_closure_set(v___f_349_, 2, v_toBind_345_);
lean_closure_set(v___f_349_, 3, v_x_343_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_350_, 0, v_toPure_346_);
v___x_351_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v___x_348_, v___f_349_);
v___x_352_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v___x_351_, v___f_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run(lean_object* v_00_u03c9_353_, lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_00_u03c3_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_toApplicative_364_; lean_object* v_toBind_365_; lean_object* v_toPure_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_toApplicative_364_ = lean_ctor_get(v_inst_361_, 0);
lean_inc_ref(v_toApplicative_364_);
v_toBind_365_ = lean_ctor_get(v_inst_361_, 1);
lean_inc_n(v_toBind_365_, 3);
lean_dec_ref(v_inst_361_);
v_toPure_366_ = lean_ctor_get(v_toApplicative_364_, 1);
lean_inc_n(v_toPure_366_, 2);
lean_dec_ref(v_toApplicative_364_);
v___x_367_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__3, &l_Lean_MonadCacheT_run___redArg___closed__3_once, _init_l_Lean_MonadCacheT_run___redArg___closed__3);
lean_inc(v_inst_360_);
v___x_368_ = lean_apply_2(v_inst_360_, lean_box(0), v___x_367_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_369_, 0, v_toPure_366_);
lean_closure_set(v___f_369_, 1, v_inst_360_);
lean_closure_set(v___f_369_, 2, v_toBind_365_);
lean_closure_set(v___f_369_, 3, v_x_363_);
v___f_370_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_370_, 0, v_toPure_366_);
v___x_371_ = lean_apply_4(v_toBind_365_, lean_box(0), lean_box(0), v___x_368_, v___f_369_);
v___x_372_ = lean_apply_4(v_toBind_365_, lean_box(0), lean_box(0), v___x_371_, v___f_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___boxed(lean_object* v_00_u03c9_373_, lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_m_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_00_u03c3_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_MonadCacheT_run(v_00_u03c9_373_, v_00_u03b1_374_, v_00_u03b2_375_, v_m_376_, v_inst_377_, v_inst_378_, v_inst_379_, v_inst_380_, v_inst_381_, v_00_u03c3_382_, v_x_383_);
lean_dec_ref(v_inst_379_);
lean_dec_ref(v_inst_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg(lean_object* v_inst_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_toApplicative_389_; lean_object* v_toFunctor_390_; lean_object* v_map_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_toApplicative_389_ = lean_ctor_get(v_inst_385_, 0);
lean_inc_ref(v_toApplicative_389_);
lean_dec_ref(v_inst_385_);
v_toFunctor_390_ = lean_ctor_get(v_toApplicative_389_, 0);
lean_inc_ref(v_toFunctor_390_);
lean_dec_ref(v_toApplicative_389_);
v_map_391_ = lean_ctor_get(v_toFunctor_390_, 0);
lean_inc(v_map_391_);
lean_dec_ref(v_toFunctor_390_);
lean_inc(v_a_388_);
v___x_392_ = lean_apply_1(v_a_387_, v_a_388_);
v___x_393_ = lean_apply_4(v_map_391_, lean_box(0), lean_box(0), v_a_386_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(lean_object* v_inst_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_MonadCacheT_instMonad___aux__1___redArg(v_inst_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1(lean_object* v_00_u03c9_399_, lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_toApplicative_412_; lean_object* v_toFunctor_413_; lean_object* v_map_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_toApplicative_412_ = lean_ctor_get(v_inst_406_, 0);
lean_inc_ref(v_toApplicative_412_);
lean_dec_ref(v_inst_406_);
v_toFunctor_413_ = lean_ctor_get(v_toApplicative_412_, 0);
lean_inc_ref(v_toFunctor_413_);
lean_dec_ref(v_toApplicative_412_);
v_map_414_ = lean_ctor_get(v_toFunctor_413_, 0);
lean_inc(v_map_414_);
lean_dec_ref(v_toFunctor_413_);
lean_inc(v_a_411_);
v___x_415_ = lean_apply_1(v_a_410_, v_a_411_);
v___x_416_ = lean_apply_4(v_map_414_, lean_box(0), lean_box(0), v_a_409_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___boxed(lean_object* v_00_u03c9_417_, lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_m_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_MonadCacheT_instMonad___aux__1(v_00_u03c9_417_, v_00_u03b1_418_, v_00_u03b2_419_, v_m_420_, v_inst_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_00_u03b1_425_, v_00_u03b2_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_inst_423_);
lean_dec_ref(v_inst_422_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg(lean_object* v_inst_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_toApplicative_435_; lean_object* v_toFunctor_436_; lean_object* v_mapConst_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_toApplicative_435_ = lean_ctor_get(v_inst_431_, 0);
lean_inc_ref(v_toApplicative_435_);
lean_dec_ref(v_inst_431_);
v_toFunctor_436_ = lean_ctor_get(v_toApplicative_435_, 0);
lean_inc_ref(v_toFunctor_436_);
lean_dec_ref(v_toApplicative_435_);
v_mapConst_437_ = lean_ctor_get(v_toFunctor_436_, 1);
lean_inc(v_mapConst_437_);
lean_dec_ref(v_toFunctor_436_);
lean_inc(v_a_434_);
v___x_438_ = lean_apply_1(v_a_433_, v_a_434_);
v___x_439_ = lean_apply_4(v_mapConst_437_, lean_box(0), lean_box(0), v_a_432_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(lean_object* v_inst_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_MonadCacheT_instMonad___aux__3___redArg(v_inst_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3(lean_object* v_00_u03c9_445_, lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_m_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_toApplicative_458_; lean_object* v_toFunctor_459_; lean_object* v_mapConst_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_toApplicative_458_ = lean_ctor_get(v_inst_452_, 0);
lean_inc_ref(v_toApplicative_458_);
lean_dec_ref(v_inst_452_);
v_toFunctor_459_ = lean_ctor_get(v_toApplicative_458_, 0);
lean_inc_ref(v_toFunctor_459_);
lean_dec_ref(v_toApplicative_458_);
v_mapConst_460_ = lean_ctor_get(v_toFunctor_459_, 1);
lean_inc(v_mapConst_460_);
lean_dec_ref(v_toFunctor_459_);
lean_inc(v_a_457_);
v___x_461_ = lean_apply_1(v_a_456_, v_a_457_);
v___x_462_ = lean_apply_4(v_mapConst_460_, lean_box(0), lean_box(0), v_a_455_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___boxed(lean_object* v_00_u03c9_463_, lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_m_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_00_u03b1_471_, lean_object* v_00_u03b2_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_MonadCacheT_instMonad___aux__3(v_00_u03c9_463_, v_00_u03b1_464_, v_00_u03b2_465_, v_m_466_, v_inst_467_, v_inst_468_, v_inst_469_, v_inst_470_, v_00_u03b1_471_, v_00_u03b2_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_inst_469_);
lean_dec_ref(v_inst_468_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___redArg(lean_object* v_inst_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_toApplicative_479_; lean_object* v_toPure_480_; lean_object* v___x_481_; 
v_toApplicative_479_ = lean_ctor_get(v_inst_477_, 0);
lean_inc_ref(v_toApplicative_479_);
lean_dec_ref(v_inst_477_);
v_toPure_480_ = lean_ctor_get(v_toApplicative_479_, 1);
lean_inc(v_toPure_480_);
lean_dec_ref(v_toApplicative_479_);
v___x_481_ = lean_apply_2(v_toPure_480_, lean_box(0), v_a_478_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5(lean_object* v_00_u03c9_482_, lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_m_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_00_u03b1_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_toApplicative_493_; lean_object* v_toPure_494_; lean_object* v___x_495_; 
v_toApplicative_493_ = lean_ctor_get(v_inst_489_, 0);
lean_inc_ref(v_toApplicative_493_);
lean_dec_ref(v_inst_489_);
v_toPure_494_ = lean_ctor_get(v_toApplicative_493_, 1);
lean_inc(v_toPure_494_);
lean_dec_ref(v_toApplicative_493_);
v___x_495_ = lean_apply_2(v_toPure_494_, lean_box(0), v_a_491_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___boxed(lean_object* v_00_u03c9_496_, lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_00_u03b1_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_MonadCacheT_instMonad___aux__5(v_00_u03c9_496_, v_00_u03b1_497_, v_00_u03b2_498_, v_m_499_, v_inst_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_00_u03b1_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_inst_502_);
lean_dec_ref(v_inst_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_box(0);
lean_inc(v_a_509_);
v___x_512_ = lean_apply_2(v_a_508_, v___x_511_, v_a_509_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(v_a_513_, v_a_514_, v_x_515_);
lean_dec(v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg(lean_object* v_inst_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_toApplicative_521_; lean_object* v_toSeq_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_toApplicative_521_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toApplicative_521_);
lean_dec_ref(v_inst_517_);
v_toSeq_522_ = lean_ctor_get(v_toApplicative_521_, 2);
lean_inc(v_toSeq_522_);
lean_dec_ref(v_toApplicative_521_);
lean_inc_n(v_a_520_, 2);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_523_, 0, v_a_519_);
lean_closure_set(v___f_523_, 1, v_a_520_);
v___x_524_ = lean_apply_1(v_a_518_, v_a_520_);
v___x_525_ = lean_apply_4(v_toSeq_522_, lean_box(0), lean_box(0), v___x_524_, v___f_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(lean_object* v_inst_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg(v_inst_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7(lean_object* v_00_u03c9_531_, lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_toApplicative_544_; lean_object* v_toSeq_545_; lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_toApplicative_544_ = lean_ctor_get(v_inst_538_, 0);
lean_inc_ref(v_toApplicative_544_);
lean_dec_ref(v_inst_538_);
v_toSeq_545_ = lean_ctor_get(v_toApplicative_544_, 2);
lean_inc(v_toSeq_545_);
lean_dec_ref(v_toApplicative_544_);
lean_inc_n(v_a_543_, 2);
v___f_546_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_546_, 0, v_a_542_);
lean_closure_set(v___f_546_, 1, v_a_543_);
v___x_547_ = lean_apply_1(v_a_541_, v_a_543_);
v___x_548_ = lean_apply_4(v_toSeq_545_, lean_box(0), lean_box(0), v___x_547_, v___f_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___boxed(lean_object* v_00_u03c9_549_, lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_m_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_MonadCacheT_instMonad___aux__7(v_00_u03c9_549_, v_00_u03b1_550_, v_00_u03b2_551_, v_m_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_inst_556_, v_00_u03b1_557_, v_00_u03b2_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_inst_555_);
lean_dec_ref(v_inst_554_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg(lean_object* v_inst_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_toApplicative_567_; lean_object* v_toSeqLeft_568_; lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_toApplicative_567_ = lean_ctor_get(v_inst_563_, 0);
lean_inc_ref(v_toApplicative_567_);
lean_dec_ref(v_inst_563_);
v_toSeqLeft_568_ = lean_ctor_get(v_toApplicative_567_, 3);
lean_inc(v_toSeqLeft_568_);
lean_dec_ref(v_toApplicative_567_);
lean_inc_n(v_a_566_, 2);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_569_, 0, v_a_565_);
lean_closure_set(v___f_569_, 1, v_a_566_);
v___x_570_ = lean_apply_1(v_a_564_, v_a_566_);
v___x_571_ = lean_apply_4(v_toSeqLeft_568_, lean_box(0), lean_box(0), v___x_570_, v___f_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(lean_object* v_inst_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_MonadCacheT_instMonad___aux__9___redArg(v_inst_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9(lean_object* v_00_u03c9_577_, lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_m_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_toApplicative_590_; lean_object* v_toSeqLeft_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_toApplicative_590_ = lean_ctor_get(v_inst_584_, 0);
lean_inc_ref(v_toApplicative_590_);
lean_dec_ref(v_inst_584_);
v_toSeqLeft_591_ = lean_ctor_get(v_toApplicative_590_, 3);
lean_inc(v_toSeqLeft_591_);
lean_dec_ref(v_toApplicative_590_);
lean_inc_n(v_a_589_, 2);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_592_, 0, v_a_588_);
lean_closure_set(v___f_592_, 1, v_a_589_);
v___x_593_ = lean_apply_1(v_a_587_, v_a_589_);
v___x_594_ = lean_apply_4(v_toSeqLeft_591_, lean_box(0), lean_box(0), v___x_593_, v___f_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___boxed(lean_object* v_00_u03c9_595_, lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_MonadCacheT_instMonad___aux__9(v_00_u03c9_595_, v_00_u03b1_596_, v_00_u03b2_597_, v_m_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_inst_602_, v_00_u03b1_603_, v_00_u03b2_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_inst_601_);
lean_dec_ref(v_inst_600_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg(lean_object* v_inst_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_toApplicative_613_; lean_object* v_toSeqRight_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_toApplicative_613_ = lean_ctor_get(v_inst_609_, 0);
lean_inc_ref(v_toApplicative_613_);
lean_dec_ref(v_inst_609_);
v_toSeqRight_614_ = lean_ctor_get(v_toApplicative_613_, 4);
lean_inc(v_toSeqRight_614_);
lean_dec_ref(v_toApplicative_613_);
lean_inc_n(v_a_612_, 2);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_615_, 0, v_a_611_);
lean_closure_set(v___f_615_, 1, v_a_612_);
v___x_616_ = lean_apply_1(v_a_610_, v_a_612_);
v___x_617_ = lean_apply_4(v_toSeqRight_614_, lean_box(0), lean_box(0), v___x_616_, v___f_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(lean_object* v_inst_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_MonadCacheT_instMonad___aux__11___redArg(v_inst_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11(lean_object* v_00_u03c9_623_, lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_toApplicative_636_; lean_object* v_toSeqRight_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_toApplicative_636_ = lean_ctor_get(v_inst_630_, 0);
lean_inc_ref(v_toApplicative_636_);
lean_dec_ref(v_inst_630_);
v_toSeqRight_637_ = lean_ctor_get(v_toApplicative_636_, 4);
lean_inc(v_toSeqRight_637_);
lean_dec_ref(v_toApplicative_636_);
lean_inc_n(v_a_635_, 2);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_638_, 0, v_a_634_);
lean_closure_set(v___f_638_, 1, v_a_635_);
v___x_639_ = lean_apply_1(v_a_633_, v_a_635_);
v___x_640_ = lean_apply_4(v_toSeqRight_637_, lean_box(0), lean_box(0), v___x_639_, v___f_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___boxed(lean_object* v_00_u03c9_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_MonadCacheT_instMonad___aux__11(v_00_u03c9_641_, v_00_u03b1_642_, v_00_u03b2_643_, v_m_644_, v_inst_645_, v_inst_646_, v_inst_647_, v_inst_648_, v_00_u03b1_649_, v_00_u03b2_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_inst_647_);
lean_dec_ref(v_inst_646_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_f_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_658_; 
lean_inc(v_a_656_);
v___x_658_ = lean_apply_2(v_f_655_, v_a_657_, v_a_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(lean_object* v_f_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_f_659_, v_a_660_, v_a_661_);
lean_dec(v_a_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg(lean_object* v_inst_663_, lean_object* v_x_664_, lean_object* v_f_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_toBind_667_; lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_toBind_667_ = lean_ctor_get(v_inst_663_, 1);
lean_inc(v_toBind_667_);
lean_dec_ref(v_inst_663_);
lean_inc_n(v_a_666_, 2);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_668_, 0, v_f_665_);
lean_closure_set(v___f_668_, 1, v_a_666_);
v___x_669_ = lean_apply_1(v_x_664_, v_a_666_);
v___x_670_ = lean_apply_4(v_toBind_667_, lean_box(0), lean_box(0), v___x_669_, v___f_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(lean_object* v_inst_671_, lean_object* v_x_672_, lean_object* v_f_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(v_inst_671_, v_x_672_, v_f_673_, v_a_674_);
lean_dec(v_a_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13(lean_object* v_00_u03c9_676_, lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_m_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_f_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_toBind_689_; lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_toBind_689_ = lean_ctor_get(v_inst_683_, 1);
lean_inc(v_toBind_689_);
lean_dec_ref(v_inst_683_);
lean_inc_n(v_a_688_, 2);
v___f_690_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_690_, 0, v_f_687_);
lean_closure_set(v___f_690_, 1, v_a_688_);
v___x_691_ = lean_apply_1(v_x_686_, v_a_688_);
v___x_692_ = lean_apply_4(v_toBind_689_, lean_box(0), lean_box(0), v___x_691_, v___f_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03c9_693_, lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_m_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_x_703_, lean_object* v_f_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_MonadCacheT_instMonad___aux__13(v_00_u03c9_693_, v_00_u03b1_694_, v_00_u03b2_695_, v_m_696_, v_inst_697_, v_inst_698_, v_inst_699_, v_inst_700_, v_00_u03b1_701_, v_00_u03b2_702_, v_x_703_, v_f_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_inst_699_);
lean_dec_ref(v_inst_698_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_inc_ref_n(v_inst_710_, 6);
lean_inc_ref_n(v_inst_709_, 6);
lean_inc_ref_n(v_inst_708_, 6);
v___x_711_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__1___boxed), 13, 8);
lean_closure_set(v___x_711_, 0, lean_box(0));
lean_closure_set(v___x_711_, 1, lean_box(0));
lean_closure_set(v___x_711_, 2, lean_box(0));
lean_closure_set(v___x_711_, 3, lean_box(0));
lean_closure_set(v___x_711_, 4, v_inst_707_);
lean_closure_set(v___x_711_, 5, v_inst_708_);
lean_closure_set(v___x_711_, 6, v_inst_709_);
lean_closure_set(v___x_711_, 7, v_inst_710_);
v___x_712_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__3___boxed), 13, 8);
lean_closure_set(v___x_712_, 0, lean_box(0));
lean_closure_set(v___x_712_, 1, lean_box(0));
lean_closure_set(v___x_712_, 2, lean_box(0));
lean_closure_set(v___x_712_, 3, lean_box(0));
lean_closure_set(v___x_712_, 4, v_inst_707_);
lean_closure_set(v___x_712_, 5, v_inst_708_);
lean_closure_set(v___x_712_, 6, v_inst_709_);
lean_closure_set(v___x_712_, 7, v_inst_710_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__5___boxed), 11, 8);
lean_closure_set(v___x_714_, 0, lean_box(0));
lean_closure_set(v___x_714_, 1, lean_box(0));
lean_closure_set(v___x_714_, 2, lean_box(0));
lean_closure_set(v___x_714_, 3, lean_box(0));
lean_closure_set(v___x_714_, 4, v_inst_707_);
lean_closure_set(v___x_714_, 5, v_inst_708_);
lean_closure_set(v___x_714_, 6, v_inst_709_);
lean_closure_set(v___x_714_, 7, v_inst_710_);
v___x_715_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___boxed), 13, 8);
lean_closure_set(v___x_715_, 0, lean_box(0));
lean_closure_set(v___x_715_, 1, lean_box(0));
lean_closure_set(v___x_715_, 2, lean_box(0));
lean_closure_set(v___x_715_, 3, lean_box(0));
lean_closure_set(v___x_715_, 4, v_inst_707_);
lean_closure_set(v___x_715_, 5, v_inst_708_);
lean_closure_set(v___x_715_, 6, v_inst_709_);
lean_closure_set(v___x_715_, 7, v_inst_710_);
v___x_716_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__9___boxed), 13, 8);
lean_closure_set(v___x_716_, 0, lean_box(0));
lean_closure_set(v___x_716_, 1, lean_box(0));
lean_closure_set(v___x_716_, 2, lean_box(0));
lean_closure_set(v___x_716_, 3, lean_box(0));
lean_closure_set(v___x_716_, 4, v_inst_707_);
lean_closure_set(v___x_716_, 5, v_inst_708_);
lean_closure_set(v___x_716_, 6, v_inst_709_);
lean_closure_set(v___x_716_, 7, v_inst_710_);
v___x_717_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__11___boxed), 13, 8);
lean_closure_set(v___x_717_, 0, lean_box(0));
lean_closure_set(v___x_717_, 1, lean_box(0));
lean_closure_set(v___x_717_, 2, lean_box(0));
lean_closure_set(v___x_717_, 3, lean_box(0));
lean_closure_set(v___x_717_, 4, v_inst_707_);
lean_closure_set(v___x_717_, 5, v_inst_708_);
lean_closure_set(v___x_717_, 6, v_inst_709_);
lean_closure_set(v___x_717_, 7, v_inst_710_);
v___x_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
lean_ctor_set(v___x_718_, 1, v___x_714_);
lean_ctor_set(v___x_718_, 2, v___x_715_);
lean_ctor_set(v___x_718_, 3, v___x_716_);
lean_ctor_set(v___x_718_, 4, v___x_717_);
v___x_719_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 8);
lean_closure_set(v___x_719_, 0, lean_box(0));
lean_closure_set(v___x_719_, 1, lean_box(0));
lean_closure_set(v___x_719_, 2, lean_box(0));
lean_closure_set(v___x_719_, 3, lean_box(0));
lean_closure_set(v___x_719_, 4, v_inst_707_);
lean_closure_set(v___x_719_, 5, v_inst_708_);
lean_closure_set(v___x_719_, 6, v_inst_709_);
lean_closure_set(v___x_719_, 7, v_inst_710_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad(lean_object* v_00_u03c9_721_, lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_m_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_MonadCacheT_instMonad___redArg(v_inst_725_, v_inst_726_, v_inst_727_, v_inst_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(lean_object* v_x_730_){
_start:
{
lean_inc(v_x_730_);
return v_x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(v_x_731_);
lean_dec(v_x_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1(lean_object* v_00_u03c9_733_, lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_m_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_00_u03b1_740_, lean_object* v_x_741_, lean_object* v_a_742_){
_start:
{
lean_inc(v_x_741_);
return v_x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(lean_object* v_00_u03c9_743_, lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_00_u03b1_750_, lean_object* v_x_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_MonadCacheT_instMonadLift___aux__1(v_00_u03c9_743_, v_00_u03b1_744_, v_00_u03b2_745_, v_m_746_, v_inst_747_, v_inst_748_, v_inst_749_, v_00_u03b1_750_, v_x_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec(v_x_751_);
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_inst_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___redArg(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 7);
lean_closure_set(v___x_757_, 0, lean_box(0));
lean_closure_set(v___x_757_, 1, lean_box(0));
lean_closure_set(v___x_757_, 2, lean_box(0));
lean_closure_set(v___x_757_, 3, lean_box(0));
lean_closure_set(v___x_757_, 4, v_inst_754_);
lean_closure_set(v___x_757_, 5, v_inst_755_);
lean_closure_set(v___x_757_, 6, v_inst_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift(lean_object* v_00_u03c9_758_, lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_m_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 7);
lean_closure_set(v___x_765_, 0, lean_box(0));
lean_closure_set(v___x_765_, 1, lean_box(0));
lean_closure_set(v___x_765_, 2, lean_box(0));
lean_closure_set(v___x_765_, 3, lean_box(0));
lean_closure_set(v___x_765_, 4, v_inst_762_);
lean_closure_set(v___x_765_, 5, v_inst_763_);
lean_closure_set(v___x_765_, 6, v_inst_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(lean_object* v_inst_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_throw_768_; lean_object* v___x_769_; 
v_throw_768_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_throw_768_);
lean_dec_ref(v_inst_766_);
v___x_769_ = lean_apply_2(v_throw_768_, lean_box(0), v_a_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1(lean_object* v_00_u03c9_770_, lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_00_u03b5_777_, lean_object* v_inst_778_, lean_object* v_00_u03b1_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_throw_782_; lean_object* v___x_783_; 
v_throw_782_ = lean_ctor_get(v_inst_778_, 0);
lean_inc(v_throw_782_);
lean_dec_ref(v_inst_778_);
v___x_783_ = lean_apply_2(v_throw_782_, lean_box(0), v_a_780_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(lean_object* v_00_u03c9_784_, lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_00_u03b5_791_, lean_object* v_inst_792_, lean_object* v_00_u03b1_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__1(v_00_u03c9_784_, v_00_u03b1_785_, v_00_u03b2_786_, v_m_787_, v_inst_788_, v_inst_789_, v_inst_790_, v_00_u03b5_791_, v_inst_792_, v_00_u03b1_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_inst_790_);
lean_dec_ref(v_inst_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object* v_c_797_, lean_object* v_s_798_, lean_object* v_e_799_){
_start:
{
lean_object* v___x_800_; 
lean_inc(v_s_798_);
v___x_800_ = lean_apply_2(v_c_797_, v_e_799_, v_s_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(lean_object* v_c_801_, lean_object* v_s_802_, lean_object* v_e_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(v_c_801_, v_s_802_, v_e_803_);
lean_dec(v_s_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(lean_object* v_inst_805_, lean_object* v_x_806_, lean_object* v_c_807_, lean_object* v_s_808_){
_start:
{
lean_object* v_tryCatch_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_tryCatch_809_ = lean_ctor_get(v_inst_805_, 1);
lean_inc(v_tryCatch_809_);
lean_dec_ref(v_inst_805_);
lean_inc_n(v_s_808_, 2);
v___f_810_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_810_, 0, v_c_807_);
lean_closure_set(v___f_810_, 1, v_s_808_);
v___x_811_ = lean_apply_1(v_x_806_, v_s_808_);
v___x_812_ = lean_apply_3(v_tryCatch_809_, lean_box(0), v___x_811_, v___f_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(lean_object* v_inst_813_, lean_object* v_x_814_, lean_object* v_c_815_, lean_object* v_s_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(v_inst_813_, v_x_814_, v_c_815_, v_s_816_);
lean_dec(v_s_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3(lean_object* v_00_u03c9_818_, lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_m_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_00_u03b5_825_, lean_object* v_inst_826_, lean_object* v_00_u03b1_827_, lean_object* v_x_828_, lean_object* v_c_829_, lean_object* v_s_830_){
_start:
{
lean_object* v_tryCatch_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_tryCatch_831_ = lean_ctor_get(v_inst_826_, 1);
lean_inc(v_tryCatch_831_);
lean_dec_ref(v_inst_826_);
lean_inc_n(v_s_830_, 2);
v___f_832_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_832_, 0, v_c_829_);
lean_closure_set(v___f_832_, 1, v_s_830_);
v___x_833_ = lean_apply_1(v_x_828_, v_s_830_);
v___x_834_ = lean_apply_3(v_tryCatch_831_, lean_box(0), v___x_833_, v___f_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(lean_object* v_00_u03c9_835_, lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_m_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_00_u03b5_842_, lean_object* v_inst_843_, lean_object* v_00_u03b1_844_, lean_object* v_x_845_, lean_object* v_c_846_, lean_object* v_s_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3(v_00_u03c9_835_, v_00_u03b1_836_, v_00_u03b2_837_, v_m_838_, v_inst_839_, v_inst_840_, v_inst_841_, v_00_u03b5_842_, v_inst_843_, v_00_u03b1_844_, v_x_845_, v_c_846_, v_s_847_);
lean_dec(v_s_847_);
lean_dec_ref(v_inst_841_);
lean_dec_ref(v_inst_840_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_inc_ref(v_inst_852_);
lean_inc_ref(v_inst_851_);
lean_inc_ref(v_inst_850_);
v___x_853_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed), 12, 9);
lean_closure_set(v___x_853_, 0, lean_box(0));
lean_closure_set(v___x_853_, 1, lean_box(0));
lean_closure_set(v___x_853_, 2, lean_box(0));
lean_closure_set(v___x_853_, 3, lean_box(0));
lean_closure_set(v___x_853_, 4, v_inst_849_);
lean_closure_set(v___x_853_, 5, v_inst_850_);
lean_closure_set(v___x_853_, 6, v_inst_851_);
lean_closure_set(v___x_853_, 7, lean_box(0));
lean_closure_set(v___x_853_, 8, v_inst_852_);
v___x_854_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed), 13, 9);
lean_closure_set(v___x_854_, 0, lean_box(0));
lean_closure_set(v___x_854_, 1, lean_box(0));
lean_closure_set(v___x_854_, 2, lean_box(0));
lean_closure_set(v___x_854_, 3, lean_box(0));
lean_closure_set(v___x_854_, 4, v_inst_849_);
lean_closure_set(v___x_854_, 5, v_inst_850_);
lean_closure_set(v___x_854_, 6, v_inst_851_);
lean_closure_set(v___x_854_, 7, lean_box(0));
lean_closure_set(v___x_854_, 8, v_inst_852_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf(lean_object* v_00_u03c9_856_, lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_m_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_00_u03b5_863_, lean_object* v_inst_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_860_, v_inst_861_, v_inst_862_, v_inst_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object* v_a_866_, lean_object* v_00_u03b2_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
lean_inc(v_a_866_);
v___x_869_ = lean_apply_1(v_x_868_, v_a_866_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(lean_object* v_a_870_, lean_object* v_00_u03b2_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(v_a_870_, v_00_u03b2_871_, v_x_872_);
lean_dec(v_a_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; 
lean_inc(v_a_875_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_876_, 0, v_a_875_);
v___x_877_ = lean_apply_1(v_a_874_, v___f_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(v_a_878_, v_a_879_);
lean_dec(v_a_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1(lean_object* v_00_u03c9_881_, lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_m_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_00_u03b1_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___f_891_; lean_object* v___x_892_; 
lean_inc(v_a_890_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_891_, 0, v_a_890_);
v___x_892_ = lean_apply_1(v_a_889_, v___f_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(lean_object* v_00_u03c9_893_, lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_m_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_00_u03b1_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_MonadCacheT_instMonadControl___aux__1(v_00_u03c9_893_, v_00_u03b1_894_, v_00_u03b2_895_, v_m_896_, v_inst_897_, v_inst_898_, v_inst_899_, v_00_u03b1_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_inst_899_);
lean_dec_ref(v_inst_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(lean_object* v_a_904_){
_start:
{
lean_inc(v_a_904_);
return v_a_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(v_a_905_);
lean_dec(v_a_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3(lean_object* v_00_u03c9_907_, lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_00_u03b1_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_inc(v_a_915_);
return v_a_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(lean_object* v_00_u03c9_917_, lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_00_u03b1_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_MonadCacheT_instMonadControl___aux__3(v_00_u03c9_917_, v_00_u03b1_918_, v_00_u03b2_919_, v_m_920_, v_inst_921_, v_inst_922_, v_inst_923_, v_00_u03b1_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_inst_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_inc_ref(v_inst_930_);
lean_inc_ref(v_inst_929_);
v___x_931_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___boxed), 10, 7);
lean_closure_set(v___x_931_, 0, lean_box(0));
lean_closure_set(v___x_931_, 1, lean_box(0));
lean_closure_set(v___x_931_, 2, lean_box(0));
lean_closure_set(v___x_931_, 3, lean_box(0));
lean_closure_set(v___x_931_, 4, v_inst_928_);
lean_closure_set(v___x_931_, 5, v_inst_929_);
lean_closure_set(v___x_931_, 6, v_inst_930_);
v___x_932_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__3___boxed), 10, 7);
lean_closure_set(v___x_932_, 0, lean_box(0));
lean_closure_set(v___x_932_, 1, lean_box(0));
lean_closure_set(v___x_932_, 2, lean_box(0));
lean_closure_set(v___x_932_, 3, lean_box(0));
lean_closure_set(v___x_932_, 4, v_inst_928_);
lean_closure_set(v___x_932_, 5, v_inst_929_);
lean_closure_set(v___x_932_, 6, v_inst_930_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl(lean_object* v_00_u03c9_934_, lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_m_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_inst_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_inst_938_, v_inst_939_, v_inst_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object* v_f_942_, lean_object* v_a_943_, lean_object* v_a_x3f_944_){
_start:
{
lean_object* v___x_945_; 
lean_inc(v_a_943_);
v___x_945_ = lean_apply_2(v_f_942_, v_a_x3f_944_, v_a_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(lean_object* v_f_946_, lean_object* v_a_947_, lean_object* v_a_x3f_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(v_f_946_, v_a_947_, v_a_x3f_948_);
lean_dec(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(lean_object* v_inst_950_, lean_object* v_x_951_, lean_object* v_f_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_inc_n(v_a_953_, 2);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_954_, 0, v_f_952_);
lean_closure_set(v___f_954_, 1, v_a_953_);
v___x_955_ = lean_apply_1(v_x_951_, v_a_953_);
v___x_956_ = lean_apply_4(v_inst_950_, lean_box(0), lean_box(0), v___x_955_, v___f_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(lean_object* v_inst_957_, lean_object* v_x_958_, lean_object* v_f_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(v_inst_957_, v_x_958_, v_f_959_, v_a_960_);
lean_dec(v_a_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1(lean_object* v_00_u03c9_962_, lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_m_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_f_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc_n(v_a_974_, 2);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_975_, 0, v_f_973_);
lean_closure_set(v___f_975_, 1, v_a_974_);
v___x_976_ = lean_apply_1(v_x_972_, v_a_974_);
v___x_977_ = lean_apply_4(v_inst_969_, lean_box(0), lean_box(0), v___x_976_, v___f_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(lean_object* v_00_u03c9_978_, lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_f_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_MonadCacheT_instMonadFinally___aux__1(v_00_u03c9_978_, v_00_u03b1_979_, v_00_u03b2_980_, v_m_981_, v_inst_982_, v_inst_983_, v_inst_984_, v_inst_985_, v_00_u03b1_986_, v_00_u03b2_987_, v_x_988_, v_f_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_inst_984_);
lean_dec_ref(v_inst_983_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___redArg(lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed), 13, 8);
lean_closure_set(v___x_996_, 0, lean_box(0));
lean_closure_set(v___x_996_, 1, lean_box(0));
lean_closure_set(v___x_996_, 2, lean_box(0));
lean_closure_set(v___x_996_, 3, lean_box(0));
lean_closure_set(v___x_996_, 4, v_inst_992_);
lean_closure_set(v___x_996_, 5, v_inst_993_);
lean_closure_set(v___x_996_, 6, v_inst_994_);
lean_closure_set(v___x_996_, 7, v_inst_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally(lean_object* v_00_u03c9_997_, lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_m_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed), 13, 8);
lean_closure_set(v___x_1005_, 0, lean_box(0));
lean_closure_set(v___x_1005_, 1, lean_box(0));
lean_closure_set(v___x_1005_, 2, lean_box(0));
lean_closure_set(v___x_1005_, 3, lean_box(0));
lean_closure_set(v___x_1005_, 4, v_inst_1001_);
lean_closure_set(v___x_1005_, 5, v_inst_1002_);
lean_closure_set(v___x_1005_, 6, v_inst_1003_);
lean_closure_set(v___x_1005_, 7, v_inst_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(lean_object* v_inst_1006_){
_start:
{
lean_object* v_getRef_1007_; 
v_getRef_1007_ = lean_ctor_get(v_inst_1006_, 0);
lean_inc(v_getRef_1007_);
return v_getRef_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(lean_object* v_inst_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(v_inst_1008_);
lean_dec_ref(v_inst_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1(lean_object* v_00_u03c9_1010_, lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_getRef_1019_; 
v_getRef_1019_ = lean_ctor_get(v_inst_1017_, 0);
lean_inc(v_getRef_1019_);
return v_getRef_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(lean_object* v_00_u03c9_1020_, lean_object* v_00_u03b1_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_m_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_MonadCacheT_instMonadRef___aux__1(v_00_u03c9_1020_, v_00_u03b1_1021_, v_00_u03b2_1022_, v_m_1023_, v_inst_1024_, v_inst_1025_, v_inst_1026_, v_inst_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_inst_1027_);
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_inst_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(lean_object* v_inst_1030_, lean_object* v_ref_1031_, lean_object* v_x_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_withRef_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_withRef_1034_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc(v_withRef_1034_);
lean_dec_ref(v_inst_1030_);
lean_inc(v_a_1033_);
v___x_1035_ = lean_apply_1(v_x_1032_, v_a_1033_);
v___x_1036_ = lean_apply_3(v_withRef_1034_, lean_box(0), v_ref_1031_, v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(lean_object* v_inst_1037_, lean_object* v_ref_1038_, lean_object* v_x_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(v_inst_1037_, v_ref_1038_, v_x_1039_, v_a_1040_);
lean_dec(v_a_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3(lean_object* v_00_u03c9_1042_, lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_m_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_00_u03b1_1050_, lean_object* v_ref_1051_, lean_object* v_x_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_withRef_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_withRef_1054_ = lean_ctor_get(v_inst_1049_, 1);
lean_inc(v_withRef_1054_);
lean_dec_ref(v_inst_1049_);
lean_inc(v_a_1053_);
v___x_1055_ = lean_apply_1(v_x_1052_, v_a_1053_);
v___x_1056_ = lean_apply_3(v_withRef_1054_, lean_box(0), v_ref_1051_, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(lean_object* v_00_u03c9_1057_, lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_m_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_00_u03b1_1065_, lean_object* v_ref_1066_, lean_object* v_x_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_MonadCacheT_instMonadRef___aux__3(v_00_u03c9_1057_, v_00_u03b1_1058_, v_00_u03b2_1059_, v_m_1060_, v_inst_1061_, v_inst_1062_, v_inst_1063_, v_inst_1064_, v_00_u03b1_1065_, v_ref_1066_, v_x_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_inst_1063_);
lean_dec_ref(v_inst_1062_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___redArg(lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc_ref(v_inst_1073_);
lean_inc_ref(v_inst_1072_);
lean_inc_ref(v_inst_1071_);
v___x_1074_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadRef___aux__1___boxed), 9, 8);
lean_closure_set(v___x_1074_, 0, lean_box(0));
lean_closure_set(v___x_1074_, 1, lean_box(0));
lean_closure_set(v___x_1074_, 2, lean_box(0));
lean_closure_set(v___x_1074_, 3, lean_box(0));
lean_closure_set(v___x_1074_, 4, v_inst_1070_);
lean_closure_set(v___x_1074_, 5, v_inst_1071_);
lean_closure_set(v___x_1074_, 6, v_inst_1072_);
lean_closure_set(v___x_1074_, 7, v_inst_1073_);
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadRef___aux__3___boxed), 12, 8);
lean_closure_set(v___x_1075_, 0, lean_box(0));
lean_closure_set(v___x_1075_, 1, lean_box(0));
lean_closure_set(v___x_1075_, 2, lean_box(0));
lean_closure_set(v___x_1075_, 3, lean_box(0));
lean_closure_set(v___x_1075_, 4, v_inst_1070_);
lean_closure_set(v___x_1075_, 5, v_inst_1071_);
lean_closure_set(v___x_1075_, 6, v_inst_1072_);
lean_closure_set(v___x_1075_, 7, v_inst_1073_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef(lean_object* v_00_u03c9_1077_, lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_m_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_MonadCacheT_instMonadRef___redArg(v_inst_1081_, v_inst_1082_, v_inst_1083_, v_inst_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___redArg(lean_object* v_inst_1086_){
_start:
{
lean_object* v_failure_1087_; lean_object* v___x_1088_; 
v_failure_1087_ = lean_ctor_get(v_inst_1086_, 1);
lean_inc(v_failure_1087_);
lean_dec_ref(v_inst_1086_);
v___x_1088_ = lean_apply_1(v_failure_1087_, lean_box(0));
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1(lean_object* v_00_u03c9_1089_, lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_00_u03b1_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_failure_1099_; lean_object* v___x_1100_; 
v_failure_1099_ = lean_ctor_get(v_inst_1096_, 1);
lean_inc(v_failure_1099_);
lean_dec_ref(v_inst_1096_);
v___x_1100_ = lean_apply_1(v_failure_1099_, lean_box(0));
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___boxed(lean_object* v_00_u03c9_1101_, lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_m_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_00_u03b1_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_MonadCacheT_instAlternative___aux__1(v_00_u03c9_1101_, v_00_u03b1_1102_, v_00_u03b2_1103_, v_m_1104_, v_inst_1105_, v_inst_1106_, v_inst_1107_, v_inst_1108_, v_00_u03b1_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_inst_1107_);
lean_dec_ref(v_inst_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0(lean_object* v_x_u2082_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(0);
lean_inc(v_a_1113_);
v___x_1116_ = lean_apply_2(v_x_u2082_1112_, v___x_1115_, v_a_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed(lean_object* v_x_u2082_1117_, lean_object* v_a_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0(v_x_u2082_1117_, v_a_1118_, v_x_1119_);
lean_dec(v_a_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg(lean_object* v_inst_1121_, lean_object* v_x_u2081_1122_, lean_object* v_x_u2082_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_orElse_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_orElse_1125_ = lean_ctor_get(v_inst_1121_, 2);
lean_inc(v_orElse_1125_);
lean_dec_ref(v_inst_1121_);
lean_inc_n(v_a_1124_, 2);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1126_, 0, v_x_u2082_1123_);
lean_closure_set(v___f_1126_, 1, v_a_1124_);
v___x_1127_ = lean_apply_1(v_x_u2081_1122_, v_a_1124_);
v___x_1128_ = lean_apply_3(v_orElse_1125_, lean_box(0), v___x_1127_, v___f_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(lean_object* v_inst_1129_, lean_object* v_x_u2081_1130_, lean_object* v_x_u2082_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(v_inst_1129_, v_x_u2081_1130_, v_x_u2082_1131_, v_a_1132_);
lean_dec(v_a_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3(lean_object* v_00_u03c9_1134_, lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_m_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_00_u03b1_1142_, lean_object* v_x_u2081_1143_, lean_object* v_x_u2082_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_orElse_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_orElse_1146_ = lean_ctor_get(v_inst_1141_, 2);
lean_inc(v_orElse_1146_);
lean_dec_ref(v_inst_1141_);
lean_inc_n(v_a_1145_, 2);
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1147_, 0, v_x_u2082_1144_);
lean_closure_set(v___f_1147_, 1, v_a_1145_);
v___x_1148_ = lean_apply_1(v_x_u2081_1143_, v_a_1145_);
v___x_1149_ = lean_apply_3(v_orElse_1146_, lean_box(0), v___x_1148_, v___f_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___boxed(lean_object* v_00_u03c9_1150_, lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_m_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_00_u03b1_1158_, lean_object* v_x_u2081_1159_, lean_object* v_x_u2082_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_MonadCacheT_instAlternative___aux__3(v_00_u03c9_1150_, v_00_u03b1_1151_, v_00_u03b2_1152_, v_m_1153_, v_inst_1154_, v_inst_1155_, v_inst_1156_, v_inst_1157_, v_00_u03b1_1158_, v_x_u2081_1159_, v_x_u2082_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_inst_1156_);
lean_dec_ref(v_inst_1155_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v_toApplicative_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_inc_ref_n(v_inst_1165_, 2);
lean_inc_ref_n(v_inst_1164_, 2);
v___x_1168_ = l_Lean_MonadCacheT_instMonad___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_);
v_toApplicative_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_toApplicative_1169_);
lean_dec_ref(v___x_1168_);
lean_inc_ref(v_inst_1167_);
v___x_1170_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__1___boxed), 10, 8);
lean_closure_set(v___x_1170_, 0, lean_box(0));
lean_closure_set(v___x_1170_, 1, lean_box(0));
lean_closure_set(v___x_1170_, 2, lean_box(0));
lean_closure_set(v___x_1170_, 3, lean_box(0));
lean_closure_set(v___x_1170_, 4, v_inst_1163_);
lean_closure_set(v___x_1170_, 5, v_inst_1164_);
lean_closure_set(v___x_1170_, 6, v_inst_1165_);
lean_closure_set(v___x_1170_, 7, v_inst_1167_);
v___x_1171_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___boxed), 12, 8);
lean_closure_set(v___x_1171_, 0, lean_box(0));
lean_closure_set(v___x_1171_, 1, lean_box(0));
lean_closure_set(v___x_1171_, 2, lean_box(0));
lean_closure_set(v___x_1171_, 3, lean_box(0));
lean_closure_set(v___x_1171_, 4, v_inst_1163_);
lean_closure_set(v___x_1171_, 5, v_inst_1164_);
lean_closure_set(v___x_1171_, 6, v_inst_1165_);
lean_closure_set(v___x_1171_, 7, v_inst_1167_);
v___x_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_toApplicative_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object* v_00_u03c9_1173_, lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_MonadCacheT_instAlternative___redArg(v_inst_1177_, v_inst_1178_, v_inst_1179_, v_inst_1180_, v_inst_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_inst_1183_, lean_object* v_f_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_toApplicative_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1197_; 
v_toApplicative_1186_ = lean_ctor_get(v_inst_1183_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_inst_1183_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v_inst_1183_, 1);
lean_dec(v_unused_1198_);
v___x_1188_ = v_inst_1183_;
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_toApplicative_1186_);
lean_dec(v_inst_1183_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_toPure_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1186_, 1);
lean_inc(v_toPure_1190_);
lean_dec_ref(v_toApplicative_1186_);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_apply_1(v_f_1184_, v___y_1185_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1192_);
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_apply_2(v_toPure_1190_, lean_box(0), v___x_1194_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_1199_){
_start:
{
lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_inc_ref(v_inst_1199_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1200_, 0, v_inst_1199_);
v___x_1201_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_1201_, 0, lean_box(0));
lean_closure_set(v___x_1201_, 1, lean_box(0));
lean_closure_set(v___x_1201_, 2, v_inst_1199_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___f_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_m_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(v_00_u03b1_1210_, v_00_u03b2_1211_, v_m_1212_, v_inst_1213_, v_inst_1214_, v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec_ref(v_inst_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0(lean_object* v_x_1217_){
_start:
{
lean_object* v_fst_1218_; 
v_fst_1218_ = lean_ctor_get(v_x_1217_, 0);
lean_inc(v_fst_1218_);
return v_fst_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(lean_object* v_x_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_1219_);
lean_dec_ref(v_x_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg(lean_object* v_inst_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_toApplicative_1224_; lean_object* v_toFunctor_1225_; lean_object* v_map_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_toApplicative_1224_ = lean_ctor_get(v_inst_1222_, 0);
lean_inc_ref(v_toApplicative_1224_);
lean_dec_ref(v_inst_1222_);
v_toFunctor_1225_ = lean_ctor_get(v_toApplicative_1224_, 0);
lean_inc_ref(v_toFunctor_1225_);
lean_dec_ref(v_toApplicative_1224_);
v_map_1226_ = lean_ctor_get(v_toFunctor_1225_, 0);
lean_inc(v_map_1226_);
lean_dec_ref(v_toFunctor_1225_);
v___f_1227_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1228_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
v___x_1229_ = lean_apply_1(v_x_1223_, v___x_1228_);
v___x_1230_ = lean_apply_4(v_map_1226_, lean_box(0), lean_box(0), v___f_1227_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_00_u03c3_1237_, lean_object* v_x_1238_){
_start:
{
lean_object* v_toApplicative_1239_; lean_object* v_toFunctor_1240_; lean_object* v_map_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_toApplicative_1239_ = lean_ctor_get(v_inst_1236_, 0);
lean_inc_ref(v_toApplicative_1239_);
lean_dec_ref(v_inst_1236_);
v_toFunctor_1240_ = lean_ctor_get(v_toApplicative_1239_, 0);
lean_inc_ref(v_toFunctor_1240_);
lean_dec_ref(v_toApplicative_1239_);
v_map_1241_ = lean_ctor_get(v_toFunctor_1240_, 0);
lean_inc(v_map_1241_);
lean_dec_ref(v_toFunctor_1240_);
v___f_1242_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1243_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
v___x_1244_ = lean_apply_1(v_x_1238_, v___x_1243_);
v___x_1245_ = lean_apply_4(v_map_1241_, lean_box(0), lean_box(0), v___f_1242_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_m_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_00_u03c3_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_MonadStateCacheT_run(v_00_u03b1_1246_, v_00_u03b2_1247_, v_m_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_00_u03c3_1252_, v_x_1253_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_inst_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(lean_object* v_f_1255_, lean_object* v_toPure_1256_, lean_object* v_____x_1257_){
_start:
{
lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v_fst_1258_ = lean_ctor_get(v_____x_1257_, 0);
v_snd_1259_ = lean_ctor_get(v_____x_1257_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_____x_1257_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v_____x_1257_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v_____x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_apply_1(v_f_1255_, v_fst_1258_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_snd_1259_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_apply_2(v_toPure_1256_, lean_box(0), v___x_1265_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(lean_object* v_inst_1269_, lean_object* v_f_1270_, lean_object* v_x_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_toApplicative_1273_; lean_object* v_toBind_1274_; lean_object* v_toPure_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; 
v_toApplicative_1273_ = lean_ctor_get(v_inst_1269_, 0);
lean_inc_ref(v_toApplicative_1273_);
v_toBind_1274_ = lean_ctor_get(v_inst_1269_, 1);
lean_inc(v_toBind_1274_);
lean_dec_ref(v_inst_1269_);
v_toPure_1275_ = lean_ctor_get(v_toApplicative_1273_, 1);
lean_inc(v_toPure_1275_);
lean_dec_ref(v_toApplicative_1273_);
v___x_1276_ = lean_apply_1(v_x_1271_, v_a_1272_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1277_, 0, v_f_1270_);
lean_closure_set(v___f_1277_, 1, v_toPure_1275_);
v___x_1278_ = lean_apply_4(v_toBind_1274_, lean_box(0), lean_box(0), v___x_1276_, v___f_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_f_1287_, lean_object* v_x_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_toApplicative_1290_; lean_object* v_toBind_1291_; lean_object* v_toPure_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; 
v_toApplicative_1290_ = lean_ctor_get(v_inst_1284_, 0);
lean_inc_ref(v_toApplicative_1290_);
v_toBind_1291_ = lean_ctor_get(v_inst_1284_, 1);
lean_inc(v_toBind_1291_);
lean_dec_ref(v_inst_1284_);
v_toPure_1292_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_inc(v_toPure_1292_);
lean_dec_ref(v_toApplicative_1290_);
v___x_1293_ = lean_apply_1(v_x_1288_, v_a_1289_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1294_, 0, v_f_1287_);
lean_closure_set(v___f_1294_, 1, v_toPure_1292_);
v___x_1295_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v___x_1293_, v___f_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_00_u03b2_1297_, lean_object* v_m_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_00_u03b1_1302_, lean_object* v_00_u03b2_1303_, lean_object* v_f_1304_, lean_object* v_x_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_MonadStateCacheT_instMonad___aux__1(v_00_u03b1_1296_, v_00_u03b2_1297_, v_m_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_00_u03b1_1302_, v_00_u03b2_1303_, v_f_1304_, v_x_1305_, v_a_1306_);
lean_dec_ref(v_inst_1300_);
lean_dec_ref(v_inst_1299_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(lean_object* v_a_1308_, lean_object* v_toPure_1309_, lean_object* v_____x_1310_){
_start:
{
lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_snd_1311_ = lean_ctor_get(v_____x_1310_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_____x_1310_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_____x_1310_, 0);
lean_dec(v_unused_1320_);
v___x_1313_ = v_____x_1310_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_dec(v_____x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_a_1308_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_snd_1311_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_apply_2(v_toPure_1309_, lean_box(0), v___x_1316_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(lean_object* v_inst_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_toApplicative_1325_; lean_object* v_toBind_1326_; lean_object* v_toPure_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; 
v_toApplicative_1325_ = lean_ctor_get(v_inst_1321_, 0);
lean_inc_ref(v_toApplicative_1325_);
v_toBind_1326_ = lean_ctor_get(v_inst_1321_, 1);
lean_inc(v_toBind_1326_);
lean_dec_ref(v_inst_1321_);
v_toPure_1327_ = lean_ctor_get(v_toApplicative_1325_, 1);
lean_inc(v_toPure_1327_);
lean_dec_ref(v_toApplicative_1325_);
v___x_1328_ = lean_apply_1(v_a_1323_, v_a_1324_);
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1329_, 0, v_a_1322_);
lean_closure_set(v___f_1329_, 1, v_toPure_1327_);
v___x_1330_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1328_, v___f_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_m_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_toApplicative_1342_; lean_object* v_toBind_1343_; lean_object* v_toPure_1344_; lean_object* v___x_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; 
v_toApplicative_1342_ = lean_ctor_get(v_inst_1336_, 0);
lean_inc_ref(v_toApplicative_1342_);
v_toBind_1343_ = lean_ctor_get(v_inst_1336_, 1);
lean_inc(v_toBind_1343_);
lean_dec_ref(v_inst_1336_);
v_toPure_1344_ = lean_ctor_get(v_toApplicative_1342_, 1);
lean_inc(v_toPure_1344_);
lean_dec_ref(v_toApplicative_1342_);
v___x_1345_ = lean_apply_1(v_a_1340_, v_a_1341_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1346_, 0, v_a_1339_);
lean_closure_set(v___f_1346_, 1, v_toPure_1344_);
v___x_1347_ = lean_apply_4(v_toBind_1343_, lean_box(0), lean_box(0), v___x_1345_, v___f_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_m_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_MonadStateCacheT_instMonad___aux__3(v_00_u03b1_1348_, v_00_u03b2_1349_, v_m_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v_00_u03b1_1354_, v_00_u03b2_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec_ref(v_inst_1352_);
lean_dec_ref(v_inst_1351_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(lean_object* v_inst_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_toApplicative_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1372_; 
v_toApplicative_1363_ = lean_ctor_get(v_inst_1360_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_inst_1360_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_inst_1360_, 1);
lean_dec(v_unused_1373_);
v___x_1365_ = v_inst_1360_;
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_toApplicative_1363_);
lean_dec(v_inst_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_toPure_1367_; lean_object* v___x_1369_; 
v_toPure_1367_ = lean_ctor_get(v_toApplicative_1363_, 1);
lean_inc(v_toPure_1367_);
lean_dec_ref(v_toApplicative_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_a_1362_);
lean_ctor_set(v___x_1365_, 0, v_a_1361_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1361_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1362_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_m_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_00_u03b1_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_toApplicative_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1392_; 
v_toApplicative_1383_ = lean_ctor_get(v_inst_1379_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_inst_1379_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_inst_1379_, 1);
lean_dec(v_unused_1393_);
v___x_1385_ = v_inst_1379_;
v_isShared_1386_ = v_isSharedCheck_1392_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_toApplicative_1383_);
lean_dec(v_inst_1379_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1392_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_toPure_1387_; lean_object* v___x_1389_; 
v_toPure_1387_ = lean_ctor_get(v_toApplicative_1383_, 1);
lean_inc(v_toPure_1387_);
lean_dec_ref(v_toApplicative_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v_a_1382_);
lean_ctor_set(v___x_1385_, 0, v_a_1381_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1381_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_a_1382_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_apply_2(v_toPure_1387_, lean_box(0), v___x_1389_);
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_m_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_00_u03b1_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_MonadStateCacheT_instMonad___aux__5(v_00_u03b1_1394_, v_00_u03b2_1395_, v_m_1396_, v_inst_1397_, v_inst_1398_, v_inst_1399_, v_00_u03b1_1400_, v_a_1401_, v_a_1402_);
lean_dec_ref(v_inst_1398_);
lean_dec_ref(v_inst_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(lean_object* v_fst_1404_, lean_object* v_toPure_1405_, lean_object* v_____x_1406_){
_start:
{
lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1417_; 
v_fst_1407_ = lean_ctor_get(v_____x_1406_, 0);
v_snd_1408_ = lean_ctor_get(v_____x_1406_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_____x_1406_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1410_ = v_____x_1406_;
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_____x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_apply_1(v_fst_1404_, v_fst_1407_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_snd_1408_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_apply_2(v_toPure_1405_, lean_box(0), v___x_1414_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(lean_object* v_toApplicative_1418_, lean_object* v_x_1419_, lean_object* v_toBind_1420_, lean_object* v_____x_1421_){
_start:
{
lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v_toPure_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; 
v_fst_1422_ = lean_ctor_get(v_____x_1421_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v_____x_1421_, 1);
lean_inc(v_snd_1423_);
lean_dec_ref(v_____x_1421_);
v_toPure_1424_ = lean_ctor_get(v_toApplicative_1418_, 1);
lean_inc(v_toPure_1424_);
lean_dec_ref(v_toApplicative_1418_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_apply_2(v_x_1419_, v___x_1425_, v_snd_1423_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1427_, 0, v_fst_1422_);
lean_closure_set(v___f_1427_, 1, v_toPure_1424_);
v___x_1428_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1426_, v___f_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(lean_object* v_inst_1429_, lean_object* v_f_1430_, lean_object* v_x_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_toApplicative_1433_; lean_object* v_toBind_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_toApplicative_1433_ = lean_ctor_get(v_inst_1429_, 0);
lean_inc_ref(v_toApplicative_1433_);
v_toBind_1434_ = lean_ctor_get(v_inst_1429_, 1);
lean_inc_n(v_toBind_1434_, 2);
lean_dec_ref(v_inst_1429_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1435_, 0, v_toApplicative_1433_);
lean_closure_set(v___f_1435_, 1, v_x_1431_);
lean_closure_set(v___f_1435_, 2, v_toBind_1434_);
v___x_1436_ = lean_apply_1(v_f_1430_, v_a_1432_);
v___x_1437_ = lean_apply_4(v_toBind_1434_, lean_box(0), lean_box(0), v___x_1436_, v___f_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_m_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_f_1446_, lean_object* v_x_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_toApplicative_1449_; lean_object* v_toBind_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_toApplicative_1449_ = lean_ctor_get(v_inst_1443_, 0);
lean_inc_ref(v_toApplicative_1449_);
v_toBind_1450_ = lean_ctor_get(v_inst_1443_, 1);
lean_inc_n(v_toBind_1450_, 2);
lean_dec_ref(v_inst_1443_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1451_, 0, v_toApplicative_1449_);
lean_closure_set(v___f_1451_, 1, v_x_1447_);
lean_closure_set(v___f_1451_, 2, v_toBind_1450_);
v___x_1452_ = lean_apply_1(v_f_1446_, v_a_1448_);
v___x_1453_ = lean_apply_4(v_toBind_1450_, lean_box(0), lean_box(0), v___x_1452_, v___f_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_00_u03b2_1455_, lean_object* v_m_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_00_u03b1_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_f_1462_, lean_object* v_x_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_MonadStateCacheT_instMonad___aux__7(v_00_u03b1_1454_, v_00_u03b2_1455_, v_m_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_00_u03b1_1460_, v_00_u03b2_1461_, v_f_1462_, v_x_1463_, v_a_1464_);
lean_dec_ref(v_inst_1458_);
lean_dec_ref(v_inst_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(lean_object* v_toApplicative_1466_, lean_object* v_fst_1467_, lean_object* v_____x_1468_){
_start:
{
lean_object* v_snd_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1478_; 
v_snd_1469_ = lean_ctor_get(v_____x_1468_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_____x_1468_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_____x_1468_, 0);
lean_dec(v_unused_1479_);
v___x_1471_ = v_____x_1468_;
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snd_1469_);
lean_dec(v_____x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_toPure_1473_; lean_object* v___x_1475_; 
v_toPure_1473_ = lean_ctor_get(v_toApplicative_1466_, 1);
lean_inc(v_toPure_1473_);
lean_dec_ref(v_toApplicative_1466_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_fst_1467_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_fst_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_snd_1469_);
v___x_1475_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_apply_2(v_toPure_1473_, lean_box(0), v___x_1475_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(lean_object* v_toApplicative_1480_, lean_object* v_y_1481_, lean_object* v_toBind_1482_, lean_object* v_____x_1483_){
_start:
{
lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_fst_1484_ = lean_ctor_get(v_____x_1483_, 0);
lean_inc(v_fst_1484_);
v_snd_1485_ = lean_ctor_get(v_____x_1483_, 1);
lean_inc(v_snd_1485_);
lean_dec_ref(v_____x_1483_);
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1486_, 0, v_toApplicative_1480_);
lean_closure_set(v___f_1486_, 1, v_fst_1484_);
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_apply_2(v_y_1481_, v___x_1487_, v_snd_1485_);
v___x_1489_ = lean_apply_4(v_toBind_1482_, lean_box(0), lean_box(0), v___x_1488_, v___f_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(lean_object* v_inst_1490_, lean_object* v_x_1491_, lean_object* v_y_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_toApplicative_1494_; lean_object* v_toBind_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_toApplicative_1494_ = lean_ctor_get(v_inst_1490_, 0);
lean_inc_ref(v_toApplicative_1494_);
v_toBind_1495_ = lean_ctor_get(v_inst_1490_, 1);
lean_inc_n(v_toBind_1495_, 2);
lean_dec_ref(v_inst_1490_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1496_, 0, v_toApplicative_1494_);
lean_closure_set(v___f_1496_, 1, v_y_1492_);
lean_closure_set(v___f_1496_, 2, v_toBind_1495_);
v___x_1497_ = lean_apply_1(v_x_1491_, v_a_1493_);
v___x_1498_ = lean_apply_4(v_toBind_1495_, lean_box(0), lean_box(0), v___x_1497_, v___f_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9(lean_object* v_00_u03b1_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_m_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_x_1507_, lean_object* v_y_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_toApplicative_1510_; lean_object* v_toBind_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_toApplicative_1510_ = lean_ctor_get(v_inst_1504_, 0);
lean_inc_ref(v_toApplicative_1510_);
v_toBind_1511_ = lean_ctor_get(v_inst_1504_, 1);
lean_inc_n(v_toBind_1511_, 2);
lean_dec_ref(v_inst_1504_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1512_, 0, v_toApplicative_1510_);
lean_closure_set(v___f_1512_, 1, v_y_1508_);
lean_closure_set(v___f_1512_, 2, v_toBind_1511_);
v___x_1513_ = lean_apply_1(v_x_1507_, v_a_1509_);
v___x_1514_ = lean_apply_4(v_toBind_1511_, lean_box(0), lean_box(0), v___x_1513_, v___f_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_x_1523_, lean_object* v_y_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_MonadStateCacheT_instMonad___aux__9(v_00_u03b1_1515_, v_00_u03b2_1516_, v_m_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_00_u03b1_1521_, v_00_u03b2_1522_, v_x_1523_, v_y_1524_, v_a_1525_);
lean_dec_ref(v_inst_1519_);
lean_dec_ref(v_inst_1518_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(lean_object* v_y_1527_, lean_object* v_____x_1528_){
_start:
{
lean_object* v_snd_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_snd_1529_ = lean_ctor_get(v_____x_1528_, 1);
lean_inc(v_snd_1529_);
lean_dec_ref(v_____x_1528_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_apply_2(v_y_1527_, v___x_1530_, v_snd_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(lean_object* v_inst_1532_, lean_object* v_x_1533_, lean_object* v_y_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_toBind_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_toBind_1536_ = lean_ctor_get(v_inst_1532_, 1);
lean_inc(v_toBind_1536_);
lean_dec_ref(v_inst_1532_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1537_, 0, v_y_1534_);
v___x_1538_ = lean_apply_1(v_x_1533_, v_a_1535_);
v___x_1539_ = lean_apply_4(v_toBind_1536_, lean_box(0), lean_box(0), v___x_1538_, v___f_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11(lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_x_1548_, lean_object* v_y_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_toBind_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_toBind_1551_ = lean_ctor_get(v_inst_1545_, 1);
lean_inc(v_toBind_1551_);
lean_dec_ref(v_inst_1545_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1552_, 0, v_y_1549_);
v___x_1553_ = lean_apply_1(v_x_1548_, v_a_1550_);
v___x_1554_ = lean_apply_4(v_toBind_1551_, lean_box(0), lean_box(0), v___x_1553_, v___f_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_00_u03b1_1561_, lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_y_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_MonadStateCacheT_instMonad___aux__11(v_00_u03b1_1555_, v_00_u03b2_1556_, v_m_1557_, v_inst_1558_, v_inst_1559_, v_inst_1560_, v_00_u03b1_1561_, v_00_u03b2_1562_, v_x_1563_, v_y_1564_, v_a_1565_);
lean_dec_ref(v_inst_1559_);
lean_dec_ref(v_inst_1558_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_f_1567_, lean_object* v_____x_1568_){
_start:
{
lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1571_; 
v_fst_1569_ = lean_ctor_get(v_____x_1568_, 0);
lean_inc(v_fst_1569_);
v_snd_1570_ = lean_ctor_get(v_____x_1568_, 1);
lean_inc(v_snd_1570_);
lean_dec_ref(v_____x_1568_);
v___x_1571_ = lean_apply_2(v_f_1567_, v_fst_1569_, v_snd_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(lean_object* v_inst_1572_, lean_object* v_x_1573_, lean_object* v_f_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_toBind_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_toBind_1576_ = lean_ctor_get(v_inst_1572_, 1);
lean_inc(v_toBind_1576_);
lean_dec_ref(v_inst_1572_);
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1577_, 0, v_f_1574_);
v___x_1578_ = lean_apply_1(v_x_1573_, v_a_1575_);
v___x_1579_ = lean_apply_4(v_toBind_1576_, lean_box(0), lean_box(0), v___x_1578_, v___f_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_m_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_x_1588_, lean_object* v_f_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_toBind_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_toBind_1591_ = lean_ctor_get(v_inst_1585_, 1);
lean_inc(v_toBind_1591_);
lean_dec_ref(v_inst_1585_);
v___f_1592_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1592_, 0, v_f_1589_);
v___x_1593_ = lean_apply_1(v_x_1588_, v_a_1590_);
v___x_1594_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1593_, v___f_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_m_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_00_u03b1_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_f_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_MonadStateCacheT_instMonad___aux__13(v_00_u03b1_1595_, v_00_u03b2_1596_, v_m_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_00_u03b1_1601_, v_00_u03b2_1602_, v_x_1603_, v_f_1604_, v_a_1605_);
lean_dec_ref(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_inc_ref_n(v_inst_1609_, 6);
lean_inc_ref_n(v_inst_1608_, 6);
lean_inc_ref_n(v_inst_1607_, 6);
v___x_1610_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___boxed), 11, 6);
lean_closure_set(v___x_1610_, 0, lean_box(0));
lean_closure_set(v___x_1610_, 1, lean_box(0));
lean_closure_set(v___x_1610_, 2, lean_box(0));
lean_closure_set(v___x_1610_, 3, v_inst_1607_);
lean_closure_set(v___x_1610_, 4, v_inst_1608_);
lean_closure_set(v___x_1610_, 5, v_inst_1609_);
v___x_1611_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___boxed), 11, 6);
lean_closure_set(v___x_1611_, 0, lean_box(0));
lean_closure_set(v___x_1611_, 1, lean_box(0));
lean_closure_set(v___x_1611_, 2, lean_box(0));
lean_closure_set(v___x_1611_, 3, v_inst_1607_);
lean_closure_set(v___x_1611_, 4, v_inst_1608_);
lean_closure_set(v___x_1611_, 5, v_inst_1609_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__5___boxed), 9, 6);
lean_closure_set(v___x_1613_, 0, lean_box(0));
lean_closure_set(v___x_1613_, 1, lean_box(0));
lean_closure_set(v___x_1613_, 2, lean_box(0));
lean_closure_set(v___x_1613_, 3, v_inst_1607_);
lean_closure_set(v___x_1613_, 4, v_inst_1608_);
lean_closure_set(v___x_1613_, 5, v_inst_1609_);
v___x_1614_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___boxed), 11, 6);
lean_closure_set(v___x_1614_, 0, lean_box(0));
lean_closure_set(v___x_1614_, 1, lean_box(0));
lean_closure_set(v___x_1614_, 2, lean_box(0));
lean_closure_set(v___x_1614_, 3, v_inst_1607_);
lean_closure_set(v___x_1614_, 4, v_inst_1608_);
lean_closure_set(v___x_1614_, 5, v_inst_1609_);
v___x_1615_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___boxed), 11, 6);
lean_closure_set(v___x_1615_, 0, lean_box(0));
lean_closure_set(v___x_1615_, 1, lean_box(0));
lean_closure_set(v___x_1615_, 2, lean_box(0));
lean_closure_set(v___x_1615_, 3, v_inst_1607_);
lean_closure_set(v___x_1615_, 4, v_inst_1608_);
lean_closure_set(v___x_1615_, 5, v_inst_1609_);
v___x_1616_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___boxed), 11, 6);
lean_closure_set(v___x_1616_, 0, lean_box(0));
lean_closure_set(v___x_1616_, 1, lean_box(0));
lean_closure_set(v___x_1616_, 2, lean_box(0));
lean_closure_set(v___x_1616_, 3, v_inst_1607_);
lean_closure_set(v___x_1616_, 4, v_inst_1608_);
lean_closure_set(v___x_1616_, 5, v_inst_1609_);
v___x_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1612_);
lean_ctor_set(v___x_1617_, 1, v___x_1613_);
lean_ctor_set(v___x_1617_, 2, v___x_1614_);
lean_ctor_set(v___x_1617_, 3, v___x_1615_);
lean_ctor_set(v___x_1617_, 4, v___x_1616_);
v___x_1618_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___boxed), 11, 6);
lean_closure_set(v___x_1618_, 0, lean_box(0));
lean_closure_set(v___x_1618_, 1, lean_box(0));
lean_closure_set(v___x_1618_, 2, lean_box(0));
lean_closure_set(v___x_1618_, 3, v_inst_1607_);
lean_closure_set(v___x_1618_, 4, v_inst_1608_);
lean_closure_set(v___x_1618_, 5, v_inst_1609_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_1623_, v_inst_1624_, v_inst_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(lean_object* v_a_1627_, lean_object* v_toPure_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_a_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1627_);
v___x_1631_ = lean_apply_2(v_toPure_1628_, lean_box(0), v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(lean_object* v_inst_1632_, lean_object* v_t_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_toApplicative_1635_; lean_object* v_toBind_1636_; lean_object* v_toPure_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; 
v_toApplicative_1635_ = lean_ctor_get(v_inst_1632_, 0);
lean_inc_ref(v_toApplicative_1635_);
v_toBind_1636_ = lean_ctor_get(v_inst_1632_, 1);
lean_inc(v_toBind_1636_);
lean_dec_ref(v_inst_1632_);
v_toPure_1637_ = lean_ctor_get(v_toApplicative_1635_, 1);
lean_inc(v_toPure_1637_);
lean_dec_ref(v_toApplicative_1635_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1638_, 0, v_a_1634_);
lean_closure_set(v___f_1638_, 1, v_toPure_1637_);
v___x_1639_ = lean_apply_4(v_toBind_1636_, lean_box(0), lean_box(0), v_t_1633_, v___f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_m_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_00_u03b1_1646_, lean_object* v_t_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_toApplicative_1649_; lean_object* v_toBind_1650_; lean_object* v_toPure_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; 
v_toApplicative_1649_ = lean_ctor_get(v_inst_1645_, 0);
lean_inc_ref(v_toApplicative_1649_);
v_toBind_1650_ = lean_ctor_get(v_inst_1645_, 1);
lean_inc(v_toBind_1650_);
lean_dec_ref(v_inst_1645_);
v_toPure_1651_ = lean_ctor_get(v_toApplicative_1649_, 1);
lean_inc(v_toPure_1651_);
lean_dec_ref(v_toApplicative_1649_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1652_, 0, v_a_1648_);
lean_closure_set(v___f_1652_, 1, v_toPure_1651_);
v___x_1653_ = lean_apply_4(v_toBind_1650_, lean_box(0), lean_box(0), v_t_1647_, v___f_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_m_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_00_u03b1_1660_, lean_object* v_t_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_MonadStateCacheT_instMonadLift___aux__1(v_00_u03b1_1654_, v_00_u03b2_1655_, v_m_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_00_u03b1_1660_, v_t_1661_, v_a_1662_);
lean_dec_ref(v_inst_1658_);
lean_dec_ref(v_inst_1657_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1667_, 0, lean_box(0));
lean_closure_set(v___x_1667_, 1, lean_box(0));
lean_closure_set(v___x_1667_, 2, lean_box(0));
lean_closure_set(v___x_1667_, 3, v_inst_1664_);
lean_closure_set(v___x_1667_, 4, v_inst_1665_);
lean_closure_set(v___x_1667_, 5, v_inst_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_m_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1674_, 0, lean_box(0));
lean_closure_set(v___x_1674_, 1, lean_box(0));
lean_closure_set(v___x_1674_, 2, lean_box(0));
lean_closure_set(v___x_1674_, 3, v_inst_1671_);
lean_closure_set(v___x_1674_, 4, v_inst_1672_);
lean_closure_set(v___x_1674_, 5, v_inst_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_toApplicative_1679_; lean_object* v_throw_1680_; lean_object* v_toBind_1681_; lean_object* v_toPure_1682_; lean_object* v___x_1683_; lean_object* v___f_1684_; lean_object* v___x_1685_; 
v_toApplicative_1679_ = lean_ctor_get(v_inst_1675_, 0);
lean_inc_ref(v_toApplicative_1679_);
v_throw_1680_ = lean_ctor_get(v_inst_1676_, 0);
lean_inc(v_throw_1680_);
lean_dec_ref(v_inst_1676_);
v_toBind_1681_ = lean_ctor_get(v_inst_1675_, 1);
lean_inc(v_toBind_1681_);
lean_dec_ref(v_inst_1675_);
v_toPure_1682_ = lean_ctor_get(v_toApplicative_1679_, 1);
lean_inc(v_toPure_1682_);
lean_dec_ref(v_toApplicative_1679_);
v___x_1683_ = lean_apply_2(v_throw_1680_, lean_box(0), v_a_1677_);
v___f_1684_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1684_, 0, v_a_1678_);
lean_closure_set(v___f_1684_, 1, v_toPure_1682_);
v___x_1685_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1683_, v___f_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(lean_object* v_00_u03b1_1686_, lean_object* v_00_u03b2_1687_, lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_00_u03b5_1692_, lean_object* v_inst_1693_, lean_object* v_00_u03b1_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_toApplicative_1697_; lean_object* v_throw_1698_; lean_object* v_toBind_1699_; lean_object* v_toPure_1700_; lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; 
v_toApplicative_1697_ = lean_ctor_get(v_inst_1691_, 0);
lean_inc_ref(v_toApplicative_1697_);
v_throw_1698_ = lean_ctor_get(v_inst_1693_, 0);
lean_inc(v_throw_1698_);
lean_dec_ref(v_inst_1693_);
v_toBind_1699_ = lean_ctor_get(v_inst_1691_, 1);
lean_inc(v_toBind_1699_);
lean_dec_ref(v_inst_1691_);
v_toPure_1700_ = lean_ctor_get(v_toApplicative_1697_, 1);
lean_inc(v_toPure_1700_);
lean_dec_ref(v_toApplicative_1697_);
v___x_1701_ = lean_apply_2(v_throw_1698_, lean_box(0), v_a_1695_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1702_, 0, v_a_1696_);
lean_closure_set(v___f_1702_, 1, v_toPure_1700_);
v___x_1703_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1701_, v___f_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_m_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_00_u03b5_1710_, lean_object* v_inst_1711_, lean_object* v_00_u03b1_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(v_00_u03b1_1704_, v_00_u03b2_1705_, v_m_1706_, v_inst_1707_, v_inst_1708_, v_inst_1709_, v_00_u03b5_1710_, v_inst_1711_, v_00_u03b1_1712_, v_a_1713_, v_a_1714_);
lean_dec_ref(v_inst_1708_);
lean_dec_ref(v_inst_1707_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object* v_c_1716_, lean_object* v_s_1717_, lean_object* v_e_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_apply_2(v_c_1716_, v_e_1718_, v_s_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(lean_object* v_inst_1720_, lean_object* v_x_1721_, lean_object* v_c_1722_, lean_object* v_s_1723_){
_start:
{
lean_object* v_tryCatch_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_tryCatch_1724_ = lean_ctor_get(v_inst_1720_, 1);
lean_inc(v_tryCatch_1724_);
lean_dec_ref(v_inst_1720_);
lean_inc_ref(v_s_1723_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1725_, 0, v_c_1722_);
lean_closure_set(v___f_1725_, 1, v_s_1723_);
v___x_1726_ = lean_apply_1(v_x_1721_, v_s_1723_);
v___x_1727_ = lean_apply_3(v_tryCatch_1724_, lean_box(0), v___x_1726_, v___f_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_00_u03b5_1733_, lean_object* v_inst_1734_, lean_object* v_00_u03b1_1735_, lean_object* v_x_1736_, lean_object* v_c_1737_, lean_object* v_s_1738_){
_start:
{
lean_object* v_tryCatch_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_tryCatch_1739_ = lean_ctor_get(v_inst_1734_, 1);
lean_inc(v_tryCatch_1739_);
lean_dec_ref(v_inst_1734_);
lean_inc_ref(v_s_1738_);
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1740_, 0, v_c_1737_);
lean_closure_set(v___f_1740_, 1, v_s_1738_);
v___x_1741_ = lean_apply_1(v_x_1736_, v_s_1738_);
v___x_1742_ = lean_apply_3(v_tryCatch_1739_, lean_box(0), v___x_1741_, v___f_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_m_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_00_u03b5_1748_, lean_object* v_inst_1749_, lean_object* v_00_u03b1_1750_, lean_object* v_x_1751_, lean_object* v_c_1752_, lean_object* v_s_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(v_00_u03b1_1743_, v_00_u03b2_1744_, v_m_1745_, v_inst_1746_, v_inst_1747_, v_00_u03b5_1748_, v_inst_1749_, v_00_u03b1_1750_, v_x_1751_, v_c_1752_, v_s_1753_);
lean_dec_ref(v_inst_1747_);
lean_dec_ref(v_inst_1746_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_inc_ref(v_inst_1758_);
lean_inc_ref(v_inst_1756_);
lean_inc_ref(v_inst_1755_);
v___x_1759_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed), 11, 8);
lean_closure_set(v___x_1759_, 0, lean_box(0));
lean_closure_set(v___x_1759_, 1, lean_box(0));
lean_closure_set(v___x_1759_, 2, lean_box(0));
lean_closure_set(v___x_1759_, 3, v_inst_1755_);
lean_closure_set(v___x_1759_, 4, v_inst_1756_);
lean_closure_set(v___x_1759_, 5, v_inst_1757_);
lean_closure_set(v___x_1759_, 6, lean_box(0));
lean_closure_set(v___x_1759_, 7, v_inst_1758_);
v___x_1760_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed), 11, 7);
lean_closure_set(v___x_1760_, 0, lean_box(0));
lean_closure_set(v___x_1760_, 1, lean_box(0));
lean_closure_set(v___x_1760_, 2, lean_box(0));
lean_closure_set(v___x_1760_, 3, v_inst_1755_);
lean_closure_set(v___x_1760_, 4, v_inst_1756_);
lean_closure_set(v___x_1760_, 5, lean_box(0));
lean_closure_set(v___x_1760_, 6, v_inst_1758_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_m_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_00_u03b5_1768_, lean_object* v_inst_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(v_inst_1765_, v_inst_1766_, v_inst_1767_, v_inst_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object* v_fst_1771_, lean_object* v_00_u03b2_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_apply_1(v_x_1773_, v_fst_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(lean_object* v_snd_1775_, lean_object* v_toPure_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1777_);
lean_ctor_set(v___x_1778_, 1, v_snd_1775_);
v___x_1779_ = lean_apply_2(v_toPure_1776_, lean_box(0), v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(lean_object* v_f_1780_, lean_object* v_toPure_1781_, lean_object* v_toBind_1782_, lean_object* v_____x_1783_){
_start:
{
lean_object* v_fst_1784_; lean_object* v_snd_1785_; lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; 
v_fst_1784_ = lean_ctor_get(v_____x_1783_, 0);
lean_inc(v_fst_1784_);
v_snd_1785_ = lean_ctor_get(v_____x_1783_, 1);
lean_inc(v_snd_1785_);
lean_dec_ref(v_____x_1783_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1786_, 0, v_fst_1784_);
v___x_1787_ = lean_apply_1(v_f_1780_, v___f_1786_);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1788_, 0, v_snd_1785_);
lean_closure_set(v___f_1788_, 1, v_toPure_1781_);
v___x_1789_ = lean_apply_4(v_toBind_1782_, lean_box(0), lean_box(0), v___x_1787_, v___f_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(lean_object* v_inst_1790_, lean_object* v_f_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_toApplicative_1793_; lean_object* v_toBind_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1805_; 
v_toApplicative_1793_ = lean_ctor_get(v_inst_1790_, 0);
v_toBind_1794_ = lean_ctor_get(v_inst_1790_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_inst_1790_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1796_ = v_inst_1790_;
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_toBind_1794_);
lean_inc(v_toApplicative_1793_);
lean_dec(v_inst_1790_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_toPure_1798_; lean_object* v___f_1799_; lean_object* v___x_1801_; 
v_toPure_1798_ = lean_ctor_get(v_toApplicative_1793_, 1);
lean_inc_n(v_toPure_1798_, 2);
lean_dec_ref(v_toApplicative_1793_);
lean_inc(v_toBind_1794_);
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1799_, 0, v_f_1791_);
lean_closure_set(v___f_1799_, 1, v_toPure_1798_);
lean_closure_set(v___f_1799_, 2, v_toBind_1794_);
lean_inc_ref(v_a_1792_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v_a_1792_);
lean_ctor_set(v___x_1796_, 0, v_a_1792_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1792_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_a_1792_);
v___x_1801_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_apply_2(v_toPure_1798_, lean_box(0), v___x_1801_);
v___x_1803_ = lean_apply_4(v_toBind_1794_, lean_box(0), lean_box(0), v___x_1802_, v___f_1799_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1(lean_object* v_00_u03b1_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_m_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_00_u03b1_1812_, lean_object* v_f_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_toApplicative_1815_; lean_object* v_toBind_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1827_; 
v_toApplicative_1815_ = lean_ctor_get(v_inst_1811_, 0);
v_toBind_1816_ = lean_ctor_get(v_inst_1811_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_inst_1811_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1818_ = v_inst_1811_;
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_toBind_1816_);
lean_inc(v_toApplicative_1815_);
lean_dec(v_inst_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_toPure_1820_; lean_object* v___f_1821_; lean_object* v___x_1823_; 
v_toPure_1820_ = lean_ctor_get(v_toApplicative_1815_, 1);
lean_inc_n(v_toPure_1820_, 2);
lean_dec_ref(v_toApplicative_1815_);
lean_inc(v_toBind_1816_);
v___f_1821_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1821_, 0, v_f_1813_);
lean_closure_set(v___f_1821_, 1, v_toPure_1820_);
lean_closure_set(v___f_1821_, 2, v_toBind_1816_);
lean_inc_ref(v_a_1814_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v_a_1814_);
lean_ctor_set(v___x_1818_, 0, v_a_1814_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1814_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1814_);
v___x_1823_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_apply_2(v_toPure_1820_, lean_box(0), v___x_1823_);
v___x_1825_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v___x_1824_, v___f_1821_);
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_m_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_00_u03b1_1834_, lean_object* v_f_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_MonadStateCacheT_instMonadControl___aux__1(v_00_u03b1_1828_, v_00_u03b2_1829_, v_m_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_00_u03b1_1834_, v_f_1835_, v_a_1836_);
lean_dec_ref(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(lean_object* v_fst_1838_, lean_object* v_toPure_1839_, lean_object* v_____x_1840_){
_start:
{
lean_object* v_snd_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
v_snd_1841_ = lean_ctor_get(v_____x_1840_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_____x_1840_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_____x_1840_, 0);
lean_dec(v_unused_1850_);
v___x_1843_ = v_____x_1840_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snd_1841_);
lean_dec(v_____x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_fst_1838_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fst_1838_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_snd_1841_);
v___x_1846_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_apply_2(v_toPure_1839_, lean_box(0), v___x_1846_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(lean_object* v_toPure_1851_, lean_object* v_toBind_1852_, lean_object* v_____x_1853_){
_start:
{
lean_object* v_fst_1854_; lean_object* v_fst_1855_; lean_object* v_snd_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1867_; 
v_fst_1854_ = lean_ctor_get(v_____x_1853_, 0);
lean_inc(v_fst_1854_);
lean_dec_ref(v_____x_1853_);
v_fst_1855_ = lean_ctor_get(v_fst_1854_, 0);
v_snd_1856_ = lean_ctor_get(v_fst_1854_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_fst_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1858_ = v_fst_1854_;
v_isShared_1859_ = v_isSharedCheck_1867_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snd_1856_);
lean_inc(v_fst_1855_);
lean_dec(v_fst_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1867_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_inc(v_toPure_1851_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1860_, 0, v_fst_1855_);
lean_closure_set(v___f_1860_, 1, v_toPure_1851_);
v___x_1861_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_snd_1856_);
v___x_1863_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_apply_2(v_toPure_1851_, lean_box(0), v___x_1863_);
v___x_1865_ = lean_apply_4(v_toBind_1852_, lean_box(0), lean_box(0), v___x_1864_, v___f_1860_);
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2(lean_object* v_a_1868_, lean_object* v_toPure_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1870_);
lean_ctor_set(v___x_1871_, 1, v_a_1868_);
v___x_1872_ = lean_apply_2(v_toPure_1869_, lean_box(0), v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(lean_object* v_inst_1873_, lean_object* v_x_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_toApplicative_1876_; lean_object* v_toBind_1877_; lean_object* v_toPure_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_toApplicative_1876_ = lean_ctor_get(v_inst_1873_, 0);
lean_inc_ref(v_toApplicative_1876_);
v_toBind_1877_ = lean_ctor_get(v_inst_1873_, 1);
lean_inc_n(v_toBind_1877_, 3);
lean_dec_ref(v_inst_1873_);
v_toPure_1878_ = lean_ctor_get(v_toApplicative_1876_, 1);
lean_inc_n(v_toPure_1878_, 2);
lean_dec_ref(v_toApplicative_1876_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1879_, 0, v_toPure_1878_);
lean_closure_set(v___f_1879_, 1, v_toBind_1877_);
v___f_1880_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1880_, 0, v_a_1875_);
lean_closure_set(v___f_1880_, 1, v_toPure_1878_);
v___x_1881_ = lean_apply_4(v_toBind_1877_, lean_box(0), lean_box(0), v_x_1874_, v___f_1880_);
v___x_1882_ = lean_apply_4(v_toBind_1877_, lean_box(0), lean_box(0), v___x_1881_, v___f_1879_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3(lean_object* v_00_u03b1_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_m_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_00_u03b1_1889_, lean_object* v_x_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_toApplicative_1892_; lean_object* v_toBind_1893_; lean_object* v_toPure_1894_; lean_object* v___f_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_toApplicative_1892_ = lean_ctor_get(v_inst_1888_, 0);
lean_inc_ref(v_toApplicative_1892_);
v_toBind_1893_ = lean_ctor_get(v_inst_1888_, 1);
lean_inc_n(v_toBind_1893_, 3);
lean_dec_ref(v_inst_1888_);
v_toPure_1894_ = lean_ctor_get(v_toApplicative_1892_, 1);
lean_inc_n(v_toPure_1894_, 2);
lean_dec_ref(v_toApplicative_1892_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1895_, 0, v_toPure_1894_);
lean_closure_set(v___f_1895_, 1, v_toBind_1893_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1896_, 0, v_a_1891_);
lean_closure_set(v___f_1896_, 1, v_toPure_1894_);
v___x_1897_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v_x_1890_, v___f_1896_);
v___x_1898_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v___x_1897_, v___f_1895_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_00_u03b2_1900_, lean_object* v_m_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_00_u03b1_1905_, lean_object* v_x_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_MonadStateCacheT_instMonadControl___aux__3(v_00_u03b1_1899_, v_00_u03b2_1900_, v_m_1901_, v_inst_1902_, v_inst_1903_, v_inst_1904_, v_00_u03b1_1905_, v_x_1906_, v_a_1907_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v_inst_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_inc_ref(v_inst_1911_);
lean_inc_ref(v_inst_1910_);
lean_inc_ref(v_inst_1909_);
v___x_1912_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1912_, 0, lean_box(0));
lean_closure_set(v___x_1912_, 1, lean_box(0));
lean_closure_set(v___x_1912_, 2, lean_box(0));
lean_closure_set(v___x_1912_, 3, v_inst_1909_);
lean_closure_set(v___x_1912_, 4, v_inst_1910_);
lean_closure_set(v___x_1912_, 5, v_inst_1911_);
v___x_1913_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed), 9, 6);
lean_closure_set(v___x_1913_, 0, lean_box(0));
lean_closure_set(v___x_1913_, 1, lean_box(0));
lean_closure_set(v___x_1913_, 2, lean_box(0));
lean_closure_set(v___x_1913_, 3, v_inst_1909_);
lean_closure_set(v___x_1913_, 4, v_inst_1910_);
lean_closure_set(v___x_1913_, 5, v_inst_1911_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_m_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_1918_, v_inst_1919_, v_inst_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object* v_h_1922_, lean_object* v_s_1923_, lean_object* v_x_1924_){
_start:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_apply_2(v_h_1922_, v___x_1925_, v_s_1923_);
return v___x_1926_;
}
else
{
lean_object* v_val_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_s_1923_);
v_val_1927_ = lean_ctor_get(v_x_1924_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_x_1924_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1929_ = v_x_1924_;
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_val_1927_);
lean_dec(v_x_1924_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1934_; 
v_fst_1931_ = lean_ctor_get(v_val_1927_, 0);
lean_inc(v_fst_1931_);
v_snd_1932_ = lean_ctor_get(v_val_1927_, 1);
lean_inc(v_snd_1932_);
lean_dec(v_val_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v_fst_1931_);
v___x_1934_ = v___x_1929_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fst_1931_);
v___x_1934_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_apply_2(v_h_1922_, v___x_1934_, v_snd_1932_);
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(lean_object* v_toPure_1938_, lean_object* v_____x_1939_){
_start:
{
lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v_fst_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1959_; 
v_fst_1940_ = lean_ctor_get(v_____x_1939_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_____x_1939_, 1);
lean_inc(v_snd_1941_);
lean_dec_ref(v_____x_1939_);
v_fst_1942_ = lean_ctor_get(v_fst_1940_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_fst_1940_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v_fst_1940_, 1);
lean_dec(v_unused_1960_);
v___x_1944_ = v_fst_1940_;
v_isShared_1945_ = v_isSharedCheck_1959_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_fst_1942_);
lean_dec(v_fst_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1959_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1958_; 
v_fst_1946_ = lean_ctor_get(v_snd_1941_, 0);
v_snd_1947_ = lean_ctor_get(v_snd_1941_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_snd_1941_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1949_ = v_snd_1941_;
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_snd_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_fst_1946_);
lean_ctor_set(v___x_1949_, 0, v_fst_1942_);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_fst_1946_);
v___x_1952_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_snd_1947_);
lean_ctor_set(v___x_1944_, 0, v___x_1952_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_snd_1947_);
v___x_1954_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_apply_2(v_toPure_1938_, lean_box(0), v___x_1954_);
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_x_1963_, lean_object* v_h_1964_, lean_object* v_s_1965_){
_start:
{
lean_object* v_toApplicative_1966_; lean_object* v_toBind_1967_; lean_object* v_toPure_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_toApplicative_1966_ = lean_ctor_get(v_inst_1961_, 0);
lean_inc_ref(v_toApplicative_1966_);
v_toBind_1967_ = lean_ctor_get(v_inst_1961_, 1);
lean_inc(v_toBind_1967_);
lean_dec_ref(v_inst_1961_);
v_toPure_1968_ = lean_ctor_get(v_toApplicative_1966_, 1);
lean_inc(v_toPure_1968_);
lean_dec_ref(v_toApplicative_1966_);
lean_inc_ref(v_s_1965_);
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1969_, 0, v_h_1964_);
lean_closure_set(v___f_1969_, 1, v_s_1965_);
v___x_1970_ = lean_apply_1(v_x_1963_, v_s_1965_);
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1971_, 0, v_toPure_1968_);
v___x_1972_ = lean_apply_4(v_inst_1962_, lean_box(0), lean_box(0), v___x_1970_, v___f_1969_);
v___x_1973_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1972_, v___f_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1(lean_object* v_00_u03b1_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_m_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, lean_object* v_h_1984_, lean_object* v_s_1985_){
_start:
{
lean_object* v_toApplicative_1986_; lean_object* v_toBind_1987_; lean_object* v_toPure_1988_; lean_object* v___f_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_toApplicative_1986_ = lean_ctor_get(v_inst_1979_, 0);
lean_inc_ref(v_toApplicative_1986_);
v_toBind_1987_ = lean_ctor_get(v_inst_1979_, 1);
lean_inc(v_toBind_1987_);
lean_dec_ref(v_inst_1979_);
v_toPure_1988_ = lean_ctor_get(v_toApplicative_1986_, 1);
lean_inc(v_toPure_1988_);
lean_dec_ref(v_toApplicative_1986_);
lean_inc_ref(v_s_1985_);
v___f_1989_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1989_, 0, v_h_1984_);
lean_closure_set(v___f_1989_, 1, v_s_1985_);
v___x_1990_ = lean_apply_1(v_x_1983_, v_s_1985_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1991_, 0, v_toPure_1988_);
v___x_1992_ = lean_apply_4(v_inst_1980_, lean_box(0), lean_box(0), v___x_1990_, v___f_1989_);
v___x_1993_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_1992_, v___f_1991_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(lean_object* v_00_u03b1_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_m_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_00_u03b1_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_x_2003_, lean_object* v_h_2004_, lean_object* v_s_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_MonadStateCacheT_instMonadFinally___aux__1(v_00_u03b1_1994_, v_00_u03b2_1995_, v_m_1996_, v_inst_1997_, v_inst_1998_, v_inst_1999_, v_inst_2000_, v_00_u03b1_2001_, v_00_u03b2_2002_, v_x_2003_, v_h_2004_, v_s_2005_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_inst_1997_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_2011_, 0, lean_box(0));
lean_closure_set(v___x_2011_, 1, lean_box(0));
lean_closure_set(v___x_2011_, 2, lean_box(0));
lean_closure_set(v___x_2011_, 3, v_inst_2007_);
lean_closure_set(v___x_2011_, 4, v_inst_2008_);
lean_closure_set(v___x_2011_, 5, v_inst_2009_);
lean_closure_set(v___x_2011_, 6, v_inst_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_m_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_2019_, 0, lean_box(0));
lean_closure_set(v___x_2019_, 1, lean_box(0));
lean_closure_set(v___x_2019_, 2, lean_box(0));
lean_closure_set(v___x_2019_, 3, v_inst_2015_);
lean_closure_set(v___x_2019_, 4, v_inst_2016_);
lean_closure_set(v___x_2019_, 5, v_inst_2017_);
lean_closure_set(v___x_2019_, 6, v_inst_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(lean_object* v_a_2020_, lean_object* v_toPure_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_a_2022_);
lean_ctor_set(v___x_2023_, 1, v_a_2020_);
v___x_2024_ = lean_apply_2(v_toPure_2021_, lean_box(0), v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_toApplicative_2028_; lean_object* v_getRef_2029_; lean_object* v_toBind_2030_; lean_object* v_toPure_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; 
v_toApplicative_2028_ = lean_ctor_get(v_inst_2025_, 0);
lean_inc_ref(v_toApplicative_2028_);
v_getRef_2029_ = lean_ctor_get(v_inst_2026_, 0);
lean_inc(v_getRef_2029_);
lean_dec_ref(v_inst_2026_);
v_toBind_2030_ = lean_ctor_get(v_inst_2025_, 1);
lean_inc(v_toBind_2030_);
lean_dec_ref(v_inst_2025_);
v_toPure_2031_ = lean_ctor_get(v_toApplicative_2028_, 1);
lean_inc(v_toPure_2031_);
lean_dec_ref(v_toApplicative_2028_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2032_, 0, v_a_2027_);
lean_closure_set(v___f_2032_, 1, v_toPure_2031_);
v___x_2033_ = lean_apply_4(v_toBind_2030_, lean_box(0), lean_box(0), v_getRef_2029_, v___f_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1(lean_object* v_00_u03b1_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_m_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_toApplicative_2042_; lean_object* v_getRef_2043_; lean_object* v_toBind_2044_; lean_object* v_toPure_2045_; lean_object* v___f_2046_; lean_object* v___x_2047_; 
v_toApplicative_2042_ = lean_ctor_get(v_inst_2039_, 0);
lean_inc_ref(v_toApplicative_2042_);
v_getRef_2043_ = lean_ctor_get(v_inst_2040_, 0);
lean_inc(v_getRef_2043_);
lean_dec_ref(v_inst_2040_);
v_toBind_2044_ = lean_ctor_get(v_inst_2039_, 1);
lean_inc(v_toBind_2044_);
lean_dec_ref(v_inst_2039_);
v_toPure_2045_ = lean_ctor_get(v_toApplicative_2042_, 1);
lean_inc(v_toPure_2045_);
lean_dec_ref(v_toApplicative_2042_);
v___f_2046_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2046_, 0, v_a_2041_);
lean_closure_set(v___f_2046_, 1, v_toPure_2045_);
v___x_2047_ = lean_apply_4(v_toBind_2044_, lean_box(0), lean_box(0), v_getRef_2043_, v___f_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_m_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_MonadStateCacheT_instMonadRef___aux__1(v_00_u03b1_2048_, v_00_u03b2_2049_, v_m_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_a_2055_);
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(lean_object* v_inst_2057_, lean_object* v_ref_2058_, lean_object* v_x_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_withRef_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_withRef_2061_ = lean_ctor_get(v_inst_2057_, 1);
lean_inc(v_withRef_2061_);
lean_dec_ref(v_inst_2057_);
v___x_2062_ = lean_apply_1(v_x_2059_, v_a_2060_);
v___x_2063_ = lean_apply_3(v_withRef_2061_, lean_box(0), v_ref_2058_, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3(lean_object* v_00_u03b1_2064_, lean_object* v_00_u03b2_2065_, lean_object* v_m_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_00_u03b1_2070_, lean_object* v_ref_2071_, lean_object* v_x_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_withRef_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_withRef_2074_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc(v_withRef_2074_);
lean_dec_ref(v_inst_2069_);
v___x_2075_ = lean_apply_1(v_x_2072_, v_a_2073_);
v___x_2076_ = lean_apply_3(v_withRef_2074_, lean_box(0), v_ref_2071_, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_m_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_00_u03b1_2083_, lean_object* v_ref_2084_, lean_object* v_x_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_MonadStateCacheT_instMonadRef___aux__3(v_00_u03b1_2077_, v_00_u03b2_2078_, v_m_2079_, v_inst_2080_, v_inst_2081_, v_inst_2082_, v_00_u03b1_2083_, v_ref_2084_, v_x_2085_, v_a_2086_);
lean_dec_ref(v_inst_2081_);
lean_dec_ref(v_inst_2080_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_inc_ref(v_inst_2091_);
lean_inc_ref(v_inst_2089_);
lean_inc_ref(v_inst_2088_);
v___x_2092_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed), 8, 7);
lean_closure_set(v___x_2092_, 0, lean_box(0));
lean_closure_set(v___x_2092_, 1, lean_box(0));
lean_closure_set(v___x_2092_, 2, lean_box(0));
lean_closure_set(v___x_2092_, 3, v_inst_2088_);
lean_closure_set(v___x_2092_, 4, v_inst_2089_);
lean_closure_set(v___x_2092_, 5, v_inst_2090_);
lean_closure_set(v___x_2092_, 6, v_inst_2091_);
v___x_2093_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed), 10, 6);
lean_closure_set(v___x_2093_, 0, lean_box(0));
lean_closure_set(v___x_2093_, 1, lean_box(0));
lean_closure_set(v___x_2093_, 2, lean_box(0));
lean_closure_set(v___x_2093_, 3, v_inst_2088_);
lean_closure_set(v___x_2093_, 4, v_inst_2089_);
lean_closure_set(v___x_2093_, 5, v_inst_2091_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_m_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(v_inst_2098_, v_inst_2099_, v_inst_2100_, v_inst_2101_);
return v___x_2102_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_MonadCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_MonadCache(builtin);
}
#ifdef __cplusplus
}
#endif
