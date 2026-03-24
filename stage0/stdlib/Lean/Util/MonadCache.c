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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_____do__lift_17_);
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
lean_inc(v_toBind_28_);
lean_dec_ref(v_inst_24_);
v_findCached_x3f_29_ = lean_ctor_get(v_inst_23_, 0);
lean_inc(v_findCached_x3f_29_);
v_cache_30_ = lean_ctor_get(v_inst_23_, 1);
lean_inc(v_cache_30_);
lean_dec_ref(v_inst_23_);
v_toPure_31_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc(v_toPure_31_);
lean_dec_ref(v_toApplicative_27_);
lean_inc(v_a_25_);
v___x_32_ = lean_apply_1(v_findCached_x3f_29_, v_a_25_);
lean_inc(v_toBind_28_);
lean_inc(v_toPure_31_);
v___f_33_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__1), 5, 4);
lean_closure_set(v___f_33_, 0, v_toPure_31_);
lean_closure_set(v___f_33_, 1, v_cache_30_);
lean_closure_set(v___f_33_, 2, v_a_25_);
lean_closure_set(v___f_33_, 3, v_toBind_28_);
lean_inc(v_toBind_28_);
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
lean_inc(v_toBind_44_);
lean_dec_ref(v_inst_40_);
v_findCached_x3f_45_ = lean_ctor_get(v_inst_39_, 0);
lean_inc(v_findCached_x3f_45_);
v_cache_46_ = lean_ctor_get(v_inst_39_, 1);
lean_inc(v_cache_46_);
lean_dec_ref(v_inst_39_);
v_toPure_47_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_47_);
lean_dec_ref(v_toApplicative_43_);
lean_inc(v_a_41_);
v___x_48_ = lean_apply_1(v_findCached_x3f_45_, v_a_41_);
lean_inc(v_toBind_44_);
lean_inc(v_toPure_47_);
v___f_49_ = lean_alloc_closure((void*)(l_Lean_checkCache___redArg___lam__1), 5, 4);
lean_closure_set(v___f_49_, 0, v_toPure_47_);
lean_closure_set(v___f_49_, 1, v_cache_46_);
lean_closure_set(v___f_49_, 2, v_a_41_);
lean_closure_set(v___f_49_, 3, v_toBind_44_);
lean_inc(v_toBind_44_);
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
lean_object* v___x_170_; 
v___x_170_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_165_, v_inst_166_, v_s_169_, v_a_167_, v_b_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
lean_object* v_modifyCache_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
v_modifyCache_176_ = lean_ctor_get(v_inst_173_, 1);
lean_inc(v_modifyCache_176_);
lean_dec_ref(v_inst_173_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0), 5, 4);
lean_closure_set(v___f_177_, 0, v_inst_171_);
lean_closure_set(v___f_177_, 1, v_inst_172_);
lean_closure_set(v___f_177_, 2, v_a_174_);
lean_closure_set(v___f_177_, 3, v_b_175_);
v___x_178_ = lean_apply_1(v_modifyCache_176_, v___f_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_cache(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_m_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_modifyCache_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v_modifyCache_187_ = lean_ctor_get(v_inst_184_, 1);
lean_inc(v_modifyCache_187_);
lean_dec_ref(v_inst_184_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0), 5, 4);
lean_closure_set(v___f_188_, 0, v_inst_182_);
lean_closure_set(v___f_188_, 1, v_inst_183_);
lean_closure_set(v___f_188_, 2, v_a_185_);
lean_closure_set(v___f_188_, 3, v_b_186_);
v___x_189_ = lean_apply_1(v_modifyCache_187_, v___f_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_inc_ref(v_inst_193_);
lean_inc_ref(v_inst_191_);
lean_inc_ref(v_inst_190_);
v___x_194_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_findCached_x3f), 8, 7);
lean_closure_set(v___x_194_, 0, lean_box(0));
lean_closure_set(v___x_194_, 1, lean_box(0));
lean_closure_set(v___x_194_, 2, lean_box(0));
lean_closure_set(v___x_194_, 3, v_inst_190_);
lean_closure_set(v___x_194_, 4, v_inst_191_);
lean_closure_set(v___x_194_, 5, v_inst_192_);
lean_closure_set(v___x_194_, 6, v_inst_193_);
v___x_195_ = lean_alloc_closure((void*)(l_Lean_MonadHashMapCacheAdapter_cache), 8, 6);
lean_closure_set(v___x_195_, 0, lean_box(0));
lean_closure_set(v___x_195_, 1, lean_box(0));
lean_closure_set(v___x_195_, 2, lean_box(0));
lean_closure_set(v___x_195_, 3, v_inst_190_);
lean_closure_set(v___x_195_, 4, v_inst_191_);
lean_closure_set(v___x_195_, 5, v_inst_193_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_m_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(v_inst_200_, v_inst_201_, v_inst_202_, v_inst_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_f_205_, lean_object* v_s_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_f_205_, v_s_206_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(lean_object* v_inst_210_, lean_object* v_f_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___f_213_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 2, 1);
lean_closure_set(v___f_213_, 0, v_f_211_);
lean_inc(v___y_212_);
v___x_214_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_214_, 0, lean_box(0));
lean_closure_set(v___x_214_, 1, lean_box(0));
lean_closure_set(v___x_214_, 2, lean_box(0));
lean_closure_set(v___x_214_, 3, v___y_212_);
lean_closure_set(v___x_214_, 4, v___f_213_);
v___x_215_ = lean_apply_2(v_inst_210_, lean_box(0), v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(lean_object* v_inst_216_, lean_object* v_f_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(v_inst_216_, v_f_217_, v___y_218_);
lean_dec(v___y_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_220_){
_start:
{
lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_inc(v_inst_220_);
v___f_221_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_221_, 0, v_inst_220_);
v___x_222_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, lean_box(0));
lean_closure_set(v___x_222_, 2, lean_box(0));
lean_closure_set(v___x_222_, 3, v_inst_220_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___f_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03c9_224_, lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_m_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03c9_233_, lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_m_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(v_00_u03c9_233_, v_00_u03b1_234_, v_00_u03b2_235_, v_m_236_, v_inst_237_, v_inst_238_, v_inst_239_, v_inst_240_);
lean_dec_ref(v_inst_239_);
lean_dec_ref(v_inst_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__0(lean_object* v_a_242_, lean_object* v_toPure_243_, lean_object* v_s_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_a_242_);
lean_ctor_set(v___x_245_, 1, v_s_244_);
v___x_246_ = lean_apply_2(v_toPure_243_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__1(lean_object* v_toPure_247_, lean_object* v_ref_248_, lean_object* v_inst_249_, lean_object* v_toBind_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___f_252_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_252_, 0, v_a_251_);
lean_closure_set(v___f_252_, 1, v_toPure_247_);
v___x_253_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, lean_box(0));
lean_closure_set(v___x_253_, 2, v_ref_248_);
v___x_254_ = lean_apply_2(v_inst_249_, lean_box(0), v___x_253_);
v___x_255_ = lean_apply_4(v_toBind_250_, lean_box(0), lean_box(0), v___x_254_, v___f_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__2(lean_object* v_toPure_256_, lean_object* v_inst_257_, lean_object* v_toBind_258_, lean_object* v_x_259_, lean_object* v_ref_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_toBind_258_);
lean_inc(v_ref_260_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_261_, 0, v_toPure_256_);
lean_closure_set(v___f_261_, 1, v_ref_260_);
lean_closure_set(v___f_261_, 2, v_inst_257_);
lean_closure_set(v___f_261_, 3, v_toBind_258_);
v___x_262_ = lean_apply_1(v_x_259_, v_ref_260_);
v___x_263_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_262_, v___f_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__3(lean_object* v_toPure_264_, lean_object* v_____x_265_){
_start:
{
lean_object* v_fst_266_; lean_object* v___x_267_; 
v_fst_266_ = lean_ctor_get(v_____x_265_, 0);
lean_inc(v_fst_266_);
lean_dec_ref(v_____x_265_);
v___x_267_ = lean_apply_2(v_toPure_264_, lean_box(0), v_fst_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_unsigned_to_nat(16u);
v___x_270_ = lean_mk_array(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__0, &l_Lean_MonadCacheT_run___redArg___closed__0_once, _init_l_Lean_MonadCacheT_run___redArg___closed__0);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_275_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, lean_box(0));
lean_closure_set(v___x_275_, 2, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_toApplicative_279_; lean_object* v_toBind_280_; lean_object* v_toPure_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_toApplicative_279_ = lean_ctor_get(v_inst_277_, 0);
lean_inc_ref(v_toApplicative_279_);
v_toBind_280_ = lean_ctor_get(v_inst_277_, 1);
lean_inc(v_toBind_280_);
lean_dec_ref(v_inst_277_);
v_toPure_281_ = lean_ctor_get(v_toApplicative_279_, 1);
lean_inc(v_toPure_281_);
lean_dec_ref(v_toApplicative_279_);
v___x_282_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_276_);
v___x_283_ = lean_apply_2(v_inst_276_, lean_box(0), v___x_282_);
lean_inc(v_toBind_280_);
lean_inc(v_toPure_281_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_284_, 0, v_toPure_281_);
lean_closure_set(v___f_284_, 1, v_inst_276_);
lean_closure_set(v___f_284_, 2, v_toBind_280_);
lean_closure_set(v___f_284_, 3, v_x_278_);
v___f_285_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_285_, 0, v_toPure_281_);
lean_inc(v_toBind_280_);
v___x_286_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_283_, v___f_284_);
v___x_287_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_286_, v___f_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run(lean_object* v_00_u03c9_288_, lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_m_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_00_u03c3_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_toApplicative_299_; lean_object* v_toBind_300_; lean_object* v_toPure_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_toApplicative_299_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref(v_toApplicative_299_);
v_toBind_300_ = lean_ctor_get(v_inst_296_, 1);
lean_inc(v_toBind_300_);
lean_dec_ref(v_inst_296_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_299_, 1);
lean_inc(v_toPure_301_);
lean_dec_ref(v_toApplicative_299_);
v___x_302_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_295_);
v___x_303_ = lean_apply_2(v_inst_295_, lean_box(0), v___x_302_);
lean_inc(v_toBind_300_);
lean_inc(v_toPure_301_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_304_, 0, v_toPure_301_);
lean_closure_set(v___f_304_, 1, v_inst_295_);
lean_closure_set(v___f_304_, 2, v_toBind_300_);
lean_closure_set(v___f_304_, 3, v_x_298_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_305_, 0, v_toPure_301_);
lean_inc(v_toBind_300_);
v___x_306_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_303_, v___f_304_);
v___x_307_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_306_, v___f_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___boxed(lean_object* v_00_u03c9_308_, lean_object* v_00_u03b1_309_, lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_00_u03c3_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_MonadCacheT_run(v_00_u03c9_308_, v_00_u03b1_309_, v_00_u03b2_310_, v_m_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_inst_315_, v_inst_316_, v_00_u03c3_317_, v_x_318_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg(lean_object* v_inst_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_toApplicative_324_; lean_object* v_toFunctor_325_; lean_object* v_map_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_320_, 0);
lean_inc_ref(v_toApplicative_324_);
lean_dec_ref(v_inst_320_);
v_toFunctor_325_ = lean_ctor_get(v_toApplicative_324_, 0);
lean_inc_ref(v_toFunctor_325_);
lean_dec_ref(v_toApplicative_324_);
v_map_326_ = lean_ctor_get(v_toFunctor_325_, 0);
lean_inc(v_map_326_);
lean_dec_ref(v_toFunctor_325_);
lean_inc(v_a_323_);
v___x_327_ = lean_apply_1(v_a_322_, v_a_323_);
v___x_328_ = lean_apply_4(v_map_326_, lean_box(0), lean_box(0), v_a_321_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(lean_object* v_inst_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_MonadCacheT_instMonad___aux__1___redArg(v_inst_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1(lean_object* v_00_u03c9_334_, lean_object* v_00_u03b1_335_, lean_object* v_00_u03b2_336_, lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_toApplicative_347_; lean_object* v_toFunctor_348_; lean_object* v_map_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_341_, 0);
lean_inc_ref(v_toApplicative_347_);
lean_dec_ref(v_inst_341_);
v_toFunctor_348_ = lean_ctor_get(v_toApplicative_347_, 0);
lean_inc_ref(v_toFunctor_348_);
lean_dec_ref(v_toApplicative_347_);
v_map_349_ = lean_ctor_get(v_toFunctor_348_, 0);
lean_inc(v_map_349_);
lean_dec_ref(v_toFunctor_348_);
lean_inc(v_a_346_);
v___x_350_ = lean_apply_1(v_a_345_, v_a_346_);
v___x_351_ = lean_apply_4(v_map_349_, lean_box(0), lean_box(0), v_a_344_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__1___boxed(lean_object* v_00_u03c9_352_, lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_m_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_MonadCacheT_instMonad___aux__1(v_00_u03c9_352_, v_00_u03b1_353_, v_00_u03b2_354_, v_m_355_, v_inst_356_, v_inst_357_, v_inst_358_, v_inst_359_, v_00_u03b1_360_, v_00_u03b2_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_inst_358_);
lean_dec_ref(v_inst_357_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg(lean_object* v_inst_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_toApplicative_370_; lean_object* v_toFunctor_371_; lean_object* v_mapConst_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_toApplicative_370_ = lean_ctor_get(v_inst_366_, 0);
lean_inc_ref(v_toApplicative_370_);
lean_dec_ref(v_inst_366_);
v_toFunctor_371_ = lean_ctor_get(v_toApplicative_370_, 0);
lean_inc_ref(v_toFunctor_371_);
lean_dec_ref(v_toApplicative_370_);
v_mapConst_372_ = lean_ctor_get(v_toFunctor_371_, 1);
lean_inc(v_mapConst_372_);
lean_dec_ref(v_toFunctor_371_);
lean_inc(v_a_369_);
v___x_373_ = lean_apply_1(v_a_368_, v_a_369_);
v___x_374_ = lean_apply_4(v_mapConst_372_, lean_box(0), lean_box(0), v_a_367_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(lean_object* v_inst_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_MonadCacheT_instMonad___aux__3___redArg(v_inst_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3(lean_object* v_00_u03c9_380_, lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_m_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_toApplicative_393_; lean_object* v_toFunctor_394_; lean_object* v_mapConst_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_toApplicative_393_ = lean_ctor_get(v_inst_387_, 0);
lean_inc_ref(v_toApplicative_393_);
lean_dec_ref(v_inst_387_);
v_toFunctor_394_ = lean_ctor_get(v_toApplicative_393_, 0);
lean_inc_ref(v_toFunctor_394_);
lean_dec_ref(v_toApplicative_393_);
v_mapConst_395_ = lean_ctor_get(v_toFunctor_394_, 1);
lean_inc(v_mapConst_395_);
lean_dec_ref(v_toFunctor_394_);
lean_inc(v_a_392_);
v___x_396_ = lean_apply_1(v_a_391_, v_a_392_);
v___x_397_ = lean_apply_4(v_mapConst_395_, lean_box(0), lean_box(0), v_a_390_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__3___boxed(lean_object* v_00_u03c9_398_, lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_MonadCacheT_instMonad___aux__3(v_00_u03c9_398_, v_00_u03b1_399_, v_00_u03b2_400_, v_m_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_00_u03b1_406_, v_00_u03b2_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_inst_404_);
lean_dec_ref(v_inst_403_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___redArg(lean_object* v_inst_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_toApplicative_414_; lean_object* v_toPure_415_; lean_object* v___x_416_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_412_, 0);
lean_inc_ref(v_toApplicative_414_);
lean_dec_ref(v_inst_412_);
v_toPure_415_ = lean_ctor_get(v_toApplicative_414_, 1);
lean_inc(v_toPure_415_);
lean_dec_ref(v_toApplicative_414_);
v___x_416_ = lean_apply_2(v_toPure_415_, lean_box(0), v_a_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5(lean_object* v_00_u03c9_417_, lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_m_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_00_u03b1_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_toApplicative_428_; lean_object* v_toPure_429_; lean_object* v___x_430_; 
v_toApplicative_428_ = lean_ctor_get(v_inst_424_, 0);
lean_inc_ref(v_toApplicative_428_);
lean_dec_ref(v_inst_424_);
v_toPure_429_ = lean_ctor_get(v_toApplicative_428_, 1);
lean_inc(v_toPure_429_);
lean_dec_ref(v_toApplicative_428_);
v___x_430_ = lean_apply_2(v_toPure_429_, lean_box(0), v_a_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__5___boxed(lean_object* v_00_u03c9_431_, lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_00_u03b1_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_MonadCacheT_instMonad___aux__5(v_00_u03c9_431_, v_00_u03b1_432_, v_00_u03b2_433_, v_m_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_00_u03b1_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_inst_437_);
lean_dec_ref(v_inst_436_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(0);
lean_inc(v_a_444_);
v___x_447_ = lean_apply_2(v_a_443_, v___x_446_, v_a_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(v_a_448_, v_a_449_, v_x_450_);
lean_dec(v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg(lean_object* v_inst_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_toApplicative_456_; lean_object* v_toSeq_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_toApplicative_456_ = lean_ctor_get(v_inst_452_, 0);
lean_inc_ref(v_toApplicative_456_);
lean_dec_ref(v_inst_452_);
v_toSeq_457_ = lean_ctor_get(v_toApplicative_456_, 2);
lean_inc(v_toSeq_457_);
lean_dec_ref(v_toApplicative_456_);
lean_inc(v_a_455_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_458_, 0, v_a_454_);
lean_closure_set(v___f_458_, 1, v_a_455_);
lean_inc(v_a_455_);
v___x_459_ = lean_apply_1(v_a_453_, v_a_455_);
v___x_460_ = lean_apply_4(v_toSeq_457_, lean_box(0), lean_box(0), v___x_459_, v___f_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(lean_object* v_inst_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg(v_inst_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7(lean_object* v_00_u03c9_466_, lean_object* v_00_u03b1_467_, lean_object* v_00_u03b2_468_, lean_object* v_m_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_toApplicative_479_; lean_object* v_toSeq_480_; lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toApplicative_479_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toApplicative_479_);
lean_dec_ref(v_inst_473_);
v_toSeq_480_ = lean_ctor_get(v_toApplicative_479_, 2);
lean_inc(v_toSeq_480_);
lean_dec_ref(v_toApplicative_479_);
lean_inc(v_a_478_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_481_, 0, v_a_477_);
lean_closure_set(v___f_481_, 1, v_a_478_);
lean_inc(v_a_478_);
v___x_482_ = lean_apply_1(v_a_476_, v_a_478_);
v___x_483_ = lean_apply_4(v_toSeq_480_, lean_box(0), lean_box(0), v___x_482_, v___f_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__7___boxed(lean_object* v_00_u03c9_484_, lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_m_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MonadCacheT_instMonad___aux__7(v_00_u03c9_484_, v_00_u03b1_485_, v_00_u03b2_486_, v_m_487_, v_inst_488_, v_inst_489_, v_inst_490_, v_inst_491_, v_00_u03b1_492_, v_00_u03b2_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg(lean_object* v_inst_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_toApplicative_502_; lean_object* v_toSeqLeft_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_toApplicative_502_ = lean_ctor_get(v_inst_498_, 0);
lean_inc_ref(v_toApplicative_502_);
lean_dec_ref(v_inst_498_);
v_toSeqLeft_503_ = lean_ctor_get(v_toApplicative_502_, 3);
lean_inc(v_toSeqLeft_503_);
lean_dec_ref(v_toApplicative_502_);
lean_inc(v_a_501_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_504_, 0, v_a_500_);
lean_closure_set(v___f_504_, 1, v_a_501_);
lean_inc(v_a_501_);
v___x_505_ = lean_apply_1(v_a_499_, v_a_501_);
v___x_506_ = lean_apply_4(v_toSeqLeft_503_, lean_box(0), lean_box(0), v___x_505_, v___f_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(lean_object* v_inst_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_MonadCacheT_instMonad___aux__9___redArg(v_inst_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9(lean_object* v_00_u03c9_512_, lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_toApplicative_525_; lean_object* v_toSeqLeft_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_toApplicative_525_ = lean_ctor_get(v_inst_519_, 0);
lean_inc_ref(v_toApplicative_525_);
lean_dec_ref(v_inst_519_);
v_toSeqLeft_526_ = lean_ctor_get(v_toApplicative_525_, 3);
lean_inc(v_toSeqLeft_526_);
lean_dec_ref(v_toApplicative_525_);
lean_inc(v_a_524_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_527_, 0, v_a_523_);
lean_closure_set(v___f_527_, 1, v_a_524_);
lean_inc(v_a_524_);
v___x_528_ = lean_apply_1(v_a_522_, v_a_524_);
v___x_529_ = lean_apply_4(v_toSeqLeft_526_, lean_box(0), lean_box(0), v___x_528_, v___f_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__9___boxed(lean_object* v_00_u03c9_530_, lean_object* v_00_u03b1_531_, lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_MonadCacheT_instMonad___aux__9(v_00_u03c9_530_, v_00_u03b1_531_, v_00_u03b2_532_, v_m_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_00_u03b1_538_, v_00_u03b2_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_inst_536_);
lean_dec_ref(v_inst_535_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg(lean_object* v_inst_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_toApplicative_548_; lean_object* v_toSeqRight_549_; lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toApplicative_548_ = lean_ctor_get(v_inst_544_, 0);
lean_inc_ref(v_toApplicative_548_);
lean_dec_ref(v_inst_544_);
v_toSeqRight_549_ = lean_ctor_get(v_toApplicative_548_, 4);
lean_inc(v_toSeqRight_549_);
lean_dec_ref(v_toApplicative_548_);
lean_inc(v_a_547_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_550_, 0, v_a_546_);
lean_closure_set(v___f_550_, 1, v_a_547_);
lean_inc(v_a_547_);
v___x_551_ = lean_apply_1(v_a_545_, v_a_547_);
v___x_552_ = lean_apply_4(v_toSeqRight_549_, lean_box(0), lean_box(0), v___x_551_, v___f_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(lean_object* v_inst_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_MonadCacheT_instMonad___aux__11___redArg(v_inst_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11(lean_object* v_00_u03c9_558_, lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_m_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_toApplicative_571_; lean_object* v_toSeqRight_572_; lean_object* v___f_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_toApplicative_571_ = lean_ctor_get(v_inst_565_, 0);
lean_inc_ref(v_toApplicative_571_);
lean_dec_ref(v_inst_565_);
v_toSeqRight_572_ = lean_ctor_get(v_toApplicative_571_, 4);
lean_inc(v_toSeqRight_572_);
lean_dec_ref(v_toApplicative_571_);
lean_inc(v_a_570_);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_573_, 0, v_a_569_);
lean_closure_set(v___f_573_, 1, v_a_570_);
lean_inc(v_a_570_);
v___x_574_ = lean_apply_1(v_a_568_, v_a_570_);
v___x_575_ = lean_apply_4(v_toSeqRight_572_, lean_box(0), lean_box(0), v___x_574_, v___f_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__11___boxed(lean_object* v_00_u03c9_576_, lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_MonadCacheT_instMonad___aux__11(v_00_u03c9_576_, v_00_u03b1_577_, v_00_u03b2_578_, v_m_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_00_u03b1_584_, v_00_u03b2_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_inst_582_);
lean_dec_ref(v_inst_581_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_593_; 
lean_inc(v_a_591_);
v___x_593_ = lean_apply_2(v_a_590_, v_a_592_, v_a_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg(lean_object* v_inst_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_toBind_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_toBind_602_ = lean_ctor_get(v_inst_598_, 1);
lean_inc(v_toBind_602_);
lean_dec_ref(v_inst_598_);
lean_inc(v_a_601_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_603_, 0, v_a_600_);
lean_closure_set(v___f_603_, 1, v_a_601_);
lean_inc(v_a_601_);
v___x_604_ = lean_apply_1(v_a_599_, v_a_601_);
v___x_605_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_604_, v___f_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(lean_object* v_inst_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(v_inst_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13(lean_object* v_00_u03c9_611_, lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_m_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_toBind_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_toBind_624_ = lean_ctor_get(v_inst_618_, 1);
lean_inc(v_toBind_624_);
lean_dec_ref(v_inst_618_);
lean_inc(v_a_623_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_625_, 0, v_a_622_);
lean_closure_set(v___f_625_, 1, v_a_623_);
lean_inc(v_a_623_);
v___x_626_ = lean_apply_1(v_a_621_, v_a_623_);
v___x_627_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_626_, v___f_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03c9_628_, lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_m_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_MonadCacheT_instMonad___aux__13(v_00_u03c9_628_, v_00_u03b1_629_, v_00_u03b2_630_, v_m_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_inst_635_, v_00_u03b1_636_, v_00_u03b2_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_inst_634_);
lean_dec_ref(v_inst_633_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_646_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__1___boxed), 13, 8);
lean_closure_set(v___x_646_, 0, lean_box(0));
lean_closure_set(v___x_646_, 1, lean_box(0));
lean_closure_set(v___x_646_, 2, lean_box(0));
lean_closure_set(v___x_646_, 3, lean_box(0));
lean_closure_set(v___x_646_, 4, v_inst_642_);
lean_closure_set(v___x_646_, 5, v_inst_643_);
lean_closure_set(v___x_646_, 6, v_inst_644_);
lean_closure_set(v___x_646_, 7, v_inst_645_);
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_647_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__3___boxed), 13, 8);
lean_closure_set(v___x_647_, 0, lean_box(0));
lean_closure_set(v___x_647_, 1, lean_box(0));
lean_closure_set(v___x_647_, 2, lean_box(0));
lean_closure_set(v___x_647_, 3, lean_box(0));
lean_closure_set(v___x_647_, 4, v_inst_642_);
lean_closure_set(v___x_647_, 5, v_inst_643_);
lean_closure_set(v___x_647_, 6, v_inst_644_);
lean_closure_set(v___x_647_, 7, v_inst_645_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_649_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__5___boxed), 11, 8);
lean_closure_set(v___x_649_, 0, lean_box(0));
lean_closure_set(v___x_649_, 1, lean_box(0));
lean_closure_set(v___x_649_, 2, lean_box(0));
lean_closure_set(v___x_649_, 3, lean_box(0));
lean_closure_set(v___x_649_, 4, v_inst_642_);
lean_closure_set(v___x_649_, 5, v_inst_643_);
lean_closure_set(v___x_649_, 6, v_inst_644_);
lean_closure_set(v___x_649_, 7, v_inst_645_);
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_650_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___boxed), 13, 8);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, lean_box(0));
lean_closure_set(v___x_650_, 3, lean_box(0));
lean_closure_set(v___x_650_, 4, v_inst_642_);
lean_closure_set(v___x_650_, 5, v_inst_643_);
lean_closure_set(v___x_650_, 6, v_inst_644_);
lean_closure_set(v___x_650_, 7, v_inst_645_);
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_651_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__9___boxed), 13, 8);
lean_closure_set(v___x_651_, 0, lean_box(0));
lean_closure_set(v___x_651_, 1, lean_box(0));
lean_closure_set(v___x_651_, 2, lean_box(0));
lean_closure_set(v___x_651_, 3, lean_box(0));
lean_closure_set(v___x_651_, 4, v_inst_642_);
lean_closure_set(v___x_651_, 5, v_inst_643_);
lean_closure_set(v___x_651_, 6, v_inst_644_);
lean_closure_set(v___x_651_, 7, v_inst_645_);
lean_inc_ref(v_inst_645_);
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
v___x_652_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__11___boxed), 13, 8);
lean_closure_set(v___x_652_, 0, lean_box(0));
lean_closure_set(v___x_652_, 1, lean_box(0));
lean_closure_set(v___x_652_, 2, lean_box(0));
lean_closure_set(v___x_652_, 3, lean_box(0));
lean_closure_set(v___x_652_, 4, v_inst_642_);
lean_closure_set(v___x_652_, 5, v_inst_643_);
lean_closure_set(v___x_652_, 6, v_inst_644_);
lean_closure_set(v___x_652_, 7, v_inst_645_);
v___x_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_653_, 0, v___x_648_);
lean_ctor_set(v___x_653_, 1, v___x_649_);
lean_ctor_set(v___x_653_, 2, v___x_650_);
lean_ctor_set(v___x_653_, 3, v___x_651_);
lean_ctor_set(v___x_653_, 4, v___x_652_);
v___x_654_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 8);
lean_closure_set(v___x_654_, 0, lean_box(0));
lean_closure_set(v___x_654_, 1, lean_box(0));
lean_closure_set(v___x_654_, 2, lean_box(0));
lean_closure_set(v___x_654_, 3, lean_box(0));
lean_closure_set(v___x_654_, 4, v_inst_642_);
lean_closure_set(v___x_654_, 5, v_inst_643_);
lean_closure_set(v___x_654_, 6, v_inst_644_);
lean_closure_set(v___x_654_, 7, v_inst_645_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad(lean_object* v_00_u03c9_656_, lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_m_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_MonadCacheT_instMonad___redArg(v_inst_660_, v_inst_661_, v_inst_662_, v_inst_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(lean_object* v_x_665_){
_start:
{
lean_inc(v_x_665_);
return v_x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(lean_object* v_x_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(v_x_666_);
lean_dec(v_x_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1(lean_object* v_00_u03c9_668_, lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_m_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_00_u03b1_675_, lean_object* v_x_676_, lean_object* v_a_677_){
_start:
{
lean_inc(v_x_676_);
return v_x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(lean_object* v_00_u03c9_678_, lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_m_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_00_u03b1_685_, lean_object* v_x_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_MonadCacheT_instMonadLift___aux__1(v_00_u03c9_678_, v_00_u03b1_679_, v_00_u03b2_680_, v_m_681_, v_inst_682_, v_inst_683_, v_inst_684_, v_00_u03b1_685_, v_x_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec(v_x_686_);
lean_dec_ref(v_inst_684_);
lean_dec_ref(v_inst_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 7);
lean_closure_set(v___x_692_, 0, lean_box(0));
lean_closure_set(v___x_692_, 1, lean_box(0));
lean_closure_set(v___x_692_, 2, lean_box(0));
lean_closure_set(v___x_692_, 3, lean_box(0));
lean_closure_set(v___x_692_, 4, v_inst_689_);
lean_closure_set(v___x_692_, 5, v_inst_690_);
lean_closure_set(v___x_692_, 6, v_inst_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift(lean_object* v_00_u03c9_693_, lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_m_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 7);
lean_closure_set(v___x_700_, 0, lean_box(0));
lean_closure_set(v___x_700_, 1, lean_box(0));
lean_closure_set(v___x_700_, 2, lean_box(0));
lean_closure_set(v___x_700_, 3, lean_box(0));
lean_closure_set(v___x_700_, 4, v_inst_697_);
lean_closure_set(v___x_700_, 5, v_inst_698_);
lean_closure_set(v___x_700_, 6, v_inst_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(lean_object* v_inst_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_throw_703_; lean_object* v___x_704_; 
v_throw_703_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_throw_703_);
lean_dec_ref(v_inst_701_);
v___x_704_ = lean_apply_2(v_throw_703_, lean_box(0), v_a_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1(lean_object* v_00_u03c9_705_, lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_m_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_00_u03b5_712_, lean_object* v_inst_713_, lean_object* v_00_u03b1_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_throw_717_; lean_object* v___x_718_; 
v_throw_717_ = lean_ctor_get(v_inst_713_, 0);
lean_inc(v_throw_717_);
lean_dec_ref(v_inst_713_);
v___x_718_ = lean_apply_2(v_throw_717_, lean_box(0), v_a_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(lean_object* v_00_u03c9_719_, lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_m_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_00_u03b5_726_, lean_object* v_inst_727_, lean_object* v_00_u03b1_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__1(v_00_u03c9_719_, v_00_u03b1_720_, v_00_u03b2_721_, v_m_722_, v_inst_723_, v_inst_724_, v_inst_725_, v_00_u03b5_726_, v_inst_727_, v_00_u03b1_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_inst_725_);
lean_dec_ref(v_inst_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object* v_c_732_, lean_object* v_s_733_, lean_object* v_e_734_){
_start:
{
lean_object* v___x_735_; 
lean_inc(v_s_733_);
v___x_735_ = lean_apply_2(v_c_732_, v_e_734_, v_s_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(lean_object* v_c_736_, lean_object* v_s_737_, lean_object* v_e_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(v_c_736_, v_s_737_, v_e_738_);
lean_dec(v_s_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(lean_object* v_inst_740_, lean_object* v_x_741_, lean_object* v_c_742_, lean_object* v_s_743_){
_start:
{
lean_object* v_tryCatch_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_tryCatch_744_ = lean_ctor_get(v_inst_740_, 1);
lean_inc(v_tryCatch_744_);
lean_dec_ref(v_inst_740_);
lean_inc(v_s_743_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_745_, 0, v_c_742_);
lean_closure_set(v___f_745_, 1, v_s_743_);
lean_inc(v_s_743_);
v___x_746_ = lean_apply_1(v_x_741_, v_s_743_);
v___x_747_ = lean_apply_3(v_tryCatch_744_, lean_box(0), v___x_746_, v___f_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(lean_object* v_inst_748_, lean_object* v_x_749_, lean_object* v_c_750_, lean_object* v_s_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(v_inst_748_, v_x_749_, v_c_750_, v_s_751_);
lean_dec(v_s_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3(lean_object* v_00_u03c9_753_, lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_00_u03b5_760_, lean_object* v_inst_761_, lean_object* v_00_u03b1_762_, lean_object* v_x_763_, lean_object* v_c_764_, lean_object* v_s_765_){
_start:
{
lean_object* v_tryCatch_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_tryCatch_766_ = lean_ctor_get(v_inst_761_, 1);
lean_inc(v_tryCatch_766_);
lean_dec_ref(v_inst_761_);
lean_inc(v_s_765_);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_767_, 0, v_c_764_);
lean_closure_set(v___f_767_, 1, v_s_765_);
lean_inc(v_s_765_);
v___x_768_ = lean_apply_1(v_x_763_, v_s_765_);
v___x_769_ = lean_apply_3(v_tryCatch_766_, lean_box(0), v___x_768_, v___f_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(lean_object* v_00_u03c9_770_, lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_00_u03b5_777_, lean_object* v_inst_778_, lean_object* v_00_u03b1_779_, lean_object* v_x_780_, lean_object* v_c_781_, lean_object* v_s_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3(v_00_u03c9_770_, v_00_u03b1_771_, v_00_u03b2_772_, v_m_773_, v_inst_774_, v_inst_775_, v_inst_776_, v_00_u03b5_777_, v_inst_778_, v_00_u03b1_779_, v_x_780_, v_c_781_, v_s_782_);
lean_dec(v_s_782_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_inst_775_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v_inst_787_);
lean_inc_ref(v_inst_786_);
lean_inc_ref(v_inst_785_);
v___x_788_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed), 12, 9);
lean_closure_set(v___x_788_, 0, lean_box(0));
lean_closure_set(v___x_788_, 1, lean_box(0));
lean_closure_set(v___x_788_, 2, lean_box(0));
lean_closure_set(v___x_788_, 3, lean_box(0));
lean_closure_set(v___x_788_, 4, v_inst_784_);
lean_closure_set(v___x_788_, 5, v_inst_785_);
lean_closure_set(v___x_788_, 6, v_inst_786_);
lean_closure_set(v___x_788_, 7, lean_box(0));
lean_closure_set(v___x_788_, 8, v_inst_787_);
v___x_789_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed), 13, 9);
lean_closure_set(v___x_789_, 0, lean_box(0));
lean_closure_set(v___x_789_, 1, lean_box(0));
lean_closure_set(v___x_789_, 2, lean_box(0));
lean_closure_set(v___x_789_, 3, lean_box(0));
lean_closure_set(v___x_789_, 4, v_inst_784_);
lean_closure_set(v___x_789_, 5, v_inst_785_);
lean_closure_set(v___x_789_, 6, v_inst_786_);
lean_closure_set(v___x_789_, 7, lean_box(0));
lean_closure_set(v___x_789_, 8, v_inst_787_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf(lean_object* v_00_u03c9_791_, lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_00_u03b5_798_, lean_object* v_inst_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_795_, v_inst_796_, v_inst_797_, v_inst_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object* v_a_801_, lean_object* v_00_u03b2_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
lean_inc(v_a_801_);
v___x_804_ = lean_apply_1(v_x_803_, v_a_801_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(lean_object* v_a_805_, lean_object* v_00_u03b2_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(v_a_805_, v_00_u03b2_806_, v_x_807_);
lean_dec(v_a_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
lean_inc(v_a_810_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_811_, 0, v_a_810_);
v___x_812_ = lean_apply_1(v_a_809_, v___f_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(v_a_813_, v_a_814_);
lean_dec(v_a_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1(lean_object* v_00_u03c9_816_, lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_00_u03b1_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___f_826_; lean_object* v___x_827_; 
lean_inc(v_a_825_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_826_, 0, v_a_825_);
v___x_827_ = lean_apply_1(v_a_824_, v___f_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(lean_object* v_00_u03c9_828_, lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_m_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_00_u03b1_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_MonadCacheT_instMonadControl___aux__1(v_00_u03c9_828_, v_00_u03b1_829_, v_00_u03b2_830_, v_m_831_, v_inst_832_, v_inst_833_, v_inst_834_, v_00_u03b1_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_inst_834_);
lean_dec_ref(v_inst_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(lean_object* v_a_839_){
_start:
{
lean_inc(v_a_839_);
return v_a_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(v_a_840_);
lean_dec(v_a_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3(lean_object* v_00_u03c9_842_, lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_00_u03b1_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_inc(v_a_850_);
return v_a_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(lean_object* v_00_u03c9_852_, lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_00_u03b1_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_MonadCacheT_instMonadControl___aux__3(v_00_u03c9_852_, v_00_u03b1_853_, v_00_u03b2_854_, v_m_855_, v_inst_856_, v_inst_857_, v_inst_858_, v_00_u03b1_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_inst_858_);
lean_dec_ref(v_inst_857_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_inc_ref(v_inst_865_);
lean_inc_ref(v_inst_864_);
v___x_866_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__1___boxed), 10, 7);
lean_closure_set(v___x_866_, 0, lean_box(0));
lean_closure_set(v___x_866_, 1, lean_box(0));
lean_closure_set(v___x_866_, 2, lean_box(0));
lean_closure_set(v___x_866_, 3, lean_box(0));
lean_closure_set(v___x_866_, 4, v_inst_863_);
lean_closure_set(v___x_866_, 5, v_inst_864_);
lean_closure_set(v___x_866_, 6, v_inst_865_);
v___x_867_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadControl___aux__3___boxed), 10, 7);
lean_closure_set(v___x_867_, 0, lean_box(0));
lean_closure_set(v___x_867_, 1, lean_box(0));
lean_closure_set(v___x_867_, 2, lean_box(0));
lean_closure_set(v___x_867_, 3, lean_box(0));
lean_closure_set(v___x_867_, 4, v_inst_863_);
lean_closure_set(v___x_867_, 5, v_inst_864_);
lean_closure_set(v___x_867_, 6, v_inst_865_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl(lean_object* v_00_u03c9_869_, lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_m_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_inst_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_inst_873_, v_inst_874_, v_inst_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object* v_f_877_, lean_object* v_a_878_, lean_object* v_a_x3f_879_){
_start:
{
lean_object* v___x_880_; 
lean_inc(v_a_878_);
v___x_880_ = lean_apply_2(v_f_877_, v_a_x3f_879_, v_a_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(lean_object* v_f_881_, lean_object* v_a_882_, lean_object* v_a_x3f_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(v_f_881_, v_a_882_, v_a_x3f_883_);
lean_dec(v_a_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(lean_object* v_inst_885_, lean_object* v_x_886_, lean_object* v_f_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_inc(v_a_888_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_889_, 0, v_f_887_);
lean_closure_set(v___f_889_, 1, v_a_888_);
lean_inc(v_a_888_);
v___x_890_ = lean_apply_1(v_x_886_, v_a_888_);
v___x_891_ = lean_apply_4(v_inst_885_, lean_box(0), lean_box(0), v___x_890_, v___f_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(lean_object* v_inst_892_, lean_object* v_x_893_, lean_object* v_f_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(v_inst_892_, v_x_893_, v_f_894_, v_a_895_);
lean_dec(v_a_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1(lean_object* v_00_u03c9_897_, lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_x_907_, lean_object* v_f_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_a_909_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_910_, 0, v_f_908_);
lean_closure_set(v___f_910_, 1, v_a_909_);
lean_inc(v_a_909_);
v___x_911_ = lean_apply_1(v_x_907_, v_a_909_);
v___x_912_ = lean_apply_4(v_inst_904_, lean_box(0), lean_box(0), v___x_911_, v___f_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(lean_object* v_00_u03c9_913_, lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_m_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_f_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_MonadCacheT_instMonadFinally___aux__1(v_00_u03c9_913_, v_00_u03b1_914_, v_00_u03b2_915_, v_m_916_, v_inst_917_, v_inst_918_, v_inst_919_, v_inst_920_, v_00_u03b1_921_, v_00_u03b2_922_, v_x_923_, v_f_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_inst_919_);
lean_dec_ref(v_inst_918_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___redArg(lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_inst_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed), 13, 8);
lean_closure_set(v___x_931_, 0, lean_box(0));
lean_closure_set(v___x_931_, 1, lean_box(0));
lean_closure_set(v___x_931_, 2, lean_box(0));
lean_closure_set(v___x_931_, 3, lean_box(0));
lean_closure_set(v___x_931_, 4, v_inst_927_);
lean_closure_set(v___x_931_, 5, v_inst_928_);
lean_closure_set(v___x_931_, 6, v_inst_929_);
lean_closure_set(v___x_931_, 7, v_inst_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally(lean_object* v_00_u03c9_932_, lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_m_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed), 13, 8);
lean_closure_set(v___x_940_, 0, lean_box(0));
lean_closure_set(v___x_940_, 1, lean_box(0));
lean_closure_set(v___x_940_, 2, lean_box(0));
lean_closure_set(v___x_940_, 3, lean_box(0));
lean_closure_set(v___x_940_, 4, v_inst_936_);
lean_closure_set(v___x_940_, 5, v_inst_937_);
lean_closure_set(v___x_940_, 6, v_inst_938_);
lean_closure_set(v___x_940_, 7, v_inst_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(lean_object* v_inst_941_){
_start:
{
lean_object* v_getRef_942_; 
v_getRef_942_ = lean_ctor_get(v_inst_941_, 0);
lean_inc(v_getRef_942_);
return v_getRef_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(lean_object* v_inst_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(v_inst_943_);
lean_dec_ref(v_inst_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1(lean_object* v_00_u03c9_945_, lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_m_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_getRef_954_; 
v_getRef_954_ = lean_ctor_get(v_inst_952_, 0);
lean_inc(v_getRef_954_);
return v_getRef_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(lean_object* v_00_u03c9_955_, lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MonadCacheT_instMonadRef___aux__1(v_00_u03c9_955_, v_00_u03b1_956_, v_00_u03b2_957_, v_m_958_, v_inst_959_, v_inst_960_, v_inst_961_, v_inst_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(lean_object* v_inst_965_, lean_object* v_ref_966_, lean_object* v_x_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_withRef_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_withRef_969_ = lean_ctor_get(v_inst_965_, 1);
lean_inc(v_withRef_969_);
lean_dec_ref(v_inst_965_);
lean_inc(v_a_968_);
v___x_970_ = lean_apply_1(v_x_967_, v_a_968_);
v___x_971_ = lean_apply_3(v_withRef_969_, lean_box(0), v_ref_966_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(lean_object* v_inst_972_, lean_object* v_ref_973_, lean_object* v_x_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(v_inst_972_, v_ref_973_, v_x_974_, v_a_975_);
lean_dec(v_a_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3(lean_object* v_00_u03c9_977_, lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_00_u03b1_985_, lean_object* v_ref_986_, lean_object* v_x_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_withRef_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_withRef_989_ = lean_ctor_get(v_inst_984_, 1);
lean_inc(v_withRef_989_);
lean_dec_ref(v_inst_984_);
lean_inc(v_a_988_);
v___x_990_ = lean_apply_1(v_x_987_, v_a_988_);
v___x_991_ = lean_apply_3(v_withRef_989_, lean_box(0), v_ref_986_, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(lean_object* v_00_u03c9_992_, lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_m_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_00_u03b1_1000_, lean_object* v_ref_1001_, lean_object* v_x_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_MonadCacheT_instMonadRef___aux__3(v_00_u03c9_992_, v_00_u03b1_993_, v_00_u03b2_994_, v_m_995_, v_inst_996_, v_inst_997_, v_inst_998_, v_inst_999_, v_00_u03b1_1000_, v_ref_1001_, v_x_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_inst_998_);
lean_dec_ref(v_inst_997_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___redArg(lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc_ref(v_inst_1008_);
lean_inc_ref(v_inst_1007_);
lean_inc_ref(v_inst_1006_);
v___x_1009_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadRef___aux__1___boxed), 9, 8);
lean_closure_set(v___x_1009_, 0, lean_box(0));
lean_closure_set(v___x_1009_, 1, lean_box(0));
lean_closure_set(v___x_1009_, 2, lean_box(0));
lean_closure_set(v___x_1009_, 3, lean_box(0));
lean_closure_set(v___x_1009_, 4, v_inst_1005_);
lean_closure_set(v___x_1009_, 5, v_inst_1006_);
lean_closure_set(v___x_1009_, 6, v_inst_1007_);
lean_closure_set(v___x_1009_, 7, v_inst_1008_);
v___x_1010_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadRef___aux__3___boxed), 12, 8);
lean_closure_set(v___x_1010_, 0, lean_box(0));
lean_closure_set(v___x_1010_, 1, lean_box(0));
lean_closure_set(v___x_1010_, 2, lean_box(0));
lean_closure_set(v___x_1010_, 3, lean_box(0));
lean_closure_set(v___x_1010_, 4, v_inst_1005_);
lean_closure_set(v___x_1010_, 5, v_inst_1006_);
lean_closure_set(v___x_1010_, 6, v_inst_1007_);
lean_closure_set(v___x_1010_, 7, v_inst_1008_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef(lean_object* v_00_u03c9_1012_, lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_m_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_MonadCacheT_instMonadRef___redArg(v_inst_1016_, v_inst_1017_, v_inst_1018_, v_inst_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___redArg(lean_object* v_inst_1021_){
_start:
{
lean_object* v_failure_1022_; lean_object* v___x_1023_; 
v_failure_1022_ = lean_ctor_get(v_inst_1021_, 1);
lean_inc(v_failure_1022_);
lean_dec_ref(v_inst_1021_);
v___x_1023_ = lean_apply_1(v_failure_1022_, lean_box(0));
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1(lean_object* v_00_u03c9_1024_, lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_m_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_00_u03b1_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_failure_1034_; lean_object* v___x_1035_; 
v_failure_1034_ = lean_ctor_get(v_inst_1031_, 1);
lean_inc(v_failure_1034_);
lean_dec_ref(v_inst_1031_);
v___x_1035_ = lean_apply_1(v_failure_1034_, lean_box(0));
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__1___boxed(lean_object* v_00_u03c9_1036_, lean_object* v_00_u03b1_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_00_u03b1_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_MonadCacheT_instAlternative___aux__1(v_00_u03c9_1036_, v_00_u03b1_1037_, v_00_u03b2_1038_, v_m_1039_, v_inst_1040_, v_inst_1041_, v_inst_1042_, v_inst_1043_, v_00_u03b1_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_inst_1042_);
lean_dec_ref(v_inst_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg(lean_object* v_inst_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_orElse_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_orElse_1051_ = lean_ctor_get(v_inst_1047_, 2);
lean_inc(v_orElse_1051_);
lean_dec_ref(v_inst_1047_);
lean_inc(v_a_1050_);
v___f_1052_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1052_, 0, v_a_1049_);
lean_closure_set(v___f_1052_, 1, v_a_1050_);
lean_inc(v_a_1050_);
v___x_1053_ = lean_apply_1(v_a_1048_, v_a_1050_);
v___x_1054_ = lean_apply_3(v_orElse_1051_, lean_box(0), v___x_1053_, v___f_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(lean_object* v_inst_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(v_inst_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3(lean_object* v_00_u03c9_1060_, lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_m_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_00_u03b1_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_orElse_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_orElse_1072_ = lean_ctor_get(v_inst_1067_, 2);
lean_inc(v_orElse_1072_);
lean_dec_ref(v_inst_1067_);
lean_inc(v_a_1071_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1073_, 0, v_a_1070_);
lean_closure_set(v___f_1073_, 1, v_a_1071_);
lean_inc(v_a_1071_);
v___x_1074_ = lean_apply_1(v_a_1069_, v_a_1071_);
v___x_1075_ = lean_apply_3(v_orElse_1072_, lean_box(0), v___x_1074_, v___f_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___boxed(lean_object* v_00_u03c9_1076_, lean_object* v_00_u03b1_1077_, lean_object* v_00_u03b2_1078_, lean_object* v_m_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_00_u03b1_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_MonadCacheT_instAlternative___aux__3(v_00_u03c9_1076_, v_00_u03b1_1077_, v_00_u03b2_1078_, v_m_1079_, v_inst_1080_, v_inst_1081_, v_inst_1082_, v_inst_1083_, v_00_u03b1_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_inst_1082_);
lean_dec_ref(v_inst_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v_toApplicative_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v_inst_1091_);
lean_inc_ref(v_inst_1090_);
v___x_1094_ = l_Lean_MonadCacheT_instMonad___redArg(v_inst_1089_, v_inst_1090_, v_inst_1091_, v_inst_1092_);
v_toApplicative_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_toApplicative_1095_);
lean_dec_ref(v___x_1094_);
lean_inc_ref(v_inst_1093_);
lean_inc_ref(v_inst_1091_);
lean_inc_ref(v_inst_1090_);
v___x_1096_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__1___boxed), 10, 8);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, lean_box(0));
lean_closure_set(v___x_1096_, 2, lean_box(0));
lean_closure_set(v___x_1096_, 3, lean_box(0));
lean_closure_set(v___x_1096_, 4, v_inst_1089_);
lean_closure_set(v___x_1096_, 5, v_inst_1090_);
lean_closure_set(v___x_1096_, 6, v_inst_1091_);
lean_closure_set(v___x_1096_, 7, v_inst_1093_);
v___x_1097_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___boxed), 12, 8);
lean_closure_set(v___x_1097_, 0, lean_box(0));
lean_closure_set(v___x_1097_, 1, lean_box(0));
lean_closure_set(v___x_1097_, 2, lean_box(0));
lean_closure_set(v___x_1097_, 3, lean_box(0));
lean_closure_set(v___x_1097_, 4, v_inst_1089_);
lean_closure_set(v___x_1097_, 5, v_inst_1090_);
lean_closure_set(v___x_1097_, 6, v_inst_1091_);
lean_closure_set(v___x_1097_, 7, v_inst_1093_);
v___x_1098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1098_, 0, v_toApplicative_1095_);
lean_ctor_set(v___x_1098_, 1, v___x_1096_);
lean_ctor_set(v___x_1098_, 2, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object* v_00_u03c9_1099_, lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_MonadCacheT_instAlternative___redArg(v_inst_1103_, v_inst_1104_, v_inst_1105_, v_inst_1106_, v_inst_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_inst_1109_, lean_object* v_f_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_toApplicative_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
v_toApplicative_1112_ = lean_ctor_get(v_inst_1109_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_inst_1109_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_inst_1109_, 1);
lean_dec(v_unused_1124_);
v___x_1114_ = v_inst_1109_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_toApplicative_1112_);
lean_dec(v_inst_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_toPure_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_toPure_1116_ = lean_ctor_get(v_toApplicative_1112_, 1);
lean_inc(v_toPure_1116_);
lean_dec_ref(v_toApplicative_1112_);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_apply_1(v_f_1110_, v___y_1111_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1118_);
lean_ctor_set(v___x_1114_, 0, v___x_1117_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_apply_2(v_toPure_1116_, lean_box(0), v___x_1120_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_1125_){
_start:
{
lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc_ref(v_inst_1125_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1126_, 0, v_inst_1125_);
v___x_1127_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_1127_, 0, lean_box(0));
lean_closure_set(v___x_1127_, 1, lean_box(0));
lean_closure_set(v___x_1127_, 2, v_inst_1125_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___f_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_m_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(v_00_u03b1_1136_, v_00_u03b2_1137_, v_m_1138_, v_inst_1139_, v_inst_1140_, v_inst_1141_);
lean_dec_ref(v_inst_1140_);
lean_dec_ref(v_inst_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0(lean_object* v_x_1143_){
_start:
{
lean_object* v_fst_1144_; 
v_fst_1144_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_fst_1144_);
return v_fst_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(lean_object* v_x_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_1145_);
lean_dec_ref(v_x_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg(lean_object* v_inst_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v_toApplicative_1150_; lean_object* v_toFunctor_1151_; lean_object* v_map_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_toApplicative_1150_ = lean_ctor_get(v_inst_1148_, 0);
lean_inc_ref(v_toApplicative_1150_);
lean_dec_ref(v_inst_1148_);
v_toFunctor_1151_ = lean_ctor_get(v_toApplicative_1150_, 0);
lean_inc_ref(v_toFunctor_1151_);
lean_dec_ref(v_toApplicative_1150_);
v_map_1152_ = lean_ctor_get(v_toFunctor_1151_, 0);
lean_inc(v_map_1152_);
lean_dec_ref(v_toFunctor_1151_);
v___f_1153_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1154_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_1155_ = lean_apply_1(v_x_1149_, v___x_1154_);
v___x_1156_ = lean_apply_4(v_map_1152_, lean_box(0), lean_box(0), v___f_1153_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_00_u03c3_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_toApplicative_1165_; lean_object* v_toFunctor_1166_; lean_object* v_map_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_toApplicative_1165_ = lean_ctor_get(v_inst_1162_, 0);
lean_inc_ref(v_toApplicative_1165_);
lean_dec_ref(v_inst_1162_);
v_toFunctor_1166_ = lean_ctor_get(v_toApplicative_1165_, 0);
lean_inc_ref(v_toFunctor_1166_);
lean_dec_ref(v_toApplicative_1165_);
v_map_1167_ = lean_ctor_get(v_toFunctor_1166_, 0);
lean_inc(v_map_1167_);
lean_dec_ref(v_toFunctor_1166_);
v___f_1168_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1169_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_1170_ = lean_apply_1(v_x_1164_, v___x_1169_);
v___x_1171_ = lean_apply_4(v_map_1167_, lean_box(0), lean_box(0), v___f_1168_, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_00_u03c3_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_MonadStateCacheT_run(v_00_u03b1_1172_, v_00_u03b2_1173_, v_m_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_, v_00_u03c3_1178_, v_x_1179_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_inst_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(lean_object* v_f_1181_, lean_object* v_toPure_1182_, lean_object* v_____x_1183_){
_start:
{
lean_object* v_fst_1184_; lean_object* v_snd_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1194_; 
v_fst_1184_ = lean_ctor_get(v_____x_1183_, 0);
v_snd_1185_ = lean_ctor_get(v_____x_1183_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_____x_1183_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1187_ = v_____x_1183_;
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snd_1185_);
lean_inc(v_fst_1184_);
lean_dec(v_____x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_apply_1(v_f_1181_, v_fst_1184_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_snd_1185_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_apply_2(v_toPure_1182_, lean_box(0), v___x_1191_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(lean_object* v_inst_1195_, lean_object* v_f_1196_, lean_object* v_x_1197_, lean_object* v_a_1198_){
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
v___x_1202_ = lean_apply_1(v_x_1197_, v_a_1198_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v_f_1196_);
lean_closure_set(v___f_1203_, 1, v_toPure_1201_);
v___x_1204_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v___x_1202_, v___f_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_f_1213_, lean_object* v_x_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_toApplicative_1216_; lean_object* v_toBind_1217_; lean_object* v_toPure_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; 
v_toApplicative_1216_ = lean_ctor_get(v_inst_1210_, 0);
lean_inc_ref(v_toApplicative_1216_);
v_toBind_1217_ = lean_ctor_get(v_inst_1210_, 1);
lean_inc(v_toBind_1217_);
lean_dec_ref(v_inst_1210_);
v_toPure_1218_ = lean_ctor_get(v_toApplicative_1216_, 1);
lean_inc(v_toPure_1218_);
lean_dec_ref(v_toApplicative_1216_);
v___x_1219_ = lean_apply_1(v_x_1214_, v_a_1215_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1220_, 0, v_f_1213_);
lean_closure_set(v___f_1220_, 1, v_toPure_1218_);
v___x_1221_ = lean_apply_4(v_toBind_1217_, lean_box(0), lean_box(0), v___x_1219_, v___f_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_m_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_f_1230_, lean_object* v_x_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_MonadStateCacheT_instMonad___aux__1(v_00_u03b1_1222_, v_00_u03b2_1223_, v_m_1224_, v_inst_1225_, v_inst_1226_, v_inst_1227_, v_00_u03b1_1228_, v_00_u03b2_1229_, v_f_1230_, v_x_1231_, v_a_1232_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v_inst_1225_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(lean_object* v_a_1234_, lean_object* v_toPure_1235_, lean_object* v_____x_1236_){
_start:
{
lean_object* v_snd_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_snd_1237_ = lean_ctor_get(v_____x_1236_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_____x_1236_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_____x_1236_, 0);
lean_dec(v_unused_1246_);
v___x_1239_ = v_____x_1236_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1237_);
lean_dec(v_____x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_a_1234_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1234_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_snd_1237_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_apply_2(v_toPure_1235_, lean_box(0), v___x_1242_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(lean_object* v_inst_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toBind_1252_; lean_object* v_toPure_1253_; lean_object* v___x_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc_ref(v_toApplicative_1251_);
v_toBind_1252_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc(v_toBind_1252_);
lean_dec_ref(v_inst_1247_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1251_, 1);
lean_inc(v_toPure_1253_);
lean_dec_ref(v_toApplicative_1251_);
v___x_1254_ = lean_apply_1(v_a_1249_, v_a_1250_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1255_, 0, v_a_1248_);
lean_closure_set(v___f_1255_, 1, v_toPure_1253_);
v___x_1256_ = lean_apply_4(v_toBind_1252_, lean_box(0), lean_box(0), v___x_1254_, v___f_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_m_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_00_u03b1_1263_, lean_object* v_00_u03b2_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_toApplicative_1268_; lean_object* v_toBind_1269_; lean_object* v_toPure_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v_toApplicative_1268_ = lean_ctor_get(v_inst_1262_, 0);
lean_inc_ref(v_toApplicative_1268_);
v_toBind_1269_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc(v_toBind_1269_);
lean_dec_ref(v_inst_1262_);
v_toPure_1270_ = lean_ctor_get(v_toApplicative_1268_, 1);
lean_inc(v_toPure_1270_);
lean_dec_ref(v_toApplicative_1268_);
v___x_1271_ = lean_apply_1(v_a_1266_, v_a_1267_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1272_, 0, v_a_1265_);
lean_closure_set(v___f_1272_, 1, v_toPure_1270_);
v___x_1273_ = lean_apply_4(v_toBind_1269_, lean_box(0), lean_box(0), v___x_1271_, v___f_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_MonadStateCacheT_instMonad___aux__3(v_00_u03b1_1274_, v_00_u03b2_1275_, v_m_1276_, v_inst_1277_, v_inst_1278_, v_inst_1279_, v_00_u03b1_1280_, v_00_u03b2_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(lean_object* v_inst_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_toApplicative_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1298_; 
v_toApplicative_1289_ = lean_ctor_get(v_inst_1286_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_inst_1286_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_inst_1286_, 1);
lean_dec(v_unused_1299_);
v___x_1291_ = v_inst_1286_;
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_toApplicative_1289_);
lean_dec(v_inst_1286_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_toPure_1293_; lean_object* v___x_1295_; 
v_toPure_1293_ = lean_ctor_get(v_toApplicative_1289_, 1);
lean_inc(v_toPure_1293_);
lean_dec_ref(v_toApplicative_1289_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v_a_1288_);
lean_ctor_set(v___x_1291_, 0, v_a_1287_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1288_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_apply_2(v_toPure_1293_, lean_box(0), v___x_1295_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5(lean_object* v_00_u03b1_1300_, lean_object* v_00_u03b2_1301_, lean_object* v_m_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_00_u03b1_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_toApplicative_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1318_; 
v_toApplicative_1309_ = lean_ctor_get(v_inst_1305_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_inst_1305_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_inst_1305_, 1);
lean_dec(v_unused_1319_);
v___x_1311_ = v_inst_1305_;
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_toApplicative_1309_);
lean_dec(v_inst_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_toPure_1313_; lean_object* v___x_1315_; 
v_toPure_1313_ = lean_ctor_get(v_toApplicative_1309_, 1);
lean_inc(v_toPure_1313_);
lean_dec_ref(v_toApplicative_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v_a_1308_);
lean_ctor_set(v___x_1311_, 0, v_a_1307_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_a_1308_);
v___x_1315_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1315_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_00_u03b2_1321_, lean_object* v_m_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_00_u03b1_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_MonadStateCacheT_instMonad___aux__5(v_00_u03b1_1320_, v_00_u03b2_1321_, v_m_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_00_u03b1_1326_, v_a_1327_, v_a_1328_);
lean_dec_ref(v_inst_1324_);
lean_dec_ref(v_inst_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(lean_object* v_fst_1330_, lean_object* v_toPure_1331_, lean_object* v_____x_1332_){
_start:
{
lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_fst_1333_ = lean_ctor_get(v_____x_1332_, 0);
v_snd_1334_ = lean_ctor_get(v_____x_1332_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_____x_1332_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1336_ = v_____x_1332_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1334_);
lean_inc(v_fst_1333_);
lean_dec(v_____x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_apply_1(v_fst_1330_, v_fst_1333_);
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
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_snd_1334_);
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
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(lean_object* v_toApplicative_1344_, lean_object* v_x_1345_, lean_object* v_toBind_1346_, lean_object* v_____x_1347_){
_start:
{
lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v_toPure_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; 
v_fst_1348_ = lean_ctor_get(v_____x_1347_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v_____x_1347_, 1);
lean_inc(v_snd_1349_);
lean_dec_ref(v_____x_1347_);
v_toPure_1350_ = lean_ctor_get(v_toApplicative_1344_, 1);
lean_inc(v_toPure_1350_);
lean_dec_ref(v_toApplicative_1344_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_apply_2(v_x_1345_, v___x_1351_, v_snd_1349_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1353_, 0, v_fst_1348_);
lean_closure_set(v___f_1353_, 1, v_toPure_1350_);
v___x_1354_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1352_, v___f_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(lean_object* v_inst_1355_, lean_object* v_f_1356_, lean_object* v_x_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_toApplicative_1359_; lean_object* v_toBind_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_toApplicative_1359_ = lean_ctor_get(v_inst_1355_, 0);
lean_inc_ref(v_toApplicative_1359_);
v_toBind_1360_ = lean_ctor_get(v_inst_1355_, 1);
lean_inc(v_toBind_1360_);
lean_dec_ref(v_inst_1355_);
lean_inc(v_toBind_1360_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1361_, 0, v_toApplicative_1359_);
lean_closure_set(v___f_1361_, 1, v_x_1357_);
lean_closure_set(v___f_1361_, 2, v_toBind_1360_);
v___x_1362_ = lean_apply_1(v_f_1356_, v_a_1358_);
v___x_1363_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1362_, v___f_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7(lean_object* v_00_u03b1_1364_, lean_object* v_00_u03b2_1365_, lean_object* v_m_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_f_1372_, lean_object* v_x_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_toApplicative_1375_; lean_object* v_toBind_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_toApplicative_1375_ = lean_ctor_get(v_inst_1369_, 0);
lean_inc_ref(v_toApplicative_1375_);
v_toBind_1376_ = lean_ctor_get(v_inst_1369_, 1);
lean_inc(v_toBind_1376_);
lean_dec_ref(v_inst_1369_);
lean_inc(v_toBind_1376_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1377_, 0, v_toApplicative_1375_);
lean_closure_set(v___f_1377_, 1, v_x_1373_);
lean_closure_set(v___f_1377_, 2, v_toBind_1376_);
v___x_1378_ = lean_apply_1(v_f_1372_, v_a_1374_);
v___x_1379_ = lean_apply_4(v_toBind_1376_, lean_box(0), lean_box(0), v___x_1378_, v___f_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_m_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_f_1388_, lean_object* v_x_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_MonadStateCacheT_instMonad___aux__7(v_00_u03b1_1380_, v_00_u03b2_1381_, v_m_1382_, v_inst_1383_, v_inst_1384_, v_inst_1385_, v_00_u03b1_1386_, v_00_u03b2_1387_, v_f_1388_, v_x_1389_, v_a_1390_);
lean_dec_ref(v_inst_1384_);
lean_dec_ref(v_inst_1383_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(lean_object* v_toApplicative_1392_, lean_object* v_fst_1393_, lean_object* v_____x_1394_){
_start:
{
lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1404_; 
v_snd_1395_ = lean_ctor_get(v_____x_1394_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_____x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_____x_1394_, 0);
lean_dec(v_unused_1405_);
v___x_1397_ = v_____x_1394_;
v_isShared_1398_ = v_isSharedCheck_1404_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_dec(v_____x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1404_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_toPure_1399_; lean_object* v___x_1401_; 
v_toPure_1399_ = lean_ctor_get(v_toApplicative_1392_, 1);
lean_inc(v_toPure_1399_);
lean_dec_ref(v_toApplicative_1392_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_fst_1393_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_fst_1393_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1395_);
v___x_1401_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_apply_2(v_toPure_1399_, lean_box(0), v___x_1401_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(lean_object* v_toApplicative_1406_, lean_object* v_y_1407_, lean_object* v_toBind_1408_, lean_object* v_____x_1409_){
_start:
{
lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_fst_1410_ = lean_ctor_get(v_____x_1409_, 0);
lean_inc(v_fst_1410_);
v_snd_1411_ = lean_ctor_get(v_____x_1409_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v_____x_1409_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1412_, 0, v_toApplicative_1406_);
lean_closure_set(v___f_1412_, 1, v_fst_1410_);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_apply_2(v_y_1407_, v___x_1413_, v_snd_1411_);
v___x_1415_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1414_, v___f_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(lean_object* v_inst_1416_, lean_object* v_x_1417_, lean_object* v_y_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_toApplicative_1420_; lean_object* v_toBind_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_toApplicative_1420_ = lean_ctor_get(v_inst_1416_, 0);
lean_inc_ref(v_toApplicative_1420_);
v_toBind_1421_ = lean_ctor_get(v_inst_1416_, 1);
lean_inc(v_toBind_1421_);
lean_dec_ref(v_inst_1416_);
lean_inc(v_toBind_1421_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1422_, 0, v_toApplicative_1420_);
lean_closure_set(v___f_1422_, 1, v_y_1418_);
lean_closure_set(v___f_1422_, 2, v_toBind_1421_);
v___x_1423_ = lean_apply_1(v_x_1417_, v_a_1419_);
v___x_1424_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v___x_1423_, v___f_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_x_1433_, lean_object* v_y_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_toApplicative_1436_; lean_object* v_toBind_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_toApplicative_1436_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1436_);
v_toBind_1437_ = lean_ctor_get(v_inst_1430_, 1);
lean_inc(v_toBind_1437_);
lean_dec_ref(v_inst_1430_);
lean_inc(v_toBind_1437_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1438_, 0, v_toApplicative_1436_);
lean_closure_set(v___f_1438_, 1, v_y_1434_);
lean_closure_set(v___f_1438_, 2, v_toBind_1437_);
v___x_1439_ = lean_apply_1(v_x_1433_, v_a_1435_);
v___x_1440_ = lean_apply_4(v_toBind_1437_, lean_box(0), lean_box(0), v___x_1439_, v___f_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(lean_object* v_00_u03b1_1441_, lean_object* v_00_u03b2_1442_, lean_object* v_m_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_x_1449_, lean_object* v_y_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_MonadStateCacheT_instMonad___aux__9(v_00_u03b1_1441_, v_00_u03b2_1442_, v_m_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_00_u03b1_1447_, v_00_u03b2_1448_, v_x_1449_, v_y_1450_, v_a_1451_);
lean_dec_ref(v_inst_1445_);
lean_dec_ref(v_inst_1444_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(lean_object* v_y_1453_, lean_object* v_____x_1454_){
_start:
{
lean_object* v_snd_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_snd_1455_ = lean_ctor_get(v_____x_1454_, 1);
lean_inc(v_snd_1455_);
lean_dec_ref(v_____x_1454_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_apply_2(v_y_1453_, v___x_1456_, v_snd_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(lean_object* v_inst_1458_, lean_object* v_x_1459_, lean_object* v_y_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_toBind_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_toBind_1462_ = lean_ctor_get(v_inst_1458_, 1);
lean_inc(v_toBind_1462_);
lean_dec_ref(v_inst_1458_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1463_, 0, v_y_1460_);
v___x_1464_ = lean_apply_1(v_x_1459_, v_a_1461_);
v___x_1465_ = lean_apply_4(v_toBind_1462_, lean_box(0), lean_box(0), v___x_1464_, v___f_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11(lean_object* v_00_u03b1_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_x_1474_, lean_object* v_y_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_toBind_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_toBind_1477_ = lean_ctor_get(v_inst_1471_, 1);
lean_inc(v_toBind_1477_);
lean_dec_ref(v_inst_1471_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1478_, 0, v_y_1475_);
v___x_1479_ = lean_apply_1(v_x_1474_, v_a_1476_);
v___x_1480_ = lean_apply_4(v_toBind_1477_, lean_box(0), lean_box(0), v___x_1479_, v___f_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_m_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_00_u03b1_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_x_1489_, lean_object* v_y_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_MonadStateCacheT_instMonad___aux__11(v_00_u03b1_1481_, v_00_u03b2_1482_, v_m_1483_, v_inst_1484_, v_inst_1485_, v_inst_1486_, v_00_u03b1_1487_, v_00_u03b2_1488_, v_x_1489_, v_y_1490_, v_a_1491_);
lean_dec_ref(v_inst_1485_);
lean_dec_ref(v_inst_1484_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_f_1493_, lean_object* v_____x_1494_){
_start:
{
lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1497_; 
v_fst_1495_ = lean_ctor_get(v_____x_1494_, 0);
lean_inc(v_fst_1495_);
v_snd_1496_ = lean_ctor_get(v_____x_1494_, 1);
lean_inc(v_snd_1496_);
lean_dec_ref(v_____x_1494_);
v___x_1497_ = lean_apply_2(v_f_1493_, v_fst_1495_, v_snd_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(lean_object* v_inst_1498_, lean_object* v_x_1499_, lean_object* v_f_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_toBind_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_toBind_1502_ = lean_ctor_get(v_inst_1498_, 1);
lean_inc(v_toBind_1502_);
lean_dec_ref(v_inst_1498_);
v___f_1503_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1503_, 0, v_f_1500_);
v___x_1504_ = lean_apply_1(v_x_1499_, v_a_1501_);
v___x_1505_ = lean_apply_4(v_toBind_1502_, lean_box(0), lean_box(0), v___x_1504_, v___f_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13(lean_object* v_00_u03b1_1506_, lean_object* v_00_u03b2_1507_, lean_object* v_m_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_x_1514_, lean_object* v_f_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_toBind_1517_; lean_object* v___f_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_toBind_1517_ = lean_ctor_get(v_inst_1511_, 1);
lean_inc(v_toBind_1517_);
lean_dec_ref(v_inst_1511_);
v___f_1518_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1518_, 0, v_f_1515_);
v___x_1519_ = lean_apply_1(v_x_1514_, v_a_1516_);
v___x_1520_ = lean_apply_4(v_toBind_1517_, lean_box(0), lean_box(0), v___x_1519_, v___f_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_00_u03b1_1527_, lean_object* v_00_u03b2_1528_, lean_object* v_x_1529_, lean_object* v_f_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_MonadStateCacheT_instMonad___aux__13(v_00_u03b1_1521_, v_00_u03b2_1522_, v_m_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_00_u03b1_1527_, v_00_u03b2_1528_, v_x_1529_, v_f_1530_, v_a_1531_);
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_inst_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1536_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___boxed), 11, 6);
lean_closure_set(v___x_1536_, 0, lean_box(0));
lean_closure_set(v___x_1536_, 1, lean_box(0));
lean_closure_set(v___x_1536_, 2, lean_box(0));
lean_closure_set(v___x_1536_, 3, v_inst_1533_);
lean_closure_set(v___x_1536_, 4, v_inst_1534_);
lean_closure_set(v___x_1536_, 5, v_inst_1535_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1537_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___boxed), 11, 6);
lean_closure_set(v___x_1537_, 0, lean_box(0));
lean_closure_set(v___x_1537_, 1, lean_box(0));
lean_closure_set(v___x_1537_, 2, lean_box(0));
lean_closure_set(v___x_1537_, 3, v_inst_1533_);
lean_closure_set(v___x_1537_, 4, v_inst_1534_);
lean_closure_set(v___x_1537_, 5, v_inst_1535_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1539_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__5___boxed), 9, 6);
lean_closure_set(v___x_1539_, 0, lean_box(0));
lean_closure_set(v___x_1539_, 1, lean_box(0));
lean_closure_set(v___x_1539_, 2, lean_box(0));
lean_closure_set(v___x_1539_, 3, v_inst_1533_);
lean_closure_set(v___x_1539_, 4, v_inst_1534_);
lean_closure_set(v___x_1539_, 5, v_inst_1535_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1540_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___boxed), 11, 6);
lean_closure_set(v___x_1540_, 0, lean_box(0));
lean_closure_set(v___x_1540_, 1, lean_box(0));
lean_closure_set(v___x_1540_, 2, lean_box(0));
lean_closure_set(v___x_1540_, 3, v_inst_1533_);
lean_closure_set(v___x_1540_, 4, v_inst_1534_);
lean_closure_set(v___x_1540_, 5, v_inst_1535_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___boxed), 11, 6);
lean_closure_set(v___x_1541_, 0, lean_box(0));
lean_closure_set(v___x_1541_, 1, lean_box(0));
lean_closure_set(v___x_1541_, 2, lean_box(0));
lean_closure_set(v___x_1541_, 3, v_inst_1533_);
lean_closure_set(v___x_1541_, 4, v_inst_1534_);
lean_closure_set(v___x_1541_, 5, v_inst_1535_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
lean_inc_ref(v_inst_1533_);
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___boxed), 11, 6);
lean_closure_set(v___x_1542_, 0, lean_box(0));
lean_closure_set(v___x_1542_, 1, lean_box(0));
lean_closure_set(v___x_1542_, 2, lean_box(0));
lean_closure_set(v___x_1542_, 3, v_inst_1533_);
lean_closure_set(v___x_1542_, 4, v_inst_1534_);
lean_closure_set(v___x_1542_, 5, v_inst_1535_);
v___x_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1538_);
lean_ctor_set(v___x_1543_, 1, v___x_1539_);
lean_ctor_set(v___x_1543_, 2, v___x_1540_);
lean_ctor_set(v___x_1543_, 3, v___x_1541_);
lean_ctor_set(v___x_1543_, 4, v___x_1542_);
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___boxed), 11, 6);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, lean_box(0));
lean_closure_set(v___x_1544_, 2, lean_box(0));
lean_closure_set(v___x_1544_, 3, v_inst_1533_);
lean_closure_set(v___x_1544_, 4, v_inst_1534_);
lean_closure_set(v___x_1544_, 5, v_inst_1535_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_m_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_1549_, v_inst_1550_, v_inst_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(lean_object* v_a_1553_, lean_object* v_toPure_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1555_);
lean_ctor_set(v___x_1556_, 1, v_a_1553_);
v___x_1557_ = lean_apply_2(v_toPure_1554_, lean_box(0), v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(lean_object* v_inst_1558_, lean_object* v_t_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_toApplicative_1561_; lean_object* v_toBind_1562_; lean_object* v_toPure_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; 
v_toApplicative_1561_ = lean_ctor_get(v_inst_1558_, 0);
lean_inc_ref(v_toApplicative_1561_);
v_toBind_1562_ = lean_ctor_get(v_inst_1558_, 1);
lean_inc(v_toBind_1562_);
lean_dec_ref(v_inst_1558_);
v_toPure_1563_ = lean_ctor_get(v_toApplicative_1561_, 1);
lean_inc(v_toPure_1563_);
lean_dec_ref(v_toApplicative_1561_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1564_, 0, v_a_1560_);
lean_closure_set(v___f_1564_, 1, v_toPure_1563_);
v___x_1565_ = lean_apply_4(v_toBind_1562_, lean_box(0), lean_box(0), v_t_1559_, v___f_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1(lean_object* v_00_u03b1_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_00_u03b1_1572_, lean_object* v_t_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_toApplicative_1575_; lean_object* v_toBind_1576_; lean_object* v_toPure_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v_toApplicative_1575_ = lean_ctor_get(v_inst_1571_, 0);
lean_inc_ref(v_toApplicative_1575_);
v_toBind_1576_ = lean_ctor_get(v_inst_1571_, 1);
lean_inc(v_toBind_1576_);
lean_dec_ref(v_inst_1571_);
v_toPure_1577_ = lean_ctor_get(v_toApplicative_1575_, 1);
lean_inc(v_toPure_1577_);
lean_dec_ref(v_toApplicative_1575_);
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1578_, 0, v_a_1574_);
lean_closure_set(v___f_1578_, 1, v_toPure_1577_);
v___x_1579_ = lean_apply_4(v_toBind_1576_, lean_box(0), lean_box(0), v_t_1573_, v___f_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_m_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_00_u03b1_1586_, lean_object* v_t_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_MonadStateCacheT_instMonadLift___aux__1(v_00_u03b1_1580_, v_00_u03b2_1581_, v_m_1582_, v_inst_1583_, v_inst_1584_, v_inst_1585_, v_00_u03b1_1586_, v_t_1587_, v_a_1588_);
lean_dec_ref(v_inst_1584_);
lean_dec_ref(v_inst_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1593_, 0, lean_box(0));
lean_closure_set(v___x_1593_, 1, lean_box(0));
lean_closure_set(v___x_1593_, 2, lean_box(0));
lean_closure_set(v___x_1593_, 3, v_inst_1590_);
lean_closure_set(v___x_1593_, 4, v_inst_1591_);
lean_closure_set(v___x_1593_, 5, v_inst_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object* v_00_u03b1_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_m_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1600_, 0, lean_box(0));
lean_closure_set(v___x_1600_, 1, lean_box(0));
lean_closure_set(v___x_1600_, 2, lean_box(0));
lean_closure_set(v___x_1600_, 3, v_inst_1597_);
lean_closure_set(v___x_1600_, 4, v_inst_1598_);
lean_closure_set(v___x_1600_, 5, v_inst_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_toApplicative_1605_; lean_object* v_throw_1606_; lean_object* v_toBind_1607_; lean_object* v_toPure_1608_; lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; 
v_toApplicative_1605_ = lean_ctor_get(v_inst_1601_, 0);
lean_inc_ref(v_toApplicative_1605_);
v_throw_1606_ = lean_ctor_get(v_inst_1602_, 0);
lean_inc(v_throw_1606_);
lean_dec_ref(v_inst_1602_);
v_toBind_1607_ = lean_ctor_get(v_inst_1601_, 1);
lean_inc(v_toBind_1607_);
lean_dec_ref(v_inst_1601_);
v_toPure_1608_ = lean_ctor_get(v_toApplicative_1605_, 1);
lean_inc(v_toPure_1608_);
lean_dec_ref(v_toApplicative_1605_);
v___x_1609_ = lean_apply_2(v_throw_1606_, lean_box(0), v_a_1603_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1610_, 0, v_a_1604_);
lean_closure_set(v___f_1610_, 1, v_toPure_1608_);
v___x_1611_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1609_, v___f_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(lean_object* v_00_u03b1_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_00_u03b5_1618_, lean_object* v_inst_1619_, lean_object* v_00_u03b1_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_toApplicative_1623_; lean_object* v_throw_1624_; lean_object* v_toBind_1625_; lean_object* v_toPure_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; 
v_toApplicative_1623_ = lean_ctor_get(v_inst_1617_, 0);
lean_inc_ref(v_toApplicative_1623_);
v_throw_1624_ = lean_ctor_get(v_inst_1619_, 0);
lean_inc(v_throw_1624_);
lean_dec_ref(v_inst_1619_);
v_toBind_1625_ = lean_ctor_get(v_inst_1617_, 1);
lean_inc(v_toBind_1625_);
lean_dec_ref(v_inst_1617_);
v_toPure_1626_ = lean_ctor_get(v_toApplicative_1623_, 1);
lean_inc(v_toPure_1626_);
lean_dec_ref(v_toApplicative_1623_);
v___x_1627_ = lean_apply_2(v_throw_1624_, lean_box(0), v_a_1621_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1628_, 0, v_a_1622_);
lean_closure_set(v___f_1628_, 1, v_toPure_1626_);
v___x_1629_ = lean_apply_4(v_toBind_1625_, lean_box(0), lean_box(0), v___x_1627_, v___f_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_m_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_00_u03b5_1636_, lean_object* v_inst_1637_, lean_object* v_00_u03b1_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(v_00_u03b1_1630_, v_00_u03b2_1631_, v_m_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_00_u03b5_1636_, v_inst_1637_, v_00_u03b1_1638_, v_a_1639_, v_a_1640_);
lean_dec_ref(v_inst_1634_);
lean_dec_ref(v_inst_1633_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object* v_c_1642_, lean_object* v_s_1643_, lean_object* v_e_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_apply_2(v_c_1642_, v_e_1644_, v_s_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(lean_object* v_inst_1646_, lean_object* v_x_1647_, lean_object* v_c_1648_, lean_object* v_s_1649_){
_start:
{
lean_object* v_tryCatch_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_tryCatch_1650_ = lean_ctor_get(v_inst_1646_, 1);
lean_inc(v_tryCatch_1650_);
lean_dec_ref(v_inst_1646_);
lean_inc_ref(v_s_1649_);
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1651_, 0, v_c_1648_);
lean_closure_set(v___f_1651_, 1, v_s_1649_);
v___x_1652_ = lean_apply_1(v_x_1647_, v_s_1649_);
v___x_1653_ = lean_apply_3(v_tryCatch_1650_, lean_box(0), v___x_1652_, v___f_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_m_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_00_u03b5_1659_, lean_object* v_inst_1660_, lean_object* v_00_u03b1_1661_, lean_object* v_x_1662_, lean_object* v_c_1663_, lean_object* v_s_1664_){
_start:
{
lean_object* v_tryCatch_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_tryCatch_1665_ = lean_ctor_get(v_inst_1660_, 1);
lean_inc(v_tryCatch_1665_);
lean_dec_ref(v_inst_1660_);
lean_inc_ref(v_s_1664_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1666_, 0, v_c_1663_);
lean_closure_set(v___f_1666_, 1, v_s_1664_);
v___x_1667_ = lean_apply_1(v_x_1662_, v_s_1664_);
v___x_1668_ = lean_apply_3(v_tryCatch_1665_, lean_box(0), v___x_1667_, v___f_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_m_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_00_u03b5_1674_, lean_object* v_inst_1675_, lean_object* v_00_u03b1_1676_, lean_object* v_x_1677_, lean_object* v_c_1678_, lean_object* v_s_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(v_00_u03b1_1669_, v_00_u03b2_1670_, v_m_1671_, v_inst_1672_, v_inst_1673_, v_00_u03b5_1674_, v_inst_1675_, v_00_u03b1_1676_, v_x_1677_, v_c_1678_, v_s_1679_);
lean_dec_ref(v_inst_1673_);
lean_dec_ref(v_inst_1672_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_inc_ref(v_inst_1684_);
lean_inc_ref(v_inst_1682_);
lean_inc_ref(v_inst_1681_);
v___x_1685_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed), 11, 8);
lean_closure_set(v___x_1685_, 0, lean_box(0));
lean_closure_set(v___x_1685_, 1, lean_box(0));
lean_closure_set(v___x_1685_, 2, lean_box(0));
lean_closure_set(v___x_1685_, 3, v_inst_1681_);
lean_closure_set(v___x_1685_, 4, v_inst_1682_);
lean_closure_set(v___x_1685_, 5, v_inst_1683_);
lean_closure_set(v___x_1685_, 6, lean_box(0));
lean_closure_set(v___x_1685_, 7, v_inst_1684_);
v___x_1686_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed), 11, 7);
lean_closure_set(v___x_1686_, 0, lean_box(0));
lean_closure_set(v___x_1686_, 1, lean_box(0));
lean_closure_set(v___x_1686_, 2, lean_box(0));
lean_closure_set(v___x_1686_, 3, v_inst_1681_);
lean_closure_set(v___x_1686_, 4, v_inst_1682_);
lean_closure_set(v___x_1686_, 5, lean_box(0));
lean_closure_set(v___x_1686_, 6, v_inst_1684_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object* v_00_u03b1_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_m_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_00_u03b5_1694_, lean_object* v_inst_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(v_inst_1691_, v_inst_1692_, v_inst_1693_, v_inst_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object* v_fst_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_apply_1(v_x_1699_, v_fst_1697_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(lean_object* v_snd_1701_, lean_object* v_toPure_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1703_);
lean_ctor_set(v___x_1704_, 1, v_snd_1701_);
v___x_1705_ = lean_apply_2(v_toPure_1702_, lean_box(0), v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(lean_object* v_f_1706_, lean_object* v_toPure_1707_, lean_object* v_toBind_1708_, lean_object* v_____x_1709_){
_start:
{
lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; 
v_fst_1710_ = lean_ctor_get(v_____x_1709_, 0);
lean_inc(v_fst_1710_);
v_snd_1711_ = lean_ctor_get(v_____x_1709_, 1);
lean_inc(v_snd_1711_);
lean_dec_ref(v_____x_1709_);
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1712_, 0, v_fst_1710_);
v___x_1713_ = lean_apply_1(v_f_1706_, v___f_1712_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1714_, 0, v_snd_1711_);
lean_closure_set(v___f_1714_, 1, v_toPure_1707_);
v___x_1715_ = lean_apply_4(v_toBind_1708_, lean_box(0), lean_box(0), v___x_1713_, v___f_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(lean_object* v_inst_1716_, lean_object* v_f_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_toApplicative_1719_; lean_object* v_toBind_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1731_; 
v_toApplicative_1719_ = lean_ctor_get(v_inst_1716_, 0);
v_toBind_1720_ = lean_ctor_get(v_inst_1716_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_inst_1716_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1722_ = v_inst_1716_;
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_toBind_1720_);
lean_inc(v_toApplicative_1719_);
lean_dec(v_inst_1716_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_toPure_1724_; lean_object* v___f_1725_; lean_object* v___x_1727_; 
v_toPure_1724_ = lean_ctor_get(v_toApplicative_1719_, 1);
lean_inc(v_toPure_1724_);
lean_dec_ref(v_toApplicative_1719_);
lean_inc(v_toBind_1720_);
lean_inc(v_toPure_1724_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1725_, 0, v_f_1717_);
lean_closure_set(v___f_1725_, 1, v_toPure_1724_);
lean_closure_set(v___f_1725_, 2, v_toBind_1720_);
lean_inc_ref(v_a_1718_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_a_1718_);
lean_ctor_set(v___x_1722_, 0, v_a_1718_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1718_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1718_);
v___x_1727_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_apply_2(v_toPure_1724_, lean_box(0), v___x_1727_);
v___x_1729_ = lean_apply_4(v_toBind_1720_, lean_box(0), lean_box(0), v___x_1728_, v___f_1725_);
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_m_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_00_u03b1_1738_, lean_object* v_f_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_toApplicative_1741_; lean_object* v_toBind_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1753_; 
v_toApplicative_1741_ = lean_ctor_get(v_inst_1737_, 0);
v_toBind_1742_ = lean_ctor_get(v_inst_1737_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_inst_1737_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1744_ = v_inst_1737_;
v_isShared_1745_ = v_isSharedCheck_1753_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_toBind_1742_);
lean_inc(v_toApplicative_1741_);
lean_dec(v_inst_1737_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1753_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_toPure_1746_; lean_object* v___f_1747_; lean_object* v___x_1749_; 
v_toPure_1746_ = lean_ctor_get(v_toApplicative_1741_, 1);
lean_inc(v_toPure_1746_);
lean_dec_ref(v_toApplicative_1741_);
lean_inc(v_toBind_1742_);
lean_inc(v_toPure_1746_);
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1747_, 0, v_f_1739_);
lean_closure_set(v___f_1747_, 1, v_toPure_1746_);
lean_closure_set(v___f_1747_, 2, v_toBind_1742_);
lean_inc_ref(v_a_1740_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_a_1740_);
lean_ctor_set(v___x_1744_, 0, v_a_1740_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1740_);
v___x_1749_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_apply_2(v_toPure_1746_, lean_box(0), v___x_1749_);
v___x_1751_ = lean_apply_4(v_toBind_1742_, lean_box(0), lean_box(0), v___x_1750_, v___f_1747_);
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_00_u03b1_1760_, lean_object* v_f_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_MonadStateCacheT_instMonadControl___aux__1(v_00_u03b1_1754_, v_00_u03b2_1755_, v_m_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_00_u03b1_1760_, v_f_1761_, v_a_1762_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(lean_object* v_fst_1764_, lean_object* v_toPure_1765_, lean_object* v_____x_1766_){
_start:
{
lean_object* v_snd_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
v_snd_1767_ = lean_ctor_get(v_____x_1766_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_____x_1766_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_____x_1766_, 0);
lean_dec(v_unused_1776_);
v___x_1769_ = v_____x_1766_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_snd_1767_);
lean_dec(v_____x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v_fst_1764_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_fst_1764_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_snd_1767_);
v___x_1772_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_apply_2(v_toPure_1765_, lean_box(0), v___x_1772_);
return v___x_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(lean_object* v_toPure_1777_, lean_object* v_toBind_1778_, lean_object* v_____x_1779_){
_start:
{
lean_object* v_fst_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1793_; 
v_fst_1780_ = lean_ctor_get(v_____x_1779_, 0);
lean_inc(v_fst_1780_);
lean_dec_ref(v_____x_1779_);
v_fst_1781_ = lean_ctor_get(v_fst_1780_, 0);
v_snd_1782_ = lean_ctor_get(v_fst_1780_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_fst_1780_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1784_ = v_fst_1780_;
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v_fst_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_inc(v_toPure_1777_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1786_, 0, v_fst_1781_);
lean_closure_set(v___f_1786_, 1, v_toPure_1777_);
v___x_1787_ = lean_box(0);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_snd_1782_);
v___x_1789_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_apply_2(v_toPure_1777_, lean_box(0), v___x_1789_);
v___x_1791_ = lean_apply_4(v_toBind_1778_, lean_box(0), lean_box(0), v___x_1790_, v___f_1786_);
return v___x_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2(lean_object* v_a_1794_, lean_object* v_toPure_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1796_);
lean_ctor_set(v___x_1797_, 1, v_a_1794_);
v___x_1798_ = lean_apply_2(v_toPure_1795_, lean_box(0), v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(lean_object* v_inst_1799_, lean_object* v_x_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_toApplicative_1802_; lean_object* v_toBind_1803_; lean_object* v_toPure_1804_; lean_object* v___f_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_toApplicative_1802_ = lean_ctor_get(v_inst_1799_, 0);
lean_inc_ref(v_toApplicative_1802_);
v_toBind_1803_ = lean_ctor_get(v_inst_1799_, 1);
lean_inc(v_toBind_1803_);
lean_dec_ref(v_inst_1799_);
v_toPure_1804_ = lean_ctor_get(v_toApplicative_1802_, 1);
lean_inc(v_toPure_1804_);
lean_dec_ref(v_toApplicative_1802_);
lean_inc(v_toBind_1803_);
lean_inc(v_toPure_1804_);
v___f_1805_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1805_, 0, v_toPure_1804_);
lean_closure_set(v___f_1805_, 1, v_toBind_1803_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1806_, 0, v_a_1801_);
lean_closure_set(v___f_1806_, 1, v_toPure_1804_);
lean_inc(v_toBind_1803_);
v___x_1807_ = lean_apply_4(v_toBind_1803_, lean_box(0), lean_box(0), v_x_1800_, v___f_1806_);
v___x_1808_ = lean_apply_4(v_toBind_1803_, lean_box(0), lean_box(0), v___x_1807_, v___f_1805_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_m_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_00_u03b1_1815_, lean_object* v_x_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_toApplicative_1818_; lean_object* v_toBind_1819_; lean_object* v_toPure_1820_; lean_object* v___f_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_toApplicative_1818_ = lean_ctor_get(v_inst_1814_, 0);
lean_inc_ref(v_toApplicative_1818_);
v_toBind_1819_ = lean_ctor_get(v_inst_1814_, 1);
lean_inc(v_toBind_1819_);
lean_dec_ref(v_inst_1814_);
v_toPure_1820_ = lean_ctor_get(v_toApplicative_1818_, 1);
lean_inc(v_toPure_1820_);
lean_dec_ref(v_toApplicative_1818_);
lean_inc(v_toBind_1819_);
lean_inc(v_toPure_1820_);
v___f_1821_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1821_, 0, v_toPure_1820_);
lean_closure_set(v___f_1821_, 1, v_toBind_1819_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1822_, 0, v_a_1817_);
lean_closure_set(v___f_1822_, 1, v_toPure_1820_);
lean_inc(v_toBind_1819_);
v___x_1823_ = lean_apply_4(v_toBind_1819_, lean_box(0), lean_box(0), v_x_1816_, v___f_1822_);
v___x_1824_ = lean_apply_4(v_toBind_1819_, lean_box(0), lean_box(0), v___x_1823_, v___f_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_m_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_00_u03b1_1831_, lean_object* v_x_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_MonadStateCacheT_instMonadControl___aux__3(v_00_u03b1_1825_, v_00_u03b2_1826_, v_m_1827_, v_inst_1828_, v_inst_1829_, v_inst_1830_, v_00_u03b1_1831_, v_x_1832_, v_a_1833_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_inc_ref(v_inst_1837_);
lean_inc_ref(v_inst_1836_);
lean_inc_ref(v_inst_1835_);
v___x_1838_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1838_, 0, lean_box(0));
lean_closure_set(v___x_1838_, 1, lean_box(0));
lean_closure_set(v___x_1838_, 2, lean_box(0));
lean_closure_set(v___x_1838_, 3, v_inst_1835_);
lean_closure_set(v___x_1838_, 4, v_inst_1836_);
lean_closure_set(v___x_1838_, 5, v_inst_1837_);
v___x_1839_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed), 9, 6);
lean_closure_set(v___x_1839_, 0, lean_box(0));
lean_closure_set(v___x_1839_, 1, lean_box(0));
lean_closure_set(v___x_1839_, 2, lean_box(0));
lean_closure_set(v___x_1839_, 3, v_inst_1835_);
lean_closure_set(v___x_1839_, 4, v_inst_1836_);
lean_closure_set(v___x_1839_, 5, v_inst_1837_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_m_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_1844_, v_inst_1845_, v_inst_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object* v_h_1848_, lean_object* v_s_1849_, lean_object* v_x_1850_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_apply_2(v_h_1848_, v___x_1851_, v_s_1849_);
return v___x_1852_;
}
else
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_s_1849_);
v_val_1853_ = lean_ctor_get(v_x_1850_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1855_ = v_x_1850_;
v_isShared_1856_ = v_isSharedCheck_1863_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v_x_1850_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1863_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; 
v_fst_1857_ = lean_ctor_get(v_val_1853_, 0);
lean_inc(v_fst_1857_);
v_snd_1858_ = lean_ctor_get(v_val_1853_, 1);
lean_inc(v_snd_1858_);
lean_dec(v_val_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_fst_1857_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_fst_1857_);
v___x_1860_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_apply_2(v_h_1848_, v___x_1860_, v_snd_1858_);
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(lean_object* v_toPure_1864_, lean_object* v_____x_1865_){
_start:
{
lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v_fst_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1885_; 
v_fst_1866_ = lean_ctor_get(v_____x_1865_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v_____x_1865_, 1);
lean_inc(v_snd_1867_);
lean_dec_ref(v_____x_1865_);
v_fst_1868_ = lean_ctor_get(v_fst_1866_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_fst_1866_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_fst_1866_, 1);
lean_dec(v_unused_1886_);
v___x_1870_ = v_fst_1866_;
v_isShared_1871_ = v_isSharedCheck_1885_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_fst_1868_);
lean_dec(v_fst_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1885_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1884_; 
v_fst_1872_ = lean_ctor_get(v_snd_1867_, 0);
v_snd_1873_ = lean_ctor_get(v_snd_1867_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_snd_1867_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1875_ = v_snd_1867_;
v_isShared_1876_ = v_isSharedCheck_1884_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_inc(v_fst_1872_);
lean_dec(v_snd_1867_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1884_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v_fst_1872_);
lean_ctor_set(v___x_1875_, 0, v_fst_1868_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fst_1868_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_fst_1872_);
v___x_1878_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v_snd_1873_);
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_snd_1873_);
v___x_1880_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_apply_2(v_toPure_1864_, lean_box(0), v___x_1880_);
return v___x_1881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_x_1889_, lean_object* v_h_1890_, lean_object* v_s_1891_){
_start:
{
lean_object* v_toApplicative_1892_; lean_object* v_toBind_1893_; lean_object* v_toPure_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_toApplicative_1892_ = lean_ctor_get(v_inst_1887_, 0);
lean_inc_ref(v_toApplicative_1892_);
v_toBind_1893_ = lean_ctor_get(v_inst_1887_, 1);
lean_inc(v_toBind_1893_);
lean_dec_ref(v_inst_1887_);
v_toPure_1894_ = lean_ctor_get(v_toApplicative_1892_, 1);
lean_inc(v_toPure_1894_);
lean_dec_ref(v_toApplicative_1892_);
lean_inc_ref(v_s_1891_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1895_, 0, v_h_1890_);
lean_closure_set(v___f_1895_, 1, v_s_1891_);
v___x_1896_ = lean_apply_1(v_x_1889_, v_s_1891_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1897_, 0, v_toPure_1894_);
v___x_1898_ = lean_apply_4(v_inst_1888_, lean_box(0), lean_box(0), v___x_1896_, v___f_1895_);
v___x_1899_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v___x_1898_, v___f_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1(lean_object* v_00_u03b1_1900_, lean_object* v_00_u03b2_1901_, lean_object* v_m_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_00_u03b1_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_h_1910_, lean_object* v_s_1911_){
_start:
{
lean_object* v_toApplicative_1912_; lean_object* v_toBind_1913_; lean_object* v_toPure_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_toApplicative_1912_ = lean_ctor_get(v_inst_1905_, 0);
lean_inc_ref(v_toApplicative_1912_);
v_toBind_1913_ = lean_ctor_get(v_inst_1905_, 1);
lean_inc(v_toBind_1913_);
lean_dec_ref(v_inst_1905_);
v_toPure_1914_ = lean_ctor_get(v_toApplicative_1912_, 1);
lean_inc(v_toPure_1914_);
lean_dec_ref(v_toApplicative_1912_);
lean_inc_ref(v_s_1911_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1915_, 0, v_h_1910_);
lean_closure_set(v___f_1915_, 1, v_s_1911_);
v___x_1916_ = lean_apply_1(v_x_1909_, v_s_1911_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1917_, 0, v_toPure_1914_);
v___x_1918_ = lean_apply_4(v_inst_1906_, lean_box(0), lean_box(0), v___x_1916_, v___f_1915_);
v___x_1919_ = lean_apply_4(v_toBind_1913_, lean_box(0), lean_box(0), v___x_1918_, v___f_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(lean_object* v_00_u03b1_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_m_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_00_u03b1_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_x_1929_, lean_object* v_h_1930_, lean_object* v_s_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_MonadStateCacheT_instMonadFinally___aux__1(v_00_u03b1_1920_, v_00_u03b2_1921_, v_m_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_inst_1926_, v_00_u03b1_1927_, v_00_u03b2_1928_, v_x_1929_, v_h_1930_, v_s_1931_);
lean_dec_ref(v_inst_1924_);
lean_dec_ref(v_inst_1923_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_1937_, 0, lean_box(0));
lean_closure_set(v___x_1937_, 1, lean_box(0));
lean_closure_set(v___x_1937_, 2, lean_box(0));
lean_closure_set(v___x_1937_, 3, v_inst_1933_);
lean_closure_set(v___x_1937_, 4, v_inst_1934_);
lean_closure_set(v___x_1937_, 5, v_inst_1935_);
lean_closure_set(v___x_1937_, 6, v_inst_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object* v_00_u03b1_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_m_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_1945_, 0, lean_box(0));
lean_closure_set(v___x_1945_, 1, lean_box(0));
lean_closure_set(v___x_1945_, 2, lean_box(0));
lean_closure_set(v___x_1945_, 3, v_inst_1941_);
lean_closure_set(v___x_1945_, 4, v_inst_1942_);
lean_closure_set(v___x_1945_, 5, v_inst_1943_);
lean_closure_set(v___x_1945_, 6, v_inst_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(lean_object* v_a_1946_, lean_object* v_toPure_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_a_1948_);
lean_ctor_set(v___x_1949_, 1, v_a_1946_);
v___x_1950_ = lean_apply_2(v_toPure_1947_, lean_box(0), v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_toApplicative_1954_; lean_object* v_getRef_1955_; lean_object* v_toBind_1956_; lean_object* v_toPure_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_toApplicative_1954_ = lean_ctor_get(v_inst_1951_, 0);
lean_inc_ref(v_toApplicative_1954_);
v_getRef_1955_ = lean_ctor_get(v_inst_1952_, 0);
lean_inc(v_getRef_1955_);
lean_dec_ref(v_inst_1952_);
v_toBind_1956_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_toBind_1956_);
lean_dec_ref(v_inst_1951_);
v_toPure_1957_ = lean_ctor_get(v_toApplicative_1954_, 1);
lean_inc(v_toPure_1957_);
lean_dec_ref(v_toApplicative_1954_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1958_, 0, v_a_1953_);
lean_closure_set(v___f_1958_, 1, v_toPure_1957_);
v___x_1959_ = lean_apply_4(v_toBind_1956_, lean_box(0), lean_box(0), v_getRef_1955_, v___f_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1(lean_object* v_00_u03b1_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_m_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_toApplicative_1968_; lean_object* v_getRef_1969_; lean_object* v_toBind_1970_; lean_object* v_toPure_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; 
v_toApplicative_1968_ = lean_ctor_get(v_inst_1965_, 0);
lean_inc_ref(v_toApplicative_1968_);
v_getRef_1969_ = lean_ctor_get(v_inst_1966_, 0);
lean_inc(v_getRef_1969_);
lean_dec_ref(v_inst_1966_);
v_toBind_1970_ = lean_ctor_get(v_inst_1965_, 1);
lean_inc(v_toBind_1970_);
lean_dec_ref(v_inst_1965_);
v_toPure_1971_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_inc(v_toPure_1971_);
lean_dec_ref(v_toApplicative_1968_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1972_, 0, v_a_1967_);
lean_closure_set(v___f_1972_, 1, v_toPure_1971_);
v___x_1973_ = lean_apply_4(v_toBind_1970_, lean_box(0), lean_box(0), v_getRef_1969_, v___f_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_m_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_MonadStateCacheT_instMonadRef___aux__1(v_00_u03b1_1974_, v_00_u03b2_1975_, v_m_1976_, v_inst_1977_, v_inst_1978_, v_inst_1979_, v_inst_1980_, v_a_1981_);
lean_dec_ref(v_inst_1978_);
lean_dec_ref(v_inst_1977_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(lean_object* v_inst_1983_, lean_object* v_ref_1984_, lean_object* v_x_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_withRef_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_withRef_1987_ = lean_ctor_get(v_inst_1983_, 1);
lean_inc(v_withRef_1987_);
lean_dec_ref(v_inst_1983_);
v___x_1988_ = lean_apply_1(v_x_1985_, v_a_1986_);
v___x_1989_ = lean_apply_3(v_withRef_1987_, lean_box(0), v_ref_1984_, v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3(lean_object* v_00_u03b1_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_m_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_00_u03b1_1996_, lean_object* v_ref_1997_, lean_object* v_x_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_withRef_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_withRef_2000_ = lean_ctor_get(v_inst_1995_, 1);
lean_inc(v_withRef_2000_);
lean_dec_ref(v_inst_1995_);
v___x_2001_ = lean_apply_1(v_x_1998_, v_a_1999_);
v___x_2002_ = lean_apply_3(v_withRef_2000_, lean_box(0), v_ref_1997_, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_m_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_00_u03b1_2009_, lean_object* v_ref_2010_, lean_object* v_x_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_MonadStateCacheT_instMonadRef___aux__3(v_00_u03b1_2003_, v_00_u03b2_2004_, v_m_2005_, v_inst_2006_, v_inst_2007_, v_inst_2008_, v_00_u03b1_2009_, v_ref_2010_, v_x_2011_, v_a_2012_);
lean_dec_ref(v_inst_2007_);
lean_dec_ref(v_inst_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_inc_ref(v_inst_2017_);
lean_inc_ref(v_inst_2015_);
lean_inc_ref(v_inst_2014_);
v___x_2018_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed), 8, 7);
lean_closure_set(v___x_2018_, 0, lean_box(0));
lean_closure_set(v___x_2018_, 1, lean_box(0));
lean_closure_set(v___x_2018_, 2, lean_box(0));
lean_closure_set(v___x_2018_, 3, v_inst_2014_);
lean_closure_set(v___x_2018_, 4, v_inst_2015_);
lean_closure_set(v___x_2018_, 5, v_inst_2016_);
lean_closure_set(v___x_2018_, 6, v_inst_2017_);
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed), 10, 6);
lean_closure_set(v___x_2019_, 0, lean_box(0));
lean_closure_set(v___x_2019_, 1, lean_box(0));
lean_closure_set(v___x_2019_, 2, lean_box(0));
lean_closure_set(v___x_2019_, 3, v_inst_2014_);
lean_closure_set(v___x_2019_, 4, v_inst_2015_);
lean_closure_set(v___x_2019_, 5, v_inst_2017_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2018_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object* v_00_u03b1_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_m_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(v_inst_2024_, v_inst_2025_, v_inst_2026_, v_inst_2027_);
return v___x_2028_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
