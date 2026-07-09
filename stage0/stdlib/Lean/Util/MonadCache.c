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
lean_inc_n(v_toBind_280_, 3);
lean_dec_ref(v_inst_277_);
v_toPure_281_ = lean_ctor_get(v_toApplicative_279_, 1);
lean_inc_n(v_toPure_281_, 2);
lean_dec_ref(v_toApplicative_279_);
v___x_282_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_276_);
v___x_283_ = lean_apply_2(v_inst_276_, lean_box(0), v___x_282_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_284_, 0, v_toPure_281_);
lean_closure_set(v___f_284_, 1, v_inst_276_);
lean_closure_set(v___f_284_, 2, v_toBind_280_);
lean_closure_set(v___f_284_, 3, v_x_278_);
v___f_285_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_285_, 0, v_toPure_281_);
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
lean_inc_n(v_toBind_300_, 3);
lean_dec_ref(v_inst_296_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_299_, 1);
lean_inc_n(v_toPure_301_, 2);
lean_dec_ref(v_toApplicative_299_);
v___x_302_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_295_);
v___x_303_ = lean_apply_2(v_inst_295_, lean_box(0), v___x_302_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_304_, 0, v_toPure_301_);
lean_closure_set(v___f_304_, 1, v_inst_295_);
lean_closure_set(v___f_304_, 2, v_toBind_300_);
lean_closure_set(v___f_304_, 3, v_x_298_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_305_, 0, v_toPure_301_);
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
lean_inc_n(v_a_455_, 2);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_458_, 0, v_a_454_);
lean_closure_set(v___f_458_, 1, v_a_455_);
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
lean_inc_n(v_a_478_, 2);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_481_, 0, v_a_477_);
lean_closure_set(v___f_481_, 1, v_a_478_);
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
lean_inc_n(v_a_501_, 2);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_504_, 0, v_a_500_);
lean_closure_set(v___f_504_, 1, v_a_501_);
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
lean_inc_n(v_a_524_, 2);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_527_, 0, v_a_523_);
lean_closure_set(v___f_527_, 1, v_a_524_);
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
lean_inc_n(v_a_547_, 2);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_550_, 0, v_a_546_);
lean_closure_set(v___f_550_, 1, v_a_547_);
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
lean_inc_n(v_a_570_, 2);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_573_, 0, v_a_569_);
lean_closure_set(v___f_573_, 1, v_a_570_);
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
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_f_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_593_; 
lean_inc(v_a_591_);
v___x_593_ = lean_apply_2(v_f_590_, v_a_592_, v_a_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(lean_object* v_f_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_f_594_, v_a_595_, v_a_596_);
lean_dec(v_a_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg(lean_object* v_inst_598_, lean_object* v_x_599_, lean_object* v_f_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_toBind_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_toBind_602_ = lean_ctor_get(v_inst_598_, 1);
lean_inc(v_toBind_602_);
lean_dec_ref(v_inst_598_);
lean_inc_n(v_a_601_, 2);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_603_, 0, v_f_600_);
lean_closure_set(v___f_603_, 1, v_a_601_);
v___x_604_ = lean_apply_1(v_x_599_, v_a_601_);
v___x_605_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_604_, v___f_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(lean_object* v_inst_606_, lean_object* v_x_607_, lean_object* v_f_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(v_inst_606_, v_x_607_, v_f_608_, v_a_609_);
lean_dec(v_a_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13(lean_object* v_00_u03c9_611_, lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_m_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_f_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_toBind_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_toBind_624_ = lean_ctor_get(v_inst_618_, 1);
lean_inc(v_toBind_624_);
lean_dec_ref(v_inst_618_);
lean_inc_n(v_a_623_, 2);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_625_, 0, v_f_622_);
lean_closure_set(v___f_625_, 1, v_a_623_);
v___x_626_ = lean_apply_1(v_x_621_, v_a_623_);
v___x_627_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_626_, v___f_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03c9_628_, lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_m_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_f_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_MonadCacheT_instMonad___aux__13(v_00_u03c9_628_, v_00_u03b1_629_, v_00_u03b2_630_, v_m_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_inst_635_, v_00_u03b1_636_, v_00_u03b2_637_, v_x_638_, v_f_639_, v_a_640_);
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
lean_inc_ref_n(v_inst_645_, 6);
lean_inc_ref_n(v_inst_644_, 6);
lean_inc_ref_n(v_inst_643_, 6);
v___x_646_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__1___boxed), 13, 8);
lean_closure_set(v___x_646_, 0, lean_box(0));
lean_closure_set(v___x_646_, 1, lean_box(0));
lean_closure_set(v___x_646_, 2, lean_box(0));
lean_closure_set(v___x_646_, 3, lean_box(0));
lean_closure_set(v___x_646_, 4, v_inst_642_);
lean_closure_set(v___x_646_, 5, v_inst_643_);
lean_closure_set(v___x_646_, 6, v_inst_644_);
lean_closure_set(v___x_646_, 7, v_inst_645_);
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
v___x_649_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__5___boxed), 11, 8);
lean_closure_set(v___x_649_, 0, lean_box(0));
lean_closure_set(v___x_649_, 1, lean_box(0));
lean_closure_set(v___x_649_, 2, lean_box(0));
lean_closure_set(v___x_649_, 3, lean_box(0));
lean_closure_set(v___x_649_, 4, v_inst_642_);
lean_closure_set(v___x_649_, 5, v_inst_643_);
lean_closure_set(v___x_649_, 6, v_inst_644_);
lean_closure_set(v___x_649_, 7, v_inst_645_);
v___x_650_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__7___boxed), 13, 8);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, lean_box(0));
lean_closure_set(v___x_650_, 3, lean_box(0));
lean_closure_set(v___x_650_, 4, v_inst_642_);
lean_closure_set(v___x_650_, 5, v_inst_643_);
lean_closure_set(v___x_650_, 6, v_inst_644_);
lean_closure_set(v___x_650_, 7, v_inst_645_);
v___x_651_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__9___boxed), 13, 8);
lean_closure_set(v___x_651_, 0, lean_box(0));
lean_closure_set(v___x_651_, 1, lean_box(0));
lean_closure_set(v___x_651_, 2, lean_box(0));
lean_closure_set(v___x_651_, 3, lean_box(0));
lean_closure_set(v___x_651_, 4, v_inst_642_);
lean_closure_set(v___x_651_, 5, v_inst_643_);
lean_closure_set(v___x_651_, 6, v_inst_644_);
lean_closure_set(v___x_651_, 7, v_inst_645_);
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
lean_inc_n(v_s_743_, 2);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_745_, 0, v_c_742_);
lean_closure_set(v___f_745_, 1, v_s_743_);
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
lean_inc_n(v_s_765_, 2);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_767_, 0, v_c_764_);
lean_closure_set(v___f_767_, 1, v_s_765_);
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
lean_inc_n(v_a_888_, 2);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_889_, 0, v_f_887_);
lean_closure_set(v___f_889_, 1, v_a_888_);
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
lean_inc_n(v_a_909_, 2);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_910_, 0, v_f_908_);
lean_closure_set(v___f_910_, 1, v_a_909_);
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
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0(lean_object* v_x_u2082_1047_, lean_object* v_a_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
lean_inc(v_a_1048_);
v___x_1051_ = lean_apply_2(v_x_u2082_1047_, v___x_1050_, v_a_1048_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed(lean_object* v_x_u2082_1052_, lean_object* v_a_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0(v_x_u2082_1052_, v_a_1053_, v_x_1054_);
lean_dec(v_a_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg(lean_object* v_inst_1056_, lean_object* v_x_u2081_1057_, lean_object* v_x_u2082_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_orElse_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_orElse_1060_ = lean_ctor_get(v_inst_1056_, 2);
lean_inc(v_orElse_1060_);
lean_dec_ref(v_inst_1056_);
lean_inc_n(v_a_1059_, 2);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1061_, 0, v_x_u2082_1058_);
lean_closure_set(v___f_1061_, 1, v_a_1059_);
v___x_1062_ = lean_apply_1(v_x_u2081_1057_, v_a_1059_);
v___x_1063_ = lean_apply_3(v_orElse_1060_, lean_box(0), v___x_1062_, v___f_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(lean_object* v_inst_1064_, lean_object* v_x_u2081_1065_, lean_object* v_x_u2082_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(v_inst_1064_, v_x_u2081_1065_, v_x_u2082_1066_, v_a_1067_);
lean_dec(v_a_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3(lean_object* v_00_u03c9_1069_, lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_m_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_00_u03b1_1077_, lean_object* v_x_u2081_1078_, lean_object* v_x_u2082_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_orElse_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_orElse_1081_ = lean_ctor_get(v_inst_1076_, 2);
lean_inc(v_orElse_1081_);
lean_dec_ref(v_inst_1076_);
lean_inc_n(v_a_1080_, 2);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1082_, 0, v_x_u2082_1079_);
lean_closure_set(v___f_1082_, 1, v_a_1080_);
v___x_1083_ = lean_apply_1(v_x_u2081_1078_, v_a_1080_);
v___x_1084_ = lean_apply_3(v_orElse_1081_, lean_box(0), v___x_1083_, v___f_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___aux__3___boxed(lean_object* v_00_u03c9_1085_, lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_00_u03b1_1093_, lean_object* v_x_u2081_1094_, lean_object* v_x_u2082_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_MonadCacheT_instAlternative___aux__3(v_00_u03c9_1085_, v_00_u03b1_1086_, v_00_u03b2_1087_, v_m_1088_, v_inst_1089_, v_inst_1090_, v_inst_1091_, v_inst_1092_, v_00_u03b1_1093_, v_x_u2081_1094_, v_x_u2082_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_inst_1091_);
lean_dec_ref(v_inst_1090_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v_toApplicative_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc_ref_n(v_inst_1100_, 2);
lean_inc_ref_n(v_inst_1099_, 2);
v___x_1103_ = l_Lean_MonadCacheT_instMonad___redArg(v_inst_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_);
v_toApplicative_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc_ref(v_toApplicative_1104_);
lean_dec_ref(v___x_1103_);
lean_inc_ref(v_inst_1102_);
v___x_1105_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__1___boxed), 10, 8);
lean_closure_set(v___x_1105_, 0, lean_box(0));
lean_closure_set(v___x_1105_, 1, lean_box(0));
lean_closure_set(v___x_1105_, 2, lean_box(0));
lean_closure_set(v___x_1105_, 3, lean_box(0));
lean_closure_set(v___x_1105_, 4, v_inst_1098_);
lean_closure_set(v___x_1105_, 5, v_inst_1099_);
lean_closure_set(v___x_1105_, 6, v_inst_1100_);
lean_closure_set(v___x_1105_, 7, v_inst_1102_);
v___x_1106_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instAlternative___aux__3___boxed), 12, 8);
lean_closure_set(v___x_1106_, 0, lean_box(0));
lean_closure_set(v___x_1106_, 1, lean_box(0));
lean_closure_set(v___x_1106_, 2, lean_box(0));
lean_closure_set(v___x_1106_, 3, lean_box(0));
lean_closure_set(v___x_1106_, 4, v_inst_1098_);
lean_closure_set(v___x_1106_, 5, v_inst_1099_);
lean_closure_set(v___x_1106_, 6, v_inst_1100_);
lean_closure_set(v___x_1106_, 7, v_inst_1102_);
v___x_1107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1107_, 0, v_toApplicative_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object* v_00_u03c9_1108_, lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_m_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_MonadCacheT_instAlternative___redArg(v_inst_1112_, v_inst_1113_, v_inst_1114_, v_inst_1115_, v_inst_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_inst_1118_, lean_object* v_f_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_toApplicative_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1132_; 
v_toApplicative_1121_ = lean_ctor_get(v_inst_1118_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_inst_1118_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_inst_1118_, 1);
lean_dec(v_unused_1133_);
v___x_1123_ = v_inst_1118_;
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_toApplicative_1121_);
lean_dec(v_inst_1118_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_toPure_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v_toPure_1125_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_inc(v_toPure_1125_);
lean_dec_ref(v_toApplicative_1121_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_apply_1(v_f_1119_, v___y_1120_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1127_);
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1129_ = v___x_1123_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_apply_2(v_toPure_1125_, lean_box(0), v___x_1129_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_1134_){
_start:
{
lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc_ref(v_inst_1134_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1135_, 0, v_inst_1134_);
v___x_1136_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_1136_, 0, lean_box(0));
lean_closure_set(v___x_1136_, 1, lean_box(0));
lean_closure_set(v___x_1136_, 2, v_inst_1134_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___f_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_m_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_m_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(v_00_u03b1_1145_, v_00_u03b2_1146_, v_m_1147_, v_inst_1148_, v_inst_1149_, v_inst_1150_);
lean_dec_ref(v_inst_1149_);
lean_dec_ref(v_inst_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0(lean_object* v_x_1152_){
_start:
{
lean_object* v_fst_1153_; 
v_fst_1153_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_fst_1153_);
return v_fst_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(lean_object* v_x_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_1154_);
lean_dec_ref(v_x_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg(lean_object* v_inst_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_toApplicative_1159_; lean_object* v_toFunctor_1160_; lean_object* v_map_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_toApplicative_1159_ = lean_ctor_get(v_inst_1157_, 0);
lean_inc_ref(v_toApplicative_1159_);
lean_dec_ref(v_inst_1157_);
v_toFunctor_1160_ = lean_ctor_get(v_toApplicative_1159_, 0);
lean_inc_ref(v_toFunctor_1160_);
lean_dec_ref(v_toApplicative_1159_);
v_map_1161_ = lean_ctor_get(v_toFunctor_1160_, 0);
lean_inc(v_map_1161_);
lean_dec_ref(v_toFunctor_1160_);
v___f_1162_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1163_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_1164_ = lean_apply_1(v_x_1158_, v___x_1163_);
v___x_1165_ = lean_apply_4(v_map_1161_, lean_box(0), lean_box(0), v___f_1162_, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_m_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_00_u03c3_1172_, lean_object* v_x_1173_){
_start:
{
lean_object* v_toApplicative_1174_; lean_object* v_toFunctor_1175_; lean_object* v_map_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_toApplicative_1174_ = lean_ctor_get(v_inst_1171_, 0);
lean_inc_ref(v_toApplicative_1174_);
lean_dec_ref(v_inst_1171_);
v_toFunctor_1175_ = lean_ctor_get(v_toApplicative_1174_, 0);
lean_inc_ref(v_toFunctor_1175_);
lean_dec_ref(v_toApplicative_1174_);
v_map_1176_ = lean_ctor_get(v_toFunctor_1175_, 0);
lean_inc(v_map_1176_);
lean_dec_ref(v_toFunctor_1175_);
v___f_1177_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_1178_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_1179_ = lean_apply_1(v_x_1173_, v___x_1178_);
v___x_1180_ = lean_apply_4(v_map_1176_, lean_box(0), lean_box(0), v___f_1177_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_00_u03c3_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_MonadStateCacheT_run(v_00_u03b1_1181_, v_00_u03b2_1182_, v_m_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_, v_00_u03c3_1187_, v_x_1188_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(lean_object* v_f_1190_, lean_object* v_toPure_1191_, lean_object* v_____x_1192_){
_start:
{
lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1203_; 
v_fst_1193_ = lean_ctor_get(v_____x_1192_, 0);
v_snd_1194_ = lean_ctor_get(v_____x_1192_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_____x_1192_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1196_ = v_____x_1192_;
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
lean_dec(v_____x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_apply_1(v_f_1190_, v_fst_1193_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_snd_1194_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_apply_2(v_toPure_1191_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(lean_object* v_inst_1204_, lean_object* v_f_1205_, lean_object* v_x_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_toApplicative_1208_; lean_object* v_toBind_1209_; lean_object* v_toPure_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; 
v_toApplicative_1208_ = lean_ctor_get(v_inst_1204_, 0);
lean_inc_ref(v_toApplicative_1208_);
v_toBind_1209_ = lean_ctor_get(v_inst_1204_, 1);
lean_inc(v_toBind_1209_);
lean_dec_ref(v_inst_1204_);
v_toPure_1210_ = lean_ctor_get(v_toApplicative_1208_, 1);
lean_inc(v_toPure_1210_);
lean_dec_ref(v_toApplicative_1208_);
v___x_1211_ = lean_apply_1(v_x_1206_, v_a_1207_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1212_, 0, v_f_1205_);
lean_closure_set(v___f_1212_, 1, v_toPure_1210_);
v___x_1213_ = lean_apply_4(v_toBind_1209_, lean_box(0), lean_box(0), v___x_1211_, v___f_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_m_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_f_1222_, lean_object* v_x_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_toApplicative_1225_; lean_object* v_toBind_1226_; lean_object* v_toPure_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v_toApplicative_1225_ = lean_ctor_get(v_inst_1219_, 0);
lean_inc_ref(v_toApplicative_1225_);
v_toBind_1226_ = lean_ctor_get(v_inst_1219_, 1);
lean_inc(v_toBind_1226_);
lean_dec_ref(v_inst_1219_);
v_toPure_1227_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_inc(v_toPure_1227_);
lean_dec_ref(v_toApplicative_1225_);
v___x_1228_ = lean_apply_1(v_x_1223_, v_a_1224_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1229_, 0, v_f_1222_);
lean_closure_set(v___f_1229_, 1, v_toPure_1227_);
v___x_1230_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1228_, v___f_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_00_u03b1_1237_, lean_object* v_00_u03b2_1238_, lean_object* v_f_1239_, lean_object* v_x_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_MonadStateCacheT_instMonad___aux__1(v_00_u03b1_1231_, v_00_u03b2_1232_, v_m_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_00_u03b1_1237_, v_00_u03b2_1238_, v_f_1239_, v_x_1240_, v_a_1241_);
lean_dec_ref(v_inst_1235_);
lean_dec_ref(v_inst_1234_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(lean_object* v_a_1243_, lean_object* v_toPure_1244_, lean_object* v_____x_1245_){
_start:
{
lean_object* v_snd_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1254_; 
v_snd_1246_ = lean_ctor_get(v_____x_1245_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_____x_1245_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_____x_1245_, 0);
lean_dec(v_unused_1255_);
v___x_1248_ = v_____x_1245_;
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_snd_1246_);
lean_dec(v_____x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_a_1243_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_snd_1246_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_apply_2(v_toPure_1244_, lean_box(0), v___x_1251_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(lean_object* v_inst_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
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
v___x_1263_ = lean_apply_1(v_a_1258_, v_a_1259_);
v___f_1264_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1264_, 0, v_a_1257_);
lean_closure_set(v___f_1264_, 1, v_toPure_1262_);
v___x_1265_ = lean_apply_4(v_toBind_1261_, lean_box(0), lean_box(0), v___x_1263_, v___f_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3(lean_object* v_00_u03b1_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_m_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_00_u03b1_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_toApplicative_1277_; lean_object* v_toBind_1278_; lean_object* v_toPure_1279_; lean_object* v___x_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; 
v_toApplicative_1277_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_ref(v_toApplicative_1277_);
v_toBind_1278_ = lean_ctor_get(v_inst_1271_, 1);
lean_inc(v_toBind_1278_);
lean_dec_ref(v_inst_1271_);
v_toPure_1279_ = lean_ctor_get(v_toApplicative_1277_, 1);
lean_inc(v_toPure_1279_);
lean_dec_ref(v_toApplicative_1277_);
v___x_1280_ = lean_apply_1(v_a_1275_, v_a_1276_);
v___f_1281_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1281_, 0, v_a_1274_);
lean_closure_set(v___f_1281_, 1, v_toPure_1279_);
v___x_1282_ = lean_apply_4(v_toBind_1278_, lean_box(0), lean_box(0), v___x_1280_, v___f_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_m_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_MonadStateCacheT_instMonad___aux__3(v_00_u03b1_1283_, v_00_u03b2_1284_, v_m_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_00_u03b1_1289_, v_00_u03b2_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec_ref(v_inst_1287_);
lean_dec_ref(v_inst_1286_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(lean_object* v_inst_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_toApplicative_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
v_toApplicative_1298_ = lean_ctor_get(v_inst_1295_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_inst_1295_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v_inst_1295_, 1);
lean_dec(v_unused_1308_);
v___x_1300_ = v_inst_1295_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_toApplicative_1298_);
lean_dec(v_inst_1295_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_toPure_1302_; lean_object* v___x_1304_; 
v_toPure_1302_ = lean_ctor_get(v_toApplicative_1298_, 1);
lean_inc(v_toPure_1302_);
lean_dec_ref(v_toApplicative_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v_a_1297_);
lean_ctor_set(v___x_1300_, 0, v_a_1296_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1296_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_a_1297_);
v___x_1304_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1304_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_m_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_00_u03b1_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_toApplicative_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1327_; 
v_toApplicative_1318_ = lean_ctor_get(v_inst_1314_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_inst_1314_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_inst_1314_, 1);
lean_dec(v_unused_1328_);
v___x_1320_ = v_inst_1314_;
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_toApplicative_1318_);
lean_dec(v_inst_1314_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_toPure_1322_; lean_object* v___x_1324_; 
v_toPure_1322_ = lean_ctor_get(v_toApplicative_1318_, 1);
lean_inc(v_toPure_1322_);
lean_dec_ref(v_toApplicative_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v_a_1317_);
lean_ctor_set(v___x_1320_, 0, v_a_1316_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1316_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_a_1317_);
v___x_1324_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_apply_2(v_toPure_1322_, lean_box(0), v___x_1324_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_m_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_00_u03b1_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_MonadStateCacheT_instMonad___aux__5(v_00_u03b1_1329_, v_00_u03b2_1330_, v_m_1331_, v_inst_1332_, v_inst_1333_, v_inst_1334_, v_00_u03b1_1335_, v_a_1336_, v_a_1337_);
lean_dec_ref(v_inst_1333_);
lean_dec_ref(v_inst_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(lean_object* v_fst_1339_, lean_object* v_toPure_1340_, lean_object* v_____x_1341_){
_start:
{
lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1352_; 
v_fst_1342_ = lean_ctor_get(v_____x_1341_, 0);
v_snd_1343_ = lean_ctor_get(v_____x_1341_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_____x_1341_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1345_ = v_____x_1341_;
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_inc(v_fst_1342_);
lean_dec(v_____x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_apply_1(v_fst_1339_, v_fst_1342_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_snd_1343_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_apply_2(v_toPure_1340_, lean_box(0), v___x_1349_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(lean_object* v_toApplicative_1353_, lean_object* v_x_1354_, lean_object* v_toBind_1355_, lean_object* v_____x_1356_){
_start:
{
lean_object* v_fst_1357_; lean_object* v_snd_1358_; lean_object* v_toPure_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; 
v_fst_1357_ = lean_ctor_get(v_____x_1356_, 0);
lean_inc(v_fst_1357_);
v_snd_1358_ = lean_ctor_get(v_____x_1356_, 1);
lean_inc(v_snd_1358_);
lean_dec_ref(v_____x_1356_);
v_toPure_1359_ = lean_ctor_get(v_toApplicative_1353_, 1);
lean_inc(v_toPure_1359_);
lean_dec_ref(v_toApplicative_1353_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_apply_2(v_x_1354_, v___x_1360_, v_snd_1358_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1362_, 0, v_fst_1357_);
lean_closure_set(v___f_1362_, 1, v_toPure_1359_);
v___x_1363_ = lean_apply_4(v_toBind_1355_, lean_box(0), lean_box(0), v___x_1361_, v___f_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(lean_object* v_inst_1364_, lean_object* v_f_1365_, lean_object* v_x_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_toApplicative_1368_; lean_object* v_toBind_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_toApplicative_1368_ = lean_ctor_get(v_inst_1364_, 0);
lean_inc_ref(v_toApplicative_1368_);
v_toBind_1369_ = lean_ctor_get(v_inst_1364_, 1);
lean_inc_n(v_toBind_1369_, 2);
lean_dec_ref(v_inst_1364_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1370_, 0, v_toApplicative_1368_);
lean_closure_set(v___f_1370_, 1, v_x_1366_);
lean_closure_set(v___f_1370_, 2, v_toBind_1369_);
v___x_1371_ = lean_apply_1(v_f_1365_, v_a_1367_);
v___x_1372_ = lean_apply_4(v_toBind_1369_, lean_box(0), lean_box(0), v___x_1371_, v___f_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_m_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_f_1381_, lean_object* v_x_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_toApplicative_1384_; lean_object* v_toBind_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_toApplicative_1384_ = lean_ctor_get(v_inst_1378_, 0);
lean_inc_ref(v_toApplicative_1384_);
v_toBind_1385_ = lean_ctor_get(v_inst_1378_, 1);
lean_inc_n(v_toBind_1385_, 2);
lean_dec_ref(v_inst_1378_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1386_, 0, v_toApplicative_1384_);
lean_closure_set(v___f_1386_, 1, v_x_1382_);
lean_closure_set(v___f_1386_, 2, v_toBind_1385_);
v___x_1387_ = lean_apply_1(v_f_1381_, v_a_1383_);
v___x_1388_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v___x_1387_, v___f_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_00_u03b2_1390_, lean_object* v_m_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_f_1397_, lean_object* v_x_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_MonadStateCacheT_instMonad___aux__7(v_00_u03b1_1389_, v_00_u03b2_1390_, v_m_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_00_u03b1_1395_, v_00_u03b2_1396_, v_f_1397_, v_x_1398_, v_a_1399_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(lean_object* v_toApplicative_1401_, lean_object* v_fst_1402_, lean_object* v_____x_1403_){
_start:
{
lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v_snd_1404_ = lean_ctor_get(v_____x_1403_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_____x_1403_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_____x_1403_, 0);
lean_dec(v_unused_1414_);
v___x_1406_ = v_____x_1403_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_dec(v_____x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_toPure_1408_; lean_object* v___x_1410_; 
v_toPure_1408_ = lean_ctor_get(v_toApplicative_1401_, 1);
lean_inc(v_toPure_1408_);
lean_dec_ref(v_toApplicative_1401_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_fst_1402_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_fst_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_snd_1404_);
v___x_1410_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_apply_2(v_toPure_1408_, lean_box(0), v___x_1410_);
return v___x_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(lean_object* v_toApplicative_1415_, lean_object* v_y_1416_, lean_object* v_toBind_1417_, lean_object* v_____x_1418_){
_start:
{
lean_object* v_fst_1419_; lean_object* v_snd_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_fst_1419_ = lean_ctor_get(v_____x_1418_, 0);
lean_inc(v_fst_1419_);
v_snd_1420_ = lean_ctor_get(v_____x_1418_, 1);
lean_inc(v_snd_1420_);
lean_dec_ref(v_____x_1418_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1421_, 0, v_toApplicative_1415_);
lean_closure_set(v___f_1421_, 1, v_fst_1419_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_apply_2(v_y_1416_, v___x_1422_, v_snd_1420_);
v___x_1424_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v___x_1423_, v___f_1421_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(lean_object* v_inst_1425_, lean_object* v_x_1426_, lean_object* v_y_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_toApplicative_1429_; lean_object* v_toBind_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_toApplicative_1429_ = lean_ctor_get(v_inst_1425_, 0);
lean_inc_ref(v_toApplicative_1429_);
v_toBind_1430_ = lean_ctor_get(v_inst_1425_, 1);
lean_inc_n(v_toBind_1430_, 2);
lean_dec_ref(v_inst_1425_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1431_, 0, v_toApplicative_1429_);
lean_closure_set(v___f_1431_, 1, v_y_1427_);
lean_closure_set(v___f_1431_, 2, v_toBind_1430_);
v___x_1432_ = lean_apply_1(v_x_1426_, v_a_1428_);
v___x_1433_ = lean_apply_4(v_toBind_1430_, lean_box(0), lean_box(0), v___x_1432_, v___f_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_y_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_toApplicative_1445_; lean_object* v_toBind_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_toApplicative_1445_ = lean_ctor_get(v_inst_1439_, 0);
lean_inc_ref(v_toApplicative_1445_);
v_toBind_1446_ = lean_ctor_get(v_inst_1439_, 1);
lean_inc_n(v_toBind_1446_, 2);
lean_dec_ref(v_inst_1439_);
v___f_1447_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1447_, 0, v_toApplicative_1445_);
lean_closure_set(v___f_1447_, 1, v_y_1443_);
lean_closure_set(v___f_1447_, 2, v_toBind_1446_);
v___x_1448_ = lean_apply_1(v_x_1442_, v_a_1444_);
v___x_1449_ = lean_apply_4(v_toBind_1446_, lean_box(0), lean_box(0), v___x_1448_, v___f_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_x_1458_, lean_object* v_y_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_MonadStateCacheT_instMonad___aux__9(v_00_u03b1_1450_, v_00_u03b2_1451_, v_m_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_00_u03b1_1456_, v_00_u03b2_1457_, v_x_1458_, v_y_1459_, v_a_1460_);
lean_dec_ref(v_inst_1454_);
lean_dec_ref(v_inst_1453_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(lean_object* v_y_1462_, lean_object* v_____x_1463_){
_start:
{
lean_object* v_snd_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_snd_1464_ = lean_ctor_get(v_____x_1463_, 1);
lean_inc(v_snd_1464_);
lean_dec_ref(v_____x_1463_);
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_apply_2(v_y_1462_, v___x_1465_, v_snd_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(lean_object* v_inst_1467_, lean_object* v_x_1468_, lean_object* v_y_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_toBind_1471_; lean_object* v___f_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_toBind_1471_ = lean_ctor_get(v_inst_1467_, 1);
lean_inc(v_toBind_1471_);
lean_dec_ref(v_inst_1467_);
v___f_1472_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1472_, 0, v_y_1469_);
v___x_1473_ = lean_apply_1(v_x_1468_, v_a_1470_);
v___x_1474_ = lean_apply_4(v_toBind_1471_, lean_box(0), lean_box(0), v___x_1473_, v___f_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11(lean_object* v_00_u03b1_1475_, lean_object* v_00_u03b2_1476_, lean_object* v_m_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_y_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_toBind_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_toBind_1486_ = lean_ctor_get(v_inst_1480_, 1);
lean_inc(v_toBind_1486_);
lean_dec_ref(v_inst_1480_);
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1487_, 0, v_y_1484_);
v___x_1488_ = lean_apply_1(v_x_1483_, v_a_1485_);
v___x_1489_ = lean_apply_4(v_toBind_1486_, lean_box(0), lean_box(0), v___x_1488_, v___f_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_x_1498_, lean_object* v_y_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_MonadStateCacheT_instMonad___aux__11(v_00_u03b1_1490_, v_00_u03b2_1491_, v_m_1492_, v_inst_1493_, v_inst_1494_, v_inst_1495_, v_00_u03b1_1496_, v_00_u03b2_1497_, v_x_1498_, v_y_1499_, v_a_1500_);
lean_dec_ref(v_inst_1494_);
lean_dec_ref(v_inst_1493_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(lean_object* v_f_1502_, lean_object* v_____x_1503_){
_start:
{
lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1506_; 
v_fst_1504_ = lean_ctor_get(v_____x_1503_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v_____x_1503_, 1);
lean_inc(v_snd_1505_);
lean_dec_ref(v_____x_1503_);
v___x_1506_ = lean_apply_2(v_f_1502_, v_fst_1504_, v_snd_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(lean_object* v_inst_1507_, lean_object* v_x_1508_, lean_object* v_f_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_toBind_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_toBind_1511_ = lean_ctor_get(v_inst_1507_, 1);
lean_inc(v_toBind_1511_);
lean_dec_ref(v_inst_1507_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1512_, 0, v_f_1509_);
v___x_1513_ = lean_apply_1(v_x_1508_, v_a_1510_);
v___x_1514_ = lean_apply_4(v_toBind_1511_, lean_box(0), lean_box(0), v___x_1513_, v___f_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_x_1523_, lean_object* v_f_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_toBind_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_toBind_1526_ = lean_ctor_get(v_inst_1520_, 1);
lean_inc(v_toBind_1526_);
lean_dec_ref(v_inst_1520_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1527_, 0, v_f_1524_);
v___x_1528_ = lean_apply_1(v_x_1523_, v_a_1525_);
v___x_1529_ = lean_apply_4(v_toBind_1526_, lean_box(0), lean_box(0), v___x_1528_, v___f_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_00_u03b2_1531_, lean_object* v_m_1532_, lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_x_1538_, lean_object* v_f_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_MonadStateCacheT_instMonad___aux__13(v_00_u03b1_1530_, v_00_u03b2_1531_, v_m_1532_, v_inst_1533_, v_inst_1534_, v_inst_1535_, v_00_u03b1_1536_, v_00_u03b2_1537_, v_x_1538_, v_f_1539_, v_a_1540_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v_inst_1533_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_inc_ref_n(v_inst_1544_, 6);
lean_inc_ref_n(v_inst_1543_, 6);
lean_inc_ref_n(v_inst_1542_, 6);
v___x_1545_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__1___boxed), 11, 6);
lean_closure_set(v___x_1545_, 0, lean_box(0));
lean_closure_set(v___x_1545_, 1, lean_box(0));
lean_closure_set(v___x_1545_, 2, lean_box(0));
lean_closure_set(v___x_1545_, 3, v_inst_1542_);
lean_closure_set(v___x_1545_, 4, v_inst_1543_);
lean_closure_set(v___x_1545_, 5, v_inst_1544_);
v___x_1546_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__3___boxed), 11, 6);
lean_closure_set(v___x_1546_, 0, lean_box(0));
lean_closure_set(v___x_1546_, 1, lean_box(0));
lean_closure_set(v___x_1546_, 2, lean_box(0));
lean_closure_set(v___x_1546_, 3, v_inst_1542_);
lean_closure_set(v___x_1546_, 4, v_inst_1543_);
lean_closure_set(v___x_1546_, 5, v_inst_1544_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__5___boxed), 9, 6);
lean_closure_set(v___x_1548_, 0, lean_box(0));
lean_closure_set(v___x_1548_, 1, lean_box(0));
lean_closure_set(v___x_1548_, 2, lean_box(0));
lean_closure_set(v___x_1548_, 3, v_inst_1542_);
lean_closure_set(v___x_1548_, 4, v_inst_1543_);
lean_closure_set(v___x_1548_, 5, v_inst_1544_);
v___x_1549_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__7___boxed), 11, 6);
lean_closure_set(v___x_1549_, 0, lean_box(0));
lean_closure_set(v___x_1549_, 1, lean_box(0));
lean_closure_set(v___x_1549_, 2, lean_box(0));
lean_closure_set(v___x_1549_, 3, v_inst_1542_);
lean_closure_set(v___x_1549_, 4, v_inst_1543_);
lean_closure_set(v___x_1549_, 5, v_inst_1544_);
v___x_1550_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__9___boxed), 11, 6);
lean_closure_set(v___x_1550_, 0, lean_box(0));
lean_closure_set(v___x_1550_, 1, lean_box(0));
lean_closure_set(v___x_1550_, 2, lean_box(0));
lean_closure_set(v___x_1550_, 3, v_inst_1542_);
lean_closure_set(v___x_1550_, 4, v_inst_1543_);
lean_closure_set(v___x_1550_, 5, v_inst_1544_);
v___x_1551_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__11___boxed), 11, 6);
lean_closure_set(v___x_1551_, 0, lean_box(0));
lean_closure_set(v___x_1551_, 1, lean_box(0));
lean_closure_set(v___x_1551_, 2, lean_box(0));
lean_closure_set(v___x_1551_, 3, v_inst_1542_);
lean_closure_set(v___x_1551_, 4, v_inst_1543_);
lean_closure_set(v___x_1551_, 5, v_inst_1544_);
v___x_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1548_);
lean_ctor_set(v___x_1552_, 2, v___x_1549_);
lean_ctor_set(v___x_1552_, 3, v___x_1550_);
lean_ctor_set(v___x_1552_, 4, v___x_1551_);
v___x_1553_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonad___aux__13___boxed), 11, 6);
lean_closure_set(v___x_1553_, 0, lean_box(0));
lean_closure_set(v___x_1553_, 1, lean_box(0));
lean_closure_set(v___x_1553_, 2, lean_box(0));
lean_closure_set(v___x_1553_, 3, v_inst_1542_);
lean_closure_set(v___x_1553_, 4, v_inst_1543_);
lean_closure_set(v___x_1553_, 5, v_inst_1544_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_1558_, v_inst_1559_, v_inst_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(lean_object* v_a_1562_, lean_object* v_toPure_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1564_);
lean_ctor_set(v___x_1565_, 1, v_a_1562_);
v___x_1566_ = lean_apply_2(v_toPure_1563_, lean_box(0), v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(lean_object* v_inst_1567_, lean_object* v_t_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_toApplicative_1570_; lean_object* v_toBind_1571_; lean_object* v_toPure_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; 
v_toApplicative_1570_ = lean_ctor_get(v_inst_1567_, 0);
lean_inc_ref(v_toApplicative_1570_);
v_toBind_1571_ = lean_ctor_get(v_inst_1567_, 1);
lean_inc(v_toBind_1571_);
lean_dec_ref(v_inst_1567_);
v_toPure_1572_ = lean_ctor_get(v_toApplicative_1570_, 1);
lean_inc(v_toPure_1572_);
lean_dec_ref(v_toApplicative_1570_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1573_, 0, v_a_1569_);
lean_closure_set(v___f_1573_, 1, v_toPure_1572_);
v___x_1574_ = lean_apply_4(v_toBind_1571_, lean_box(0), lean_box(0), v_t_1568_, v___f_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_m_1577_, lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_00_u03b1_1581_, lean_object* v_t_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_toApplicative_1584_; lean_object* v_toBind_1585_; lean_object* v_toPure_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v_toApplicative_1584_ = lean_ctor_get(v_inst_1580_, 0);
lean_inc_ref(v_toApplicative_1584_);
v_toBind_1585_ = lean_ctor_get(v_inst_1580_, 1);
lean_inc(v_toBind_1585_);
lean_dec_ref(v_inst_1580_);
v_toPure_1586_ = lean_ctor_get(v_toApplicative_1584_, 1);
lean_inc(v_toPure_1586_);
lean_dec_ref(v_toApplicative_1584_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1587_, 0, v_a_1583_);
lean_closure_set(v___f_1587_, 1, v_toPure_1586_);
v___x_1588_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v_t_1582_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(lean_object* v_00_u03b1_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_m_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_00_u03b1_1595_, lean_object* v_t_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_MonadStateCacheT_instMonadLift___aux__1(v_00_u03b1_1589_, v_00_u03b2_1590_, v_m_1591_, v_inst_1592_, v_inst_1593_, v_inst_1594_, v_00_u03b1_1595_, v_t_1596_, v_a_1597_);
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1602_, 0, lean_box(0));
lean_closure_set(v___x_1602_, 1, lean_box(0));
lean_closure_set(v___x_1602_, 2, lean_box(0));
lean_closure_set(v___x_1602_, 3, v_inst_1599_);
lean_closure_set(v___x_1602_, 4, v_inst_1600_);
lean_closure_set(v___x_1602_, 5, v_inst_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object* v_00_u03b1_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1609_, 0, lean_box(0));
lean_closure_set(v___x_1609_, 1, lean_box(0));
lean_closure_set(v___x_1609_, 2, lean_box(0));
lean_closure_set(v___x_1609_, 3, v_inst_1606_);
lean_closure_set(v___x_1609_, 4, v_inst_1607_);
lean_closure_set(v___x_1609_, 5, v_inst_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_toApplicative_1614_; lean_object* v_throw_1615_; lean_object* v_toBind_1616_; lean_object* v_toPure_1617_; lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; 
v_toApplicative_1614_ = lean_ctor_get(v_inst_1610_, 0);
lean_inc_ref(v_toApplicative_1614_);
v_throw_1615_ = lean_ctor_get(v_inst_1611_, 0);
lean_inc(v_throw_1615_);
lean_dec_ref(v_inst_1611_);
v_toBind_1616_ = lean_ctor_get(v_inst_1610_, 1);
lean_inc(v_toBind_1616_);
lean_dec_ref(v_inst_1610_);
v_toPure_1617_ = lean_ctor_get(v_toApplicative_1614_, 1);
lean_inc(v_toPure_1617_);
lean_dec_ref(v_toApplicative_1614_);
v___x_1618_ = lean_apply_2(v_throw_1615_, lean_box(0), v_a_1612_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1619_, 0, v_a_1613_);
lean_closure_set(v___f_1619_, 1, v_toPure_1617_);
v___x_1620_ = lean_apply_4(v_toBind_1616_, lean_box(0), lean_box(0), v___x_1618_, v___f_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(lean_object* v_00_u03b1_1621_, lean_object* v_00_u03b2_1622_, lean_object* v_m_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_00_u03b5_1627_, lean_object* v_inst_1628_, lean_object* v_00_u03b1_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_toApplicative_1632_; lean_object* v_throw_1633_; lean_object* v_toBind_1634_; lean_object* v_toPure_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; 
v_toApplicative_1632_ = lean_ctor_get(v_inst_1626_, 0);
lean_inc_ref(v_toApplicative_1632_);
v_throw_1633_ = lean_ctor_get(v_inst_1628_, 0);
lean_inc(v_throw_1633_);
lean_dec_ref(v_inst_1628_);
v_toBind_1634_ = lean_ctor_get(v_inst_1626_, 1);
lean_inc(v_toBind_1634_);
lean_dec_ref(v_inst_1626_);
v_toPure_1635_ = lean_ctor_get(v_toApplicative_1632_, 1);
lean_inc(v_toPure_1635_);
lean_dec_ref(v_toApplicative_1632_);
v___x_1636_ = lean_apply_2(v_throw_1633_, lean_box(0), v_a_1630_);
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1637_, 0, v_a_1631_);
lean_closure_set(v___f_1637_, 1, v_toPure_1635_);
v___x_1638_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v___x_1636_, v___f_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_m_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_00_u03b5_1645_, lean_object* v_inst_1646_, lean_object* v_00_u03b1_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(v_00_u03b1_1639_, v_00_u03b2_1640_, v_m_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_00_u03b5_1645_, v_inst_1646_, v_00_u03b1_1647_, v_a_1648_, v_a_1649_);
lean_dec_ref(v_inst_1643_);
lean_dec_ref(v_inst_1642_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(lean_object* v_c_1651_, lean_object* v_s_1652_, lean_object* v_e_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_apply_2(v_c_1651_, v_e_1653_, v_s_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(lean_object* v_inst_1655_, lean_object* v_x_1656_, lean_object* v_c_1657_, lean_object* v_s_1658_){
_start:
{
lean_object* v_tryCatch_1659_; lean_object* v___f_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_tryCatch_1659_ = lean_ctor_get(v_inst_1655_, 1);
lean_inc(v_tryCatch_1659_);
lean_dec_ref(v_inst_1655_);
lean_inc_ref(v_s_1658_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1660_, 0, v_c_1657_);
lean_closure_set(v___f_1660_, 1, v_s_1658_);
v___x_1661_ = lean_apply_1(v_x_1656_, v_s_1658_);
v___x_1662_ = lean_apply_3(v_tryCatch_1659_, lean_box(0), v___x_1661_, v___f_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(lean_object* v_00_u03b1_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_m_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_00_u03b5_1668_, lean_object* v_inst_1669_, lean_object* v_00_u03b1_1670_, lean_object* v_x_1671_, lean_object* v_c_1672_, lean_object* v_s_1673_){
_start:
{
lean_object* v_tryCatch_1674_; lean_object* v___f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_tryCatch_1674_ = lean_ctor_get(v_inst_1669_, 1);
lean_inc(v_tryCatch_1674_);
lean_dec_ref(v_inst_1669_);
lean_inc_ref(v_s_1673_);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1675_, 0, v_c_1672_);
lean_closure_set(v___f_1675_, 1, v_s_1673_);
v___x_1676_ = lean_apply_1(v_x_1671_, v_s_1673_);
v___x_1677_ = lean_apply_3(v_tryCatch_1674_, lean_box(0), v___x_1676_, v___f_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_m_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_00_u03b5_1683_, lean_object* v_inst_1684_, lean_object* v_00_u03b1_1685_, lean_object* v_x_1686_, lean_object* v_c_1687_, lean_object* v_s_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(v_00_u03b1_1678_, v_00_u03b2_1679_, v_m_1680_, v_inst_1681_, v_inst_1682_, v_00_u03b5_1683_, v_inst_1684_, v_00_u03b1_1685_, v_x_1686_, v_c_1687_, v_s_1688_);
lean_dec_ref(v_inst_1682_);
lean_dec_ref(v_inst_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_inc_ref(v_inst_1693_);
lean_inc_ref(v_inst_1691_);
lean_inc_ref(v_inst_1690_);
v___x_1694_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed), 11, 8);
lean_closure_set(v___x_1694_, 0, lean_box(0));
lean_closure_set(v___x_1694_, 1, lean_box(0));
lean_closure_set(v___x_1694_, 2, lean_box(0));
lean_closure_set(v___x_1694_, 3, v_inst_1690_);
lean_closure_set(v___x_1694_, 4, v_inst_1691_);
lean_closure_set(v___x_1694_, 5, v_inst_1692_);
lean_closure_set(v___x_1694_, 6, lean_box(0));
lean_closure_set(v___x_1694_, 7, v_inst_1693_);
v___x_1695_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed), 11, 7);
lean_closure_set(v___x_1695_, 0, lean_box(0));
lean_closure_set(v___x_1695_, 1, lean_box(0));
lean_closure_set(v___x_1695_, 2, lean_box(0));
lean_closure_set(v___x_1695_, 3, v_inst_1690_);
lean_closure_set(v___x_1695_, 4, v_inst_1691_);
lean_closure_set(v___x_1695_, 5, lean_box(0));
lean_closure_set(v___x_1695_, 6, v_inst_1693_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_m_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_00_u03b5_1703_, lean_object* v_inst_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(v_inst_1700_, v_inst_1701_, v_inst_1702_, v_inst_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(lean_object* v_fst_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_apply_1(v_x_1708_, v_fst_1706_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(lean_object* v_snd_1710_, lean_object* v_toPure_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_a_1712_);
lean_ctor_set(v___x_1713_, 1, v_snd_1710_);
v___x_1714_ = lean_apply_2(v_toPure_1711_, lean_box(0), v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(lean_object* v_f_1715_, lean_object* v_toPure_1716_, lean_object* v_toBind_1717_, lean_object* v_____x_1718_){
_start:
{
lean_object* v_fst_1719_; lean_object* v_snd_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; 
v_fst_1719_ = lean_ctor_get(v_____x_1718_, 0);
lean_inc(v_fst_1719_);
v_snd_1720_ = lean_ctor_get(v_____x_1718_, 1);
lean_inc(v_snd_1720_);
lean_dec_ref(v_____x_1718_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1721_, 0, v_fst_1719_);
v___x_1722_ = lean_apply_1(v_f_1715_, v___f_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1723_, 0, v_snd_1720_);
lean_closure_set(v___f_1723_, 1, v_toPure_1716_);
v___x_1724_ = lean_apply_4(v_toBind_1717_, lean_box(0), lean_box(0), v___x_1722_, v___f_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(lean_object* v_inst_1725_, lean_object* v_f_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_toApplicative_1728_; lean_object* v_toBind_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1740_; 
v_toApplicative_1728_ = lean_ctor_get(v_inst_1725_, 0);
v_toBind_1729_ = lean_ctor_get(v_inst_1725_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_inst_1725_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1731_ = v_inst_1725_;
v_isShared_1732_ = v_isSharedCheck_1740_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_toBind_1729_);
lean_inc(v_toApplicative_1728_);
lean_dec(v_inst_1725_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1740_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_toPure_1733_; lean_object* v___f_1734_; lean_object* v___x_1736_; 
v_toPure_1733_ = lean_ctor_get(v_toApplicative_1728_, 1);
lean_inc_n(v_toPure_1733_, 2);
lean_dec_ref(v_toApplicative_1728_);
lean_inc(v_toBind_1729_);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1734_, 0, v_f_1726_);
lean_closure_set(v___f_1734_, 1, v_toPure_1733_);
lean_closure_set(v___f_1734_, 2, v_toBind_1729_);
lean_inc_ref(v_a_1727_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_a_1727_);
lean_ctor_set(v___x_1731_, 0, v_a_1727_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1727_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1727_);
v___x_1736_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_apply_2(v_toPure_1733_, lean_box(0), v___x_1736_);
v___x_1738_ = lean_apply_4(v_toBind_1729_, lean_box(0), lean_box(0), v___x_1737_, v___f_1734_);
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_m_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_00_u03b1_1747_, lean_object* v_f_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_toApplicative_1750_; lean_object* v_toBind_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1762_; 
v_toApplicative_1750_ = lean_ctor_get(v_inst_1746_, 0);
v_toBind_1751_ = lean_ctor_get(v_inst_1746_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_inst_1746_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1753_ = v_inst_1746_;
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_toBind_1751_);
lean_inc(v_toApplicative_1750_);
lean_dec(v_inst_1746_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_toPure_1755_; lean_object* v___f_1756_; lean_object* v___x_1758_; 
v_toPure_1755_ = lean_ctor_get(v_toApplicative_1750_, 1);
lean_inc_n(v_toPure_1755_, 2);
lean_dec_ref(v_toApplicative_1750_);
lean_inc(v_toBind_1751_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1756_, 0, v_f_1748_);
lean_closure_set(v___f_1756_, 1, v_toPure_1755_);
lean_closure_set(v___f_1756_, 2, v_toBind_1751_);
lean_inc_ref(v_a_1749_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v_a_1749_);
lean_ctor_set(v___x_1753_, 0, v_a_1749_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1749_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_a_1749_);
v___x_1758_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_apply_2(v_toPure_1755_, lean_box(0), v___x_1758_);
v___x_1760_ = lean_apply_4(v_toBind_1751_, lean_box(0), lean_box(0), v___x_1759_, v___f_1756_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_m_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_00_u03b1_1769_, lean_object* v_f_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_MonadStateCacheT_instMonadControl___aux__1(v_00_u03b1_1763_, v_00_u03b2_1764_, v_m_1765_, v_inst_1766_, v_inst_1767_, v_inst_1768_, v_00_u03b1_1769_, v_f_1770_, v_a_1771_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(lean_object* v_fst_1773_, lean_object* v_toPure_1774_, lean_object* v_____x_1775_){
_start:
{
lean_object* v_snd_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1784_; 
v_snd_1776_ = lean_ctor_get(v_____x_1775_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_____x_1775_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_____x_1775_, 0);
lean_dec(v_unused_1785_);
v___x_1778_ = v_____x_1775_;
v_isShared_1779_ = v_isSharedCheck_1784_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snd_1776_);
lean_dec(v_____x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1784_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_fst_1773_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_fst_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_snd_1776_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_apply_2(v_toPure_1774_, lean_box(0), v___x_1781_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(lean_object* v_toPure_1786_, lean_object* v_toBind_1787_, lean_object* v_____x_1788_){
_start:
{
lean_object* v_fst_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1802_; 
v_fst_1789_ = lean_ctor_get(v_____x_1788_, 0);
lean_inc(v_fst_1789_);
lean_dec_ref(v_____x_1788_);
v_fst_1790_ = lean_ctor_get(v_fst_1789_, 0);
v_snd_1791_ = lean_ctor_get(v_fst_1789_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_fst_1789_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1793_ = v_fst_1789_;
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_fst_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_inc(v_toPure_1786_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1795_, 0, v_fst_1790_);
lean_closure_set(v___f_1795_, 1, v_toPure_1786_);
v___x_1796_ = lean_box(0);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_snd_1791_);
v___x_1798_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_apply_2(v_toPure_1786_, lean_box(0), v___x_1798_);
v___x_1800_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1799_, v___f_1795_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2(lean_object* v_a_1803_, lean_object* v_toPure_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_a_1805_);
lean_ctor_set(v___x_1806_, 1, v_a_1803_);
v___x_1807_ = lean_apply_2(v_toPure_1804_, lean_box(0), v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(lean_object* v_inst_1808_, lean_object* v_x_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_toApplicative_1811_; lean_object* v_toBind_1812_; lean_object* v_toPure_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_toApplicative_1811_ = lean_ctor_get(v_inst_1808_, 0);
lean_inc_ref(v_toApplicative_1811_);
v_toBind_1812_ = lean_ctor_get(v_inst_1808_, 1);
lean_inc_n(v_toBind_1812_, 3);
lean_dec_ref(v_inst_1808_);
v_toPure_1813_ = lean_ctor_get(v_toApplicative_1811_, 1);
lean_inc_n(v_toPure_1813_, 2);
lean_dec_ref(v_toApplicative_1811_);
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1814_, 0, v_toPure_1813_);
lean_closure_set(v___f_1814_, 1, v_toBind_1812_);
v___f_1815_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1815_, 0, v_a_1810_);
lean_closure_set(v___f_1815_, 1, v_toPure_1813_);
v___x_1816_ = lean_apply_4(v_toBind_1812_, lean_box(0), lean_box(0), v_x_1809_, v___f_1815_);
v___x_1817_ = lean_apply_4(v_toBind_1812_, lean_box(0), lean_box(0), v___x_1816_, v___f_1814_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_m_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_00_u03b1_1824_, lean_object* v_x_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_toApplicative_1827_; lean_object* v_toBind_1828_; lean_object* v_toPure_1829_; lean_object* v___f_1830_; lean_object* v___f_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_toApplicative_1827_ = lean_ctor_get(v_inst_1823_, 0);
lean_inc_ref(v_toApplicative_1827_);
v_toBind_1828_ = lean_ctor_get(v_inst_1823_, 1);
lean_inc_n(v_toBind_1828_, 3);
lean_dec_ref(v_inst_1823_);
v_toPure_1829_ = lean_ctor_get(v_toApplicative_1827_, 1);
lean_inc_n(v_toPure_1829_, 2);
lean_dec_ref(v_toApplicative_1827_);
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1830_, 0, v_toPure_1829_);
lean_closure_set(v___f_1830_, 1, v_toBind_1828_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1831_, 0, v_a_1826_);
lean_closure_set(v___f_1831_, 1, v_toPure_1829_);
v___x_1832_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v_x_1825_, v___f_1831_);
v___x_1833_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1832_, v___f_1830_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_m_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_00_u03b1_1840_, lean_object* v_x_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_MonadStateCacheT_instMonadControl___aux__3(v_00_u03b1_1834_, v_00_u03b2_1835_, v_m_1836_, v_inst_1837_, v_inst_1838_, v_inst_1839_, v_00_u03b1_1840_, v_x_1841_, v_a_1842_);
lean_dec_ref(v_inst_1838_);
lean_dec_ref(v_inst_1837_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_inc_ref(v_inst_1846_);
lean_inc_ref(v_inst_1845_);
lean_inc_ref(v_inst_1844_);
v___x_1847_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed), 9, 6);
lean_closure_set(v___x_1847_, 0, lean_box(0));
lean_closure_set(v___x_1847_, 1, lean_box(0));
lean_closure_set(v___x_1847_, 2, lean_box(0));
lean_closure_set(v___x_1847_, 3, v_inst_1844_);
lean_closure_set(v___x_1847_, 4, v_inst_1845_);
lean_closure_set(v___x_1847_, 5, v_inst_1846_);
v___x_1848_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed), 9, 6);
lean_closure_set(v___x_1848_, 0, lean_box(0));
lean_closure_set(v___x_1848_, 1, lean_box(0));
lean_closure_set(v___x_1848_, 2, lean_box(0));
lean_closure_set(v___x_1848_, 3, v_inst_1844_);
lean_closure_set(v___x_1848_, 4, v_inst_1845_);
lean_closure_set(v___x_1848_, 5, v_inst_1846_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_m_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_1853_, v_inst_1854_, v_inst_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(lean_object* v_h_1857_, lean_object* v_s_1858_, lean_object* v_x_1859_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_apply_2(v_h_1857_, v___x_1860_, v_s_1858_);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v_s_1858_);
v_val_1862_ = lean_ctor_get(v_x_1859_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1864_ = v_x_1859_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_val_1862_);
lean_dec(v_x_1859_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1869_; 
v_fst_1866_ = lean_ctor_get(v_val_1862_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v_val_1862_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_val_1862_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_fst_1866_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1866_);
v___x_1869_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_apply_2(v_h_1857_, v___x_1869_, v_snd_1867_);
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(lean_object* v_toPure_1873_, lean_object* v_____x_1874_){
_start:
{
lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v_fst_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1894_; 
v_fst_1875_ = lean_ctor_get(v_____x_1874_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_____x_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec_ref(v_____x_1874_);
v_fst_1877_ = lean_ctor_get(v_fst_1875_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_fst_1875_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_fst_1875_, 1);
lean_dec(v_unused_1895_);
v___x_1879_ = v_fst_1875_;
v_isShared_1880_ = v_isSharedCheck_1894_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_fst_1877_);
lean_dec(v_fst_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1894_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1893_; 
v_fst_1881_ = lean_ctor_get(v_snd_1876_, 0);
v_snd_1882_ = lean_ctor_get(v_snd_1876_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_snd_1876_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1884_ = v_snd_1876_;
v_isShared_1885_ = v_isSharedCheck_1893_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
lean_dec(v_snd_1876_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1893_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v_fst_1881_);
lean_ctor_set(v___x_1884_, 0, v_fst_1877_);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_fst_1881_);
v___x_1887_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_snd_1882_);
lean_ctor_set(v___x_1879_, 0, v___x_1887_);
v___x_1889_ = v___x_1879_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_snd_1882_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_apply_2(v_toPure_1873_, lean_box(0), v___x_1889_);
return v___x_1890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_x_1898_, lean_object* v_h_1899_, lean_object* v_s_1900_){
_start:
{
lean_object* v_toApplicative_1901_; lean_object* v_toBind_1902_; lean_object* v_toPure_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_toApplicative_1901_ = lean_ctor_get(v_inst_1896_, 0);
lean_inc_ref(v_toApplicative_1901_);
v_toBind_1902_ = lean_ctor_get(v_inst_1896_, 1);
lean_inc(v_toBind_1902_);
lean_dec_ref(v_inst_1896_);
v_toPure_1903_ = lean_ctor_get(v_toApplicative_1901_, 1);
lean_inc(v_toPure_1903_);
lean_dec_ref(v_toApplicative_1901_);
lean_inc_ref(v_s_1900_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1904_, 0, v_h_1899_);
lean_closure_set(v___f_1904_, 1, v_s_1900_);
v___x_1905_ = lean_apply_1(v_x_1898_, v_s_1900_);
v___f_1906_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1906_, 0, v_toPure_1903_);
v___x_1907_ = lean_apply_4(v_inst_1897_, lean_box(0), lean_box(0), v___x_1905_, v___f_1904_);
v___x_1908_ = lean_apply_4(v_toBind_1902_, lean_box(0), lean_box(0), v___x_1907_, v___f_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1(lean_object* v_00_u03b1_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_m_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_00_u03b1_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_x_1918_, lean_object* v_h_1919_, lean_object* v_s_1920_){
_start:
{
lean_object* v_toApplicative_1921_; lean_object* v_toBind_1922_; lean_object* v_toPure_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_toApplicative_1921_ = lean_ctor_get(v_inst_1914_, 0);
lean_inc_ref(v_toApplicative_1921_);
v_toBind_1922_ = lean_ctor_get(v_inst_1914_, 1);
lean_inc(v_toBind_1922_);
lean_dec_ref(v_inst_1914_);
v_toPure_1923_ = lean_ctor_get(v_toApplicative_1921_, 1);
lean_inc(v_toPure_1923_);
lean_dec_ref(v_toApplicative_1921_);
lean_inc_ref(v_s_1920_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1924_, 0, v_h_1919_);
lean_closure_set(v___f_1924_, 1, v_s_1920_);
v___x_1925_ = lean_apply_1(v_x_1918_, v_s_1920_);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1926_, 0, v_toPure_1923_);
v___x_1927_ = lean_apply_4(v_inst_1915_, lean_box(0), lean_box(0), v___x_1925_, v___f_1924_);
v___x_1928_ = lean_apply_4(v_toBind_1922_, lean_box(0), lean_box(0), v___x_1927_, v___f_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_00_u03b2_1930_, lean_object* v_m_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_00_u03b1_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, lean_object* v_h_1939_, lean_object* v_s_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_MonadStateCacheT_instMonadFinally___aux__1(v_00_u03b1_1929_, v_00_u03b2_1930_, v_m_1931_, v_inst_1932_, v_inst_1933_, v_inst_1934_, v_inst_1935_, v_00_u03b1_1936_, v_00_u03b2_1937_, v_x_1938_, v_h_1939_, v_s_1940_);
lean_dec_ref(v_inst_1933_);
lean_dec_ref(v_inst_1932_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_1946_, 0, lean_box(0));
lean_closure_set(v___x_1946_, 1, lean_box(0));
lean_closure_set(v___x_1946_, 2, lean_box(0));
lean_closure_set(v___x_1946_, 3, v_inst_1942_);
lean_closure_set(v___x_1946_, 4, v_inst_1943_);
lean_closure_set(v___x_1946_, 5, v_inst_1944_);
lean_closure_set(v___x_1946_, 6, v_inst_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object* v_00_u03b1_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_m_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed), 12, 7);
lean_closure_set(v___x_1954_, 0, lean_box(0));
lean_closure_set(v___x_1954_, 1, lean_box(0));
lean_closure_set(v___x_1954_, 2, lean_box(0));
lean_closure_set(v___x_1954_, 3, v_inst_1950_);
lean_closure_set(v___x_1954_, 4, v_inst_1951_);
lean_closure_set(v___x_1954_, 5, v_inst_1952_);
lean_closure_set(v___x_1954_, 6, v_inst_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(lean_object* v_a_1955_, lean_object* v_toPure_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1957_);
lean_ctor_set(v___x_1958_, 1, v_a_1955_);
v___x_1959_ = lean_apply_2(v_toPure_1956_, lean_box(0), v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_toApplicative_1963_; lean_object* v_getRef_1964_; lean_object* v_toBind_1965_; lean_object* v_toPure_1966_; lean_object* v___f_1967_; lean_object* v___x_1968_; 
v_toApplicative_1963_ = lean_ctor_get(v_inst_1960_, 0);
lean_inc_ref(v_toApplicative_1963_);
v_getRef_1964_ = lean_ctor_get(v_inst_1961_, 0);
lean_inc(v_getRef_1964_);
lean_dec_ref(v_inst_1961_);
v_toBind_1965_ = lean_ctor_get(v_inst_1960_, 1);
lean_inc(v_toBind_1965_);
lean_dec_ref(v_inst_1960_);
v_toPure_1966_ = lean_ctor_get(v_toApplicative_1963_, 1);
lean_inc(v_toPure_1966_);
lean_dec_ref(v_toApplicative_1963_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1967_, 0, v_a_1962_);
lean_closure_set(v___f_1967_, 1, v_toPure_1966_);
v___x_1968_ = lean_apply_4(v_toBind_1965_, lean_box(0), lean_box(0), v_getRef_1964_, v___f_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1(lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_m_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_toApplicative_1977_; lean_object* v_getRef_1978_; lean_object* v_toBind_1979_; lean_object* v_toPure_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; 
v_toApplicative_1977_ = lean_ctor_get(v_inst_1974_, 0);
lean_inc_ref(v_toApplicative_1977_);
v_getRef_1978_ = lean_ctor_get(v_inst_1975_, 0);
lean_inc(v_getRef_1978_);
lean_dec_ref(v_inst_1975_);
v_toBind_1979_ = lean_ctor_get(v_inst_1974_, 1);
lean_inc(v_toBind_1979_);
lean_dec_ref(v_inst_1974_);
v_toPure_1980_ = lean_ctor_get(v_toApplicative_1977_, 1);
lean_inc(v_toPure_1980_);
lean_dec_ref(v_toApplicative_1977_);
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1981_, 0, v_a_1976_);
lean_closure_set(v___f_1981_, 1, v_toPure_1980_);
v___x_1982_ = lean_apply_4(v_toBind_1979_, lean_box(0), lean_box(0), v_getRef_1978_, v___f_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_00_u03b2_1984_, lean_object* v_m_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_MonadStateCacheT_instMonadRef___aux__1(v_00_u03b1_1983_, v_00_u03b2_1984_, v_m_1985_, v_inst_1986_, v_inst_1987_, v_inst_1988_, v_inst_1989_, v_a_1990_);
lean_dec_ref(v_inst_1987_);
lean_dec_ref(v_inst_1986_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(lean_object* v_inst_1992_, lean_object* v_ref_1993_, lean_object* v_x_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_withRef_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_withRef_1996_ = lean_ctor_get(v_inst_1992_, 1);
lean_inc(v_withRef_1996_);
lean_dec_ref(v_inst_1992_);
v___x_1997_ = lean_apply_1(v_x_1994_, v_a_1995_);
v___x_1998_ = lean_apply_3(v_withRef_1996_, lean_box(0), v_ref_1993_, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3(lean_object* v_00_u03b1_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_m_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_00_u03b1_2005_, lean_object* v_ref_2006_, lean_object* v_x_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_withRef_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_withRef_2009_ = lean_ctor_get(v_inst_2004_, 1);
lean_inc(v_withRef_2009_);
lean_dec_ref(v_inst_2004_);
v___x_2010_ = lean_apply_1(v_x_2007_, v_a_2008_);
v___x_2011_ = lean_apply_3(v_withRef_2009_, lean_box(0), v_ref_2006_, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_m_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_00_u03b1_2018_, lean_object* v_ref_2019_, lean_object* v_x_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_MonadStateCacheT_instMonadRef___aux__3(v_00_u03b1_2012_, v_00_u03b2_2013_, v_m_2014_, v_inst_2015_, v_inst_2016_, v_inst_2017_, v_00_u03b1_2018_, v_ref_2019_, v_x_2020_, v_a_2021_);
lean_dec_ref(v_inst_2016_);
lean_dec_ref(v_inst_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_inc_ref(v_inst_2026_);
lean_inc_ref(v_inst_2024_);
lean_inc_ref(v_inst_2023_);
v___x_2027_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed), 8, 7);
lean_closure_set(v___x_2027_, 0, lean_box(0));
lean_closure_set(v___x_2027_, 1, lean_box(0));
lean_closure_set(v___x_2027_, 2, lean_box(0));
lean_closure_set(v___x_2027_, 3, v_inst_2023_);
lean_closure_set(v___x_2027_, 4, v_inst_2024_);
lean_closure_set(v___x_2027_, 5, v_inst_2025_);
lean_closure_set(v___x_2027_, 6, v_inst_2026_);
v___x_2028_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed), 10, 6);
lean_closure_set(v___x_2028_, 0, lean_box(0));
lean_closure_set(v___x_2028_, 1, lean_box(0));
lean_closure_set(v___x_2028_, 2, lean_box(0));
lean_closure_set(v___x_2028_, 3, v_inst_2023_);
lean_closure_set(v___x_2028_, 4, v_inst_2024_);
lean_closure_set(v___x_2028_, 5, v_inst_2026_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object* v_00_u03b1_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_m_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(v_inst_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_);
return v___x_2037_;
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
