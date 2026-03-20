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
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_tryFinally___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_StateT_tryFinally___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_monadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_monadControl___redArg___lam__5(lean_object*, lean_object*);
lean_object* l_StateT_monadControl___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_StateT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MonadCacheT_instMonadLift___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_MonadCacheT_instMonadLift___closed__0 = (const lean_object*)&l_Lean_MonadCacheT_instMonadLift___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MonadCacheT_instMonadControl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadCacheT_instMonadControl___closed__0;
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MonadCacheT_instMonadRef___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MonadCacheT_instMonadRef___redArg___closed__0 = (const lean_object*)&l_Lean_MonadCacheT_instMonadRef___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MonadStateCacheT_instMonadRef___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg___closed__0 = (const lean_object*)&l_Lean_MonadStateCacheT_instMonadRef___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_216_){
_start:
{
lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc(v_inst_216_);
v___f_217_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1), 3, 1);
lean_closure_set(v___f_217_, 0, v_inst_216_);
v___x_218_ = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(v___x_218_, 0, lean_box(0));
lean_closure_set(v___x_218_, 1, lean_box(0));
lean_closure_set(v___x_218_, 2, lean_box(0));
lean_closure_set(v___x_218_, 3, v_inst_216_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___f_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03c9_220_, lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_m_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03c9_229_, lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_m_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(v_00_u03c9_229_, v_00_u03b1_230_, v_00_u03b2_231_, v_m_232_, v_inst_233_, v_inst_234_, v_inst_235_, v_inst_236_);
lean_dec_ref(v_inst_235_);
lean_dec_ref(v_inst_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__0(lean_object* v_a_238_, lean_object* v_toPure_239_, lean_object* v_s_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_a_238_);
lean_ctor_set(v___x_241_, 1, v_s_240_);
v___x_242_ = lean_apply_2(v_toPure_239_, lean_box(0), v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__1(lean_object* v_toPure_243_, lean_object* v_ref_244_, lean_object* v_inst_245_, lean_object* v_toBind_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_248_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_248_, 0, v_a_247_);
lean_closure_set(v___f_248_, 1, v_toPure_243_);
v___x_249_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_249_, 0, lean_box(0));
lean_closure_set(v___x_249_, 1, lean_box(0));
lean_closure_set(v___x_249_, 2, v_ref_244_);
v___x_250_ = lean_apply_2(v_inst_245_, lean_box(0), v___x_249_);
v___x_251_ = lean_apply_4(v_toBind_246_, lean_box(0), lean_box(0), v___x_250_, v___f_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__2(lean_object* v_toPure_252_, lean_object* v_inst_253_, lean_object* v_toBind_254_, lean_object* v_x_255_, lean_object* v_ref_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_inc(v_toBind_254_);
lean_inc(v_ref_256_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_257_, 0, v_toPure_252_);
lean_closure_set(v___f_257_, 1, v_ref_256_);
lean_closure_set(v___f_257_, 2, v_inst_253_);
lean_closure_set(v___f_257_, 3, v_toBind_254_);
v___x_258_ = lean_apply_1(v_x_255_, v_ref_256_);
v___x_259_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_258_, v___f_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg___lam__3(lean_object* v_toPure_260_, lean_object* v_____x_261_){
_start:
{
lean_object* v_fst_262_; lean_object* v___x_263_; 
v_fst_262_ = lean_ctor_get(v_____x_261_, 0);
lean_inc(v_fst_262_);
lean_dec_ref(v_____x_261_);
v___x_263_ = lean_apply_2(v_toPure_260_, lean_box(0), v_fst_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = lean_unsigned_to_nat(16u);
v___x_266_ = lean_mk_array(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__0, &l_Lean_MonadCacheT_run___redArg___closed__0_once, _init_l_Lean_MonadCacheT_run___redArg___closed__0);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_271_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, lean_box(0));
lean_closure_set(v___x_271_, 2, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___redArg(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_x_274_){
_start:
{
lean_object* v_toApplicative_275_; lean_object* v_toBind_276_; lean_object* v_toPure_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_toApplicative_275_ = lean_ctor_get(v_inst_273_, 0);
lean_inc_ref(v_toApplicative_275_);
v_toBind_276_ = lean_ctor_get(v_inst_273_, 1);
lean_inc(v_toBind_276_);
lean_dec_ref(v_inst_273_);
v_toPure_277_ = lean_ctor_get(v_toApplicative_275_, 1);
lean_inc(v_toPure_277_);
lean_dec_ref(v_toApplicative_275_);
v___x_278_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_272_);
v___x_279_ = lean_apply_2(v_inst_272_, lean_box(0), v___x_278_);
lean_inc(v_toBind_276_);
lean_inc(v_toPure_277_);
v___f_280_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_280_, 0, v_toPure_277_);
lean_closure_set(v___f_280_, 1, v_inst_272_);
lean_closure_set(v___f_280_, 2, v_toBind_276_);
lean_closure_set(v___f_280_, 3, v_x_274_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_281_, 0, v_toPure_277_);
lean_inc(v_toBind_276_);
v___x_282_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_279_, v___f_280_);
v___x_283_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_282_, v___f_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run(lean_object* v_00_u03c9_284_, lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_m_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_00_u03c3_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_toApplicative_295_; lean_object* v_toBind_296_; lean_object* v_toPure_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___f_300_; lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_toApplicative_295_ = lean_ctor_get(v_inst_292_, 0);
lean_inc_ref(v_toApplicative_295_);
v_toBind_296_ = lean_ctor_get(v_inst_292_, 1);
lean_inc(v_toBind_296_);
lean_dec_ref(v_inst_292_);
v_toPure_297_ = lean_ctor_get(v_toApplicative_295_, 1);
lean_inc(v_toPure_297_);
lean_dec_ref(v_toApplicative_295_);
v___x_298_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__2, &l_Lean_MonadCacheT_run___redArg___closed__2_once, _init_l_Lean_MonadCacheT_run___redArg___closed__2);
lean_inc(v_inst_291_);
v___x_299_ = lean_apply_2(v_inst_291_, lean_box(0), v___x_298_);
lean_inc(v_toBind_296_);
lean_inc(v_toPure_297_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_300_, 0, v_toPure_297_);
lean_closure_set(v___f_300_, 1, v_inst_291_);
lean_closure_set(v___f_300_, 2, v_toBind_296_);
lean_closure_set(v___f_300_, 3, v_x_294_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_301_, 0, v_toPure_297_);
lean_inc(v_toBind_296_);
v___x_302_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_299_, v___f_300_);
v___x_303_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_302_, v___f_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_run___boxed(lean_object* v_00_u03c9_304_, lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_00_u03c3_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_MonadCacheT_run(v_00_u03c9_304_, v_00_u03b1_305_, v_00_u03b2_306_, v_m_307_, v_inst_308_, v_inst_309_, v_inst_310_, v_inst_311_, v_inst_312_, v_00_u03c3_313_, v_x_314_);
lean_dec_ref(v_inst_310_);
lean_dec_ref(v_inst_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object* v_inst_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_ReaderT_instMonad___redArg(v_inst_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad(lean_object* v_00_u03c9_318_, lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_m_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_ReaderT_instMonad___redArg(v_inst_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonad___boxed(lean_object* v_00_u03c9_327_, lean_object* v_00_u03b1_328_, lean_object* v_00_u03b2_329_, lean_object* v_m_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_MonadCacheT_instMonad(v_00_u03c9_327_, v_00_u03b1_328_, v_00_u03b2_329_, v_m_330_, v_inst_331_, v_inst_332_, v_inst_333_, v_inst_334_);
lean_dec_ref(v_inst_333_);
lean_dec_ref(v_inst_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift(lean_object* v_00_u03c9_337_, lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_m_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = ((lean_object*)(l_Lean_MonadCacheT_instMonadLift___closed__0));
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadLift___boxed(lean_object* v_00_u03c9_345_, lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_MonadCacheT_instMonadLift(v_00_u03c9_345_, v_00_u03b1_346_, v_00_u03b2_347_, v_m_348_, v_inst_349_, v_inst_350_, v_inst_351_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object* v_inst_353_){
_start:
{
lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
lean_inc_ref(v_inst_353_);
v___f_354_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_354_, 0, v_inst_353_);
v___f_355_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_355_, 0, v_inst_353_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___f_354_);
lean_ctor_set(v___x_356_, 1, v___f_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf(lean_object* v_00_u03c9_357_, lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_m_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_00_u03b5_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadExceptOf___boxed(lean_object* v_00_u03c9_367_, lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_m_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_00_u03b5_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_MonadCacheT_instMonadExceptOf(v_00_u03c9_367_, v_00_u03b1_368_, v_00_u03b2_369_, v_m_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_00_u03b5_374_, v_inst_375_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_MonadCacheT_instMonadControl___closed__0(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_instMonadControlReaderT(lean_box(0), lean_box(0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl(lean_object* v_00_u03c9_378_, lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_m_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&l_Lean_MonadCacheT_instMonadControl___closed__0, &l_Lean_MonadCacheT_instMonadControl___closed__0_once, _init_l_Lean_MonadCacheT_instMonadControl___closed__0);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadControl___boxed(lean_object* v_00_u03c9_386_, lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_m_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_MonadCacheT_instMonadControl(v_00_u03c9_386_, v_00_u03b1_387_, v_00_u03b2_388_, v_m_389_, v_inst_390_, v_inst_391_, v_inst_392_);
lean_dec_ref(v_inst_392_);
lean_dec_ref(v_inst_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___redArg(lean_object* v_inst_394_){
_start:
{
lean_object* v___f_395_; 
v___f_395_ = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(v___f_395_, 0, v_inst_394_);
return v___f_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally(lean_object* v_00_u03c9_396_, lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_m_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v___f_404_; 
v___f_404_ = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(v___f_404_, 0, v_inst_403_);
return v___f_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadFinally___boxed(lean_object* v_00_u03c9_405_, lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_MonadCacheT_instMonadFinally(v_00_u03c9_405_, v_00_u03b1_406_, v_00_u03b2_407_, v_m_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_);
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___redArg(lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v___x_416_ = ((lean_object*)(l_Lean_MonadCacheT_instMonadLift___closed__0));
v___f_417_ = ((lean_object*)(l_Lean_MonadCacheT_instMonadRef___redArg___closed__0));
v___x_418_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_416_, v___f_417_, v_inst_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef(lean_object* v_00_u03c9_419_, lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_m_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_MonadCacheT_instMonadRef___redArg(v_inst_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instMonadRef___boxed(lean_object* v_00_u03c9_428_, lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_MonadCacheT_instMonadRef(v_00_u03c9_428_, v_00_u03b1_429_, v_00_u03b2_430_, v_m_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_inst_435_);
lean_dec_ref(v_inst_434_);
lean_dec_ref(v_inst_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___redArg(lean_object* v_inst_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_ReaderT_instAlternativeOfMonad___redArg(v_inst_438_, v_inst_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative(lean_object* v_00_u03c9_440_, lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_m_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_ReaderT_instAlternativeOfMonad___redArg(v_inst_448_, v_inst_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadCacheT_instAlternative___boxed(lean_object* v_00_u03c9_450_, lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_m_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_MonadCacheT_instAlternative(v_00_u03c9_450_, v_00_u03b1_451_, v_00_u03b2_452_, v_m_453_, v_inst_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_);
lean_dec_ref(v_inst_456_);
lean_dec_ref(v_inst_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(lean_object* v_inst_460_, lean_object* v_f_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_toApplicative_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_474_; 
v_toApplicative_463_ = lean_ctor_get(v_inst_460_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_inst_460_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_inst_460_, 1);
lean_dec(v_unused_475_);
v___x_465_ = v_inst_460_;
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_toApplicative_463_);
lean_dec(v_inst_460_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_toPure_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v_toPure_467_ = lean_ctor_get(v_toApplicative_463_, 1);
lean_inc(v_toPure_467_);
lean_dec_ref(v_toApplicative_463_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_apply_1(v_f_461_, v___y_462_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_469_);
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_471_ = v___x_465_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_2(v_toPure_467_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(lean_object* v_inst_476_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_inc_ref(v_inst_476_);
v___f_477_ = lean_alloc_closure((void*)(l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_477_, 0, v_inst_476_);
v___x_478_ = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(v___x_478_, 0, lean_box(0));
lean_closure_set(v___x_478_, 1, lean_box(0));
lean_closure_set(v___x_478_, 2, v_inst_476_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___f_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_m_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(v_00_u03b1_487_, v_00_u03b2_488_, v_m_489_, v_inst_490_, v_inst_491_, v_inst_492_);
lean_dec_ref(v_inst_491_);
lean_dec_ref(v_inst_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0(lean_object* v_x_494_){
_start:
{
lean_object* v_fst_495_; 
v_fst_495_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_fst_495_);
return v_fst_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_496_);
lean_dec_ref(v_x_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___redArg(lean_object* v_inst_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_toApplicative_501_; lean_object* v_toFunctor_502_; lean_object* v_map_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_toApplicative_501_ = lean_ctor_get(v_inst_499_, 0);
lean_inc_ref(v_toApplicative_501_);
lean_dec_ref(v_inst_499_);
v_toFunctor_502_ = lean_ctor_get(v_toApplicative_501_, 0);
lean_inc_ref(v_toFunctor_502_);
lean_dec_ref(v_toApplicative_501_);
v_map_503_ = lean_ctor_get(v_toFunctor_502_, 0);
lean_inc(v_map_503_);
lean_dec_ref(v_toFunctor_502_);
v___f_504_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_505_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_506_ = lean_apply_1(v_x_500_, v___x_505_);
v___x_507_ = lean_apply_4(v_map_503_, lean_box(0), lean_box(0), v___f_504_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_00_u03c3_514_, lean_object* v_x_515_){
_start:
{
lean_object* v_toApplicative_516_; lean_object* v_toFunctor_517_; lean_object* v_map_518_; lean_object* v___f_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_toApplicative_516_ = lean_ctor_get(v_inst_513_, 0);
lean_inc_ref(v_toApplicative_516_);
lean_dec_ref(v_inst_513_);
v_toFunctor_517_ = lean_ctor_get(v_toApplicative_516_, 0);
lean_inc_ref(v_toFunctor_517_);
lean_dec_ref(v_toApplicative_516_);
v_map_518_ = lean_ctor_get(v_toFunctor_517_, 0);
lean_inc(v_map_518_);
lean_dec_ref(v_toFunctor_517_);
v___f_519_ = ((lean_object*)(l_Lean_MonadStateCacheT_run___redArg___closed__0));
v___x_520_ = lean_obj_once(&l_Lean_MonadCacheT_run___redArg___closed__1, &l_Lean_MonadCacheT_run___redArg___closed__1_once, _init_l_Lean_MonadCacheT_run___redArg___closed__1);
v___x_521_ = lean_apply_1(v_x_515_, v___x_520_);
v___x_522_ = lean_apply_4(v_map_518_, lean_box(0), lean_box(0), v___f_519_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_run___boxed(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_, lean_object* v_m_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_00_u03c3_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MonadStateCacheT_run(v_00_u03b1_523_, v_00_u03b2_524_, v_m_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_00_u03c3_529_, v_x_530_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object* v_inst_532_){
_start:
{
lean_object* v___f_533_; lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc_ref(v_inst_532_);
v___f_533_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_533_, 0, v_inst_532_);
lean_inc_ref(v_inst_532_);
v___f_534_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_534_, 0, v_inst_532_);
lean_inc_ref(v_inst_532_);
v___f_535_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_535_, 0, v_inst_532_);
lean_inc_ref(v_inst_532_);
v___f_536_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_536_, 0, v_inst_532_);
lean_inc_ref(v_inst_532_);
v___x_537_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_537_, 0, lean_box(0));
lean_closure_set(v___x_537_, 1, lean_box(0));
lean_closure_set(v___x_537_, 2, v_inst_532_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___f_533_);
lean_inc_ref(v_inst_532_);
v___x_539_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_539_, 0, lean_box(0));
lean_closure_set(v___x_539_, 1, lean_box(0));
lean_closure_set(v___x_539_, 2, v_inst_532_);
v___x_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_ctor_set(v___x_540_, 2, v___f_534_);
lean_ctor_set(v___x_540_, 3, v___f_535_);
lean_ctor_set(v___x_540_, 4, v___f_536_);
v___x_541_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_541_, 0, lean_box(0));
lean_closure_set(v___x_541_, 1, lean_box(0));
lean_closure_set(v___x_541_, 2, v_inst_532_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_m_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonad___boxed(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_m_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_MonadStateCacheT_instMonad(v_00_u03b1_550_, v_00_u03b2_551_, v_m_552_, v_inst_553_, v_inst_554_, v_inst_555_);
lean_dec_ref(v_inst_554_);
lean_dec_ref(v_inst_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___redArg(lean_object* v_inst_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_558_, 0, lean_box(0));
lean_closure_set(v___x_558_, 1, lean_box(0));
lean_closure_set(v___x_558_, 2, v_inst_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_m_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_565_, 0, lean_box(0));
lean_closure_set(v___x_565_, 1, lean_box(0));
lean_closure_set(v___x_565_, 2, v_inst_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadLift___boxed(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_MonadStateCacheT_instMonadLift(v_00_u03b1_566_, v_00_u03b2_567_, v_m_568_, v_inst_569_, v_inst_570_, v_inst_571_);
lean_dec_ref(v_inst_570_);
lean_dec_ref(v_inst_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(lean_object* v_inst_573_, lean_object* v_inst_574_){
_start:
{
lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___x_577_; 
lean_inc_ref(v_inst_574_);
v___f_575_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_575_, 0, v_inst_574_);
lean_closure_set(v___f_575_, 1, v_inst_573_);
v___f_576_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_576_, 0, v_inst_574_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___f_575_);
lean_ctor_set(v___x_577_, 1, v___f_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_m_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_00_u03b5_584_, lean_object* v_inst_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(v_inst_583_, v_inst_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadExceptOf___boxed(lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_00_u03b5_593_, lean_object* v_inst_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_MonadStateCacheT_instMonadExceptOf(v_00_u03b1_587_, v_00_u03b2_588_, v_m_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_00_u03b5_593_, v_inst_594_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___redArg(lean_object* v_inst_596_){
_start:
{
lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; 
lean_inc_ref(v_inst_596_);
v___f_597_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__3), 4, 1);
lean_closure_set(v___f_597_, 0, v_inst_596_);
lean_inc_ref(v_inst_596_);
v___f_598_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__5), 2, 1);
lean_closure_set(v___f_598_, 0, v_inst_596_);
v___f_599_ = lean_alloc_closure((void*)(l_StateT_monadControl___redArg___lam__7), 5, 2);
lean_closure_set(v___f_599_, 0, v_inst_596_);
lean_closure_set(v___f_599_, 1, v___f_598_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_597_);
lean_ctor_set(v___x_600_, 1, v___f_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_m_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadControl___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_m_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_MonadStateCacheT_instMonadControl(v_00_u03b1_608_, v_00_u03b2_609_, v_m_610_, v_inst_611_, v_inst_612_, v_inst_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_inst_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___redArg(lean_object* v_inst_615_, lean_object* v_inst_616_){
_start:
{
lean_object* v_toApplicative_617_; lean_object* v_toBind_618_; lean_object* v_toPure_619_; lean_object* v___f_620_; lean_object* v___f_621_; 
v_toApplicative_617_ = lean_ctor_get(v_inst_615_, 0);
lean_inc_ref(v_toApplicative_617_);
v_toBind_618_ = lean_ctor_get(v_inst_615_, 1);
lean_inc(v_toBind_618_);
lean_dec_ref(v_inst_615_);
v_toPure_619_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_inc(v_toPure_619_);
lean_dec_ref(v_toApplicative_617_);
v___f_620_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__0), 2, 1);
lean_closure_set(v___f_620_, 0, v_toPure_619_);
v___f_621_ = lean_alloc_closure((void*)(l_StateT_tryFinally___redArg___lam__2), 8, 3);
lean_closure_set(v___f_621_, 0, v_inst_616_);
lean_closure_set(v___f_621_, 1, v_toBind_618_);
lean_closure_set(v___f_621_, 2, v___f_620_);
return v___f_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_MonadStateCacheT_instMonadFinally___redArg(v_inst_627_, v_inst_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadFinally___boxed(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_m_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_MonadStateCacheT_instMonadFinally(v_00_u03b1_630_, v_00_u03b2_631_, v_m_632_, v_inst_633_, v_inst_634_, v_inst_635_, v_inst_636_);
lean_dec_ref(v_inst_634_);
lean_dec_ref(v_inst_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___redArg(lean_object* v_inst_639_, lean_object* v_inst_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v___x_641_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_inst_639_);
v___f_642_ = ((lean_object*)(l_Lean_MonadStateCacheT_instMonadRef___redArg___closed__0));
v___x_643_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_641_, v___f_642_, v_inst_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(v_inst_649_, v_inst_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadStateCacheT_instMonadRef___boxed(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_m_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_MonadStateCacheT_instMonadRef(v_00_u03b1_652_, v_00_u03b2_653_, v_m_654_, v_inst_655_, v_inst_656_, v_inst_657_, v_inst_658_);
lean_dec_ref(v_inst_656_);
lean_dec_ref(v_inst_655_);
return v_res_659_;
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
