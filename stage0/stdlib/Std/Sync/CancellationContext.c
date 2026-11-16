// Lean compiler output
// Module: Std.Sync.CancellationContext
// Imports: public import Std.Sync.CancellationToken public import Init.Data.Ord.UInt
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
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
lean_object* l_Std_CancellationToken_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_new();
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(uint64_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(uint64_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t v_k_1_, lean_object* v_v_2_, lean_object* v_t_3_){
_start:
{
if (lean_obj_tag(v_t_3_) == 0)
{
lean_object* v_size_4_; lean_object* v_k_5_; lean_object* v_v_6_; lean_object* v_l_7_; lean_object* v_r_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_292_; 
v_size_4_ = lean_ctor_get(v_t_3_, 0);
v_k_5_ = lean_ctor_get(v_t_3_, 1);
v_v_6_ = lean_ctor_get(v_t_3_, 2);
v_l_7_ = lean_ctor_get(v_t_3_, 3);
v_r_8_ = lean_ctor_get(v_t_3_, 4);
v_isSharedCheck_292_ = !lean_is_exclusive(v_t_3_);
if (v_isSharedCheck_292_ == 0)
{
v___x_10_ = v_t_3_;
v_isShared_11_ = v_isSharedCheck_292_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_r_8_);
lean_inc(v_l_7_);
lean_inc(v_v_6_);
lean_inc(v_k_5_);
lean_inc(v_size_4_);
lean_dec(v_t_3_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_292_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint64_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = lean_unbox_uint64(v_k_5_);
v___x_13_ = lean_uint64_dec_lt(v_k_1_, v___x_12_);
if (v___x_13_ == 0)
{
uint64_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unbox_uint64(v_k_5_);
v___x_15_ = lean_uint64_dec_eq(v_k_1_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v_impl_16_; lean_object* v___x_17_; 
lean_dec(v_size_4_);
v_impl_16_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1_, v_v_2_, v_r_8_);
v___x_17_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7_) == 0)
{
lean_object* v_size_18_; lean_object* v_size_19_; lean_object* v_k_20_; lean_object* v_v_21_; lean_object* v_l_22_; lean_object* v_r_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_size_18_ = lean_ctor_get(v_l_7_, 0);
v_size_19_ = lean_ctor_get(v_impl_16_, 0);
v_k_20_ = lean_ctor_get(v_impl_16_, 1);
v_v_21_ = lean_ctor_get(v_impl_16_, 2);
v_l_22_ = lean_ctor_get(v_impl_16_, 3);
lean_inc(v_l_22_);
v_r_23_ = lean_ctor_get(v_impl_16_, 4);
v___x_24_ = lean_unsigned_to_nat(3u);
v___x_25_ = lean_nat_mul(v___x_24_, v_size_18_);
v___x_26_ = lean_nat_dec_lt(v___x_25_, v_size_19_);
lean_dec(v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
lean_dec(v_l_22_);
v___x_27_ = lean_nat_add(v___x_17_, v_size_18_);
v___x_28_ = lean_nat_add(v___x_27_, v_size_19_);
lean_dec(v___x_27_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_16_);
lean_ctor_set(v___x_10_, 0, v___x_28_);
v___x_30_ = v___x_10_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_31_, 4, v_impl_16_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
else
{
lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_95_; 
lean_inc(v_r_23_);
lean_inc(v_v_21_);
lean_inc(v_k_20_);
lean_inc(v_size_19_);
v_isSharedCheck_95_ = !lean_is_exclusive(v_impl_16_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; lean_object* v_unused_100_; 
v_unused_96_ = lean_ctor_get(v_impl_16_, 4);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_impl_16_, 3);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_impl_16_, 2);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_impl_16_, 1);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v_impl_16_, 0);
lean_dec(v_unused_100_);
v___x_33_ = v_impl_16_;
v_isShared_34_ = v_isSharedCheck_95_;
goto v_resetjp_32_;
}
else
{
lean_dec(v_impl_16_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_95_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_size_35_; lean_object* v_k_36_; lean_object* v_v_37_; lean_object* v_l_38_; lean_object* v_r_39_; lean_object* v_size_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_size_35_ = lean_ctor_get(v_l_22_, 0);
v_k_36_ = lean_ctor_get(v_l_22_, 1);
v_v_37_ = lean_ctor_get(v_l_22_, 2);
v_l_38_ = lean_ctor_get(v_l_22_, 3);
v_r_39_ = lean_ctor_get(v_l_22_, 4);
v_size_40_ = lean_ctor_get(v_r_23_, 0);
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lean_nat_mul(v___x_41_, v_size_40_);
v___x_43_ = lean_nat_dec_lt(v_size_35_, v___x_42_);
lean_dec(v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_71_; 
lean_inc(v_r_39_);
lean_inc(v_l_38_);
lean_inc(v_v_37_);
lean_inc(v_k_36_);
v_isSharedCheck_71_ = !lean_is_exclusive(v_l_22_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; lean_object* v_unused_73_; lean_object* v_unused_74_; lean_object* v_unused_75_; lean_object* v_unused_76_; 
v_unused_72_ = lean_ctor_get(v_l_22_, 4);
lean_dec(v_unused_72_);
v_unused_73_ = lean_ctor_get(v_l_22_, 3);
lean_dec(v_unused_73_);
v_unused_74_ = lean_ctor_get(v_l_22_, 2);
lean_dec(v_unused_74_);
v_unused_75_ = lean_ctor_get(v_l_22_, 1);
lean_dec(v_unused_75_);
v_unused_76_ = lean_ctor_get(v_l_22_, 0);
lean_dec(v_unused_76_);
v___x_45_ = v_l_22_;
v_isShared_46_ = v_isSharedCheck_71_;
goto v_resetjp_44_;
}
else
{
lean_dec(v_l_22_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_71_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_61_; 
v___x_47_ = lean_nat_add(v___x_17_, v_size_18_);
v___x_48_ = lean_nat_add(v___x_47_, v_size_19_);
lean_dec(v_size_19_);
if (lean_obj_tag(v_l_38_) == 0)
{
lean_object* v_size_69_; 
v_size_69_ = lean_ctor_get(v_l_38_, 0);
lean_inc(v_size_69_);
v___y_61_ = v_size_69_;
goto v___jp_60_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___y_61_ = v___x_70_;
goto v___jp_60_;
}
v___jp_49_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_nat_add(v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec(v___y_51_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 4, v_r_23_);
lean_ctor_set(v___x_45_, 3, v_r_39_);
lean_ctor_set(v___x_45_, 2, v_v_21_);
lean_ctor_set(v___x_45_, 1, v_k_20_);
lean_ctor_set(v___x_45_, 0, v___x_53_);
v___x_55_ = v___x_45_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_k_20_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v_v_21_);
lean_ctor_set(v_reuseFailAlloc_59_, 3, v_r_39_);
lean_ctor_set(v_reuseFailAlloc_59_, 4, v_r_23_);
v___x_55_ = v_reuseFailAlloc_59_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_57_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 4, v___x_55_);
lean_ctor_set(v___x_33_, 3, v___y_50_);
lean_ctor_set(v___x_33_, 2, v_v_37_);
lean_ctor_set(v___x_33_, 1, v_k_36_);
lean_ctor_set(v___x_33_, 0, v___x_48_);
v___x_57_ = v___x_33_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_k_36_);
lean_ctor_set(v_reuseFailAlloc_58_, 2, v_v_37_);
lean_ctor_set(v_reuseFailAlloc_58_, 3, v___y_50_);
lean_ctor_set(v_reuseFailAlloc_58_, 4, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_nat_add(v___x_47_, v___y_61_);
lean_dec(v___y_61_);
lean_dec(v___x_47_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_38_);
lean_ctor_set(v___x_10_, 0, v___x_62_);
v___x_64_ = v___x_10_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_68_, 4, v_l_38_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_nat_add(v___x_17_, v_size_40_);
if (lean_obj_tag(v_r_39_) == 0)
{
lean_object* v_size_66_; 
v_size_66_ = lean_ctor_get(v_r_39_, 0);
lean_inc(v_size_66_);
v___y_50_ = v___x_64_;
v___y_51_ = v___x_65_;
v___y_52_ = v_size_66_;
goto v___jp_49_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___y_50_ = v___x_64_;
v___y_51_ = v___x_65_;
v___y_52_ = v___x_67_;
goto v___jp_49_;
}
}
}
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
lean_del_object(v___x_10_);
v___x_77_ = lean_nat_add(v___x_17_, v_size_18_);
v___x_78_ = lean_nat_add(v___x_77_, v_size_19_);
lean_dec(v_size_19_);
v___x_79_ = lean_nat_add(v___x_77_, v_size_35_);
lean_dec(v___x_77_);
lean_inc_ref(v_l_7_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 4, v_l_22_);
lean_ctor_set(v___x_33_, 3, v_l_7_);
lean_ctor_set(v___x_33_, 2, v_v_6_);
lean_ctor_set(v___x_33_, 1, v_k_5_);
lean_ctor_set(v___x_33_, 0, v___x_79_);
v___x_81_ = v___x_33_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v_l_22_);
v___x_81_ = v_reuseFailAlloc_94_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v_l_7_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; lean_object* v_unused_90_; lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; 
v_unused_89_ = lean_ctor_get(v_l_7_, 4);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_l_7_, 3);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_l_7_, 2);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_l_7_, 1);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_l_7_, 0);
lean_dec(v_unused_93_);
v___x_83_ = v_l_7_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_l_7_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 4, v_r_23_);
lean_ctor_set(v___x_83_, 3, v___x_81_);
lean_ctor_set(v___x_83_, 2, v_v_21_);
lean_ctor_set(v___x_83_, 1, v_k_20_);
lean_ctor_set(v___x_83_, 0, v___x_78_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_k_20_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_v_21_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_87_, 4, v_r_23_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_101_; 
v_l_101_ = lean_ctor_get(v_impl_16_, 3);
lean_inc(v_l_101_);
if (lean_obj_tag(v_l_101_) == 0)
{
lean_object* v_r_102_; lean_object* v_k_103_; lean_object* v_v_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_127_; 
v_r_102_ = lean_ctor_get(v_impl_16_, 4);
v_k_103_ = lean_ctor_get(v_impl_16_, 1);
v_v_104_ = lean_ctor_get(v_impl_16_, 2);
v_isSharedCheck_127_ = !lean_is_exclusive(v_impl_16_);
if (v_isSharedCheck_127_ == 0)
{
lean_object* v_unused_128_; lean_object* v_unused_129_; 
v_unused_128_ = lean_ctor_get(v_impl_16_, 3);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_impl_16_, 0);
lean_dec(v_unused_129_);
v___x_106_ = v_impl_16_;
v_isShared_107_ = v_isSharedCheck_127_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_r_102_);
lean_inc(v_v_104_);
lean_inc(v_k_103_);
lean_dec(v_impl_16_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_127_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_k_108_; lean_object* v_v_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_123_; 
v_k_108_ = lean_ctor_get(v_l_101_, 1);
v_v_109_ = lean_ctor_get(v_l_101_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_l_101_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; lean_object* v_unused_126_; 
v_unused_124_ = lean_ctor_get(v_l_101_, 4);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_l_101_, 3);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_l_101_, 0);
lean_dec(v_unused_126_);
v___x_111_ = v_l_101_;
v_isShared_112_ = v_isSharedCheck_123_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_v_109_);
lean_inc(v_k_108_);
lean_dec(v_l_101_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_123_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_102_, 2);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_r_102_);
lean_ctor_set(v___x_111_, 3, v_r_102_);
lean_ctor_set(v___x_111_, 2, v_v_6_);
lean_ctor_set(v___x_111_, 1, v_k_5_);
lean_ctor_set(v___x_111_, 0, v___x_17_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_122_, 4, v_r_102_);
v___x_115_ = v_reuseFailAlloc_122_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
lean_inc(v_r_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 3, v_r_102_);
lean_ctor_set(v___x_106_, 0, v___x_17_);
v___x_117_ = v___x_106_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_121_, 4, v_r_102_);
v___x_117_ = v_reuseFailAlloc_121_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_117_);
lean_ctor_set(v___x_10_, 3, v___x_115_);
lean_ctor_set(v___x_10_, 2, v_v_109_);
lean_ctor_set(v___x_10_, 1, v_k_108_);
lean_ctor_set(v___x_10_, 0, v___x_113_);
v___x_119_ = v___x_10_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_120_, 4, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
else
{
lean_object* v_r_130_; 
v_r_130_ = lean_ctor_get(v_impl_16_, 4);
lean_inc(v_r_130_);
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_k_131_; lean_object* v_v_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_k_131_ = lean_ctor_get(v_impl_16_, 1);
v_v_132_ = lean_ctor_get(v_impl_16_, 2);
v_isSharedCheck_143_ = !lean_is_exclusive(v_impl_16_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_144_ = lean_ctor_get(v_impl_16_, 4);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_impl_16_, 3);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_impl_16_, 0);
lean_dec(v_unused_146_);
v___x_134_ = v_impl_16_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_v_132_);
lean_inc(v_k_131_);
lean_dec(v_impl_16_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(3u);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 4, v_l_101_);
lean_ctor_set(v___x_134_, 2, v_v_6_);
lean_ctor_set(v___x_134_, 1, v_k_5_);
lean_ctor_set(v___x_134_, 0, v___x_17_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_l_101_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_130_);
lean_ctor_set(v___x_10_, 3, v___x_138_);
lean_ctor_set(v___x_10_, 2, v_v_132_);
lean_ctor_set(v___x_10_, 1, v_k_131_);
lean_ctor_set(v___x_10_, 0, v___x_136_);
v___x_140_ = v___x_10_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_131_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_132_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_r_130_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_16_);
lean_ctor_set(v___x_10_, 3, v_r_130_);
lean_ctor_set(v___x_10_, 0, v___x_147_);
v___x_149_ = v___x_10_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_r_130_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_impl_16_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_153_; 
lean_dec(v_v_6_);
lean_dec(v_k_5_);
v___x_151_ = lean_box_uint64(v_k_1_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 2, v_v_2_);
lean_ctor_set(v___x_10_, 1, v___x_151_);
v___x_153_ = v___x_10_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_size_4_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_2_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_r_8_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_impl_155_; lean_object* v___x_156_; 
lean_dec(v_size_4_);
v_impl_155_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1_, v_v_2_, v_l_7_);
v___x_156_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_8_) == 0)
{
lean_object* v_size_157_; lean_object* v_size_158_; lean_object* v_k_159_; lean_object* v_v_160_; lean_object* v_l_161_; lean_object* v_r_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_size_157_ = lean_ctor_get(v_r_8_, 0);
v_size_158_ = lean_ctor_get(v_impl_155_, 0);
v_k_159_ = lean_ctor_get(v_impl_155_, 1);
v_v_160_ = lean_ctor_get(v_impl_155_, 2);
v_l_161_ = lean_ctor_get(v_impl_155_, 3);
v_r_162_ = lean_ctor_get(v_impl_155_, 4);
lean_inc(v_r_162_);
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = lean_nat_mul(v___x_163_, v_size_157_);
v___x_165_ = lean_nat_dec_lt(v___x_164_, v_size_158_);
lean_dec(v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
lean_dec(v_r_162_);
v___x_166_ = lean_nat_add(v___x_156_, v_size_158_);
v___x_167_ = lean_nat_add(v___x_166_, v_size_157_);
lean_dec(v___x_166_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v_impl_155_);
lean_ctor_set(v___x_10_, 0, v___x_167_);
v___x_169_ = v___x_10_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_impl_155_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v_r_8_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_236_; 
lean_inc(v_l_161_);
lean_inc(v_v_160_);
lean_inc(v_k_159_);
lean_inc(v_size_158_);
v_isSharedCheck_236_ = !lean_is_exclusive(v_impl_155_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_237_ = lean_ctor_get(v_impl_155_, 4);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_155_, 3);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_impl_155_, 2);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_impl_155_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_impl_155_, 0);
lean_dec(v_unused_241_);
v___x_172_ = v_impl_155_;
v_isShared_173_ = v_isSharedCheck_236_;
goto v_resetjp_171_;
}
else
{
lean_dec(v_impl_155_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_236_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_size_174_; lean_object* v_size_175_; lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_l_178_; lean_object* v_r_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_size_174_ = lean_ctor_get(v_l_161_, 0);
v_size_175_ = lean_ctor_get(v_r_162_, 0);
v_k_176_ = lean_ctor_get(v_r_162_, 1);
v_v_177_ = lean_ctor_get(v_r_162_, 2);
v_l_178_ = lean_ctor_get(v_r_162_, 3);
v_r_179_ = lean_ctor_get(v_r_162_, 4);
v___x_180_ = lean_unsigned_to_nat(2u);
v___x_181_ = lean_nat_mul(v___x_180_, v_size_174_);
v___x_182_ = lean_nat_dec_lt(v_size_175_, v___x_181_);
lean_dec(v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_211_; 
lean_inc(v_r_179_);
lean_inc(v_l_178_);
lean_inc(v_v_177_);
lean_inc(v_k_176_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_r_162_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_212_ = lean_ctor_get(v_r_162_, 4);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_r_162_, 3);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_r_162_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_r_162_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_r_162_, 0);
lean_dec(v_unused_216_);
v___x_184_ = v_r_162_;
v_isShared_185_ = v_isSharedCheck_211_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_r_162_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_211_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___x_199_; lean_object* v___y_201_; 
v___x_186_ = lean_nat_add(v___x_156_, v_size_158_);
lean_dec(v_size_158_);
v___x_187_ = lean_nat_add(v___x_186_, v_size_157_);
lean_dec(v___x_186_);
v___x_199_ = lean_nat_add(v___x_156_, v_size_174_);
if (lean_obj_tag(v_l_178_) == 0)
{
lean_object* v_size_209_; 
v_size_209_ = lean_ctor_get(v_l_178_, 0);
lean_inc(v_size_209_);
v___y_201_ = v_size_209_;
goto v___jp_200_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___y_201_ = v___x_210_;
goto v___jp_200_;
}
v___jp_188_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_nat_add(v___y_189_, v___y_191_);
lean_dec(v___y_191_);
lean_dec(v___y_189_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 4, v_r_8_);
lean_ctor_set(v___x_184_, 3, v_r_179_);
lean_ctor_set(v___x_184_, 2, v_v_6_);
lean_ctor_set(v___x_184_, 1, v_k_5_);
lean_ctor_set(v___x_184_, 0, v___x_192_);
v___x_194_ = v___x_184_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_r_179_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_r_8_);
v___x_194_ = v_reuseFailAlloc_198_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v___x_194_);
lean_ctor_set(v___x_172_, 3, v___y_190_);
lean_ctor_set(v___x_172_, 2, v_v_177_);
lean_ctor_set(v___x_172_, 1, v_k_176_);
lean_ctor_set(v___x_172_, 0, v___x_187_);
v___x_196_ = v___x_172_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_k_176_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_v_177_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___y_190_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_nat_add(v___x_199_, v___y_201_);
lean_dec(v___y_201_);
lean_dec(v___x_199_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_178_);
lean_ctor_set(v___x_10_, 3, v_l_161_);
lean_ctor_set(v___x_10_, 2, v_v_160_);
lean_ctor_set(v___x_10_, 1, v_k_159_);
lean_ctor_set(v___x_10_, 0, v___x_202_);
v___x_204_ = v___x_10_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_159_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_160_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_l_161_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_l_178_);
v___x_204_ = v_reuseFailAlloc_208_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_nat_add(v___x_156_, v_size_157_);
if (lean_obj_tag(v_r_179_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_r_179_, 0);
lean_inc(v_size_206_);
v___y_189_ = v___x_205_;
v___y_190_ = v___x_204_;
v___y_191_ = v_size_206_;
goto v___jp_188_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_189_ = v___x_205_;
v___y_190_ = v___x_204_;
v___y_191_ = v___x_207_;
goto v___jp_188_;
}
}
}
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_del_object(v___x_10_);
v___x_217_ = lean_nat_add(v___x_156_, v_size_158_);
lean_dec(v_size_158_);
v___x_218_ = lean_nat_add(v___x_217_, v_size_157_);
lean_dec(v___x_217_);
v___x_219_ = lean_nat_add(v___x_156_, v_size_157_);
v___x_220_ = lean_nat_add(v___x_219_, v_size_175_);
lean_dec(v___x_219_);
lean_inc_ref(v_r_8_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v_r_8_);
lean_ctor_set(v___x_172_, 3, v_r_162_);
lean_ctor_set(v___x_172_, 2, v_v_6_);
lean_ctor_set(v___x_172_, 1, v_k_5_);
lean_ctor_set(v___x_172_, 0, v___x_220_);
v___x_222_ = v___x_172_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_r_162_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_r_8_);
v___x_222_ = v_reuseFailAlloc_235_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v_r_8_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_230_ = lean_ctor_get(v_r_8_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_r_8_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_r_8_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_r_8_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_r_8_, 0);
lean_dec(v_unused_234_);
v___x_224_ = v_r_8_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_r_8_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 4, v___x_222_);
lean_ctor_set(v___x_224_, 3, v_l_161_);
lean_ctor_set(v___x_224_, 2, v_v_160_);
lean_ctor_set(v___x_224_, 1, v_k_159_);
lean_ctor_set(v___x_224_, 0, v___x_218_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_159_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_160_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_l_161_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v___x_222_);
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
}
}
else
{
lean_object* v_l_242_; 
v_l_242_ = lean_ctor_get(v_impl_155_, 3);
if (lean_obj_tag(v_l_242_) == 0)
{
lean_object* v_r_243_; lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_l_242_);
v_r_243_ = lean_ctor_get(v_impl_155_, 4);
v_k_244_ = lean_ctor_get(v_impl_155_, 1);
v_v_245_ = lean_ctor_get(v_impl_155_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v_impl_155_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_257_ = lean_ctor_get(v_impl_155_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_impl_155_, 0);
lean_dec(v_unused_258_);
v___x_247_ = v_impl_155_;
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_r_243_);
lean_inc(v_v_245_);
lean_inc(v_k_244_);
lean_dec(v_impl_155_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 3, v_r_243_);
lean_ctor_set(v___x_247_, 2, v_v_6_);
lean_ctor_set(v___x_247_, 1, v_k_5_);
lean_ctor_set(v___x_247_, 0, v___x_156_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_243_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_251_);
lean_ctor_set(v___x_10_, 3, v_l_242_);
lean_ctor_set(v___x_10_, 2, v_v_245_);
lean_ctor_set(v___x_10_, 1, v_k_244_);
lean_ctor_set(v___x_10_, 0, v___x_249_);
v___x_253_ = v___x_10_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_244_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_245_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_r_259_; 
v_r_259_ = lean_ctor_get(v_impl_155_, 4);
lean_inc(v_r_259_);
if (lean_obj_tag(v_r_259_) == 0)
{
lean_object* v_k_260_; lean_object* v_v_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_284_; 
lean_inc(v_l_242_);
v_k_260_ = lean_ctor_get(v_impl_155_, 1);
v_v_261_ = lean_ctor_get(v_impl_155_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_impl_155_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_impl_155_, 4);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_impl_155_, 3);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_impl_155_, 0);
lean_dec(v_unused_287_);
v___x_263_ = v_impl_155_;
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_v_261_);
lean_inc(v_k_260_);
lean_dec(v_impl_155_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_280_; 
v_k_265_ = lean_ctor_get(v_r_259_, 1);
v_v_266_ = lean_ctor_get(v_r_259_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_r_259_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_r_259_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_r_259_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_r_259_, 0);
lean_dec(v_unused_283_);
v___x_268_ = v_r_259_;
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_dec(v_r_259_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(3u);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_l_242_);
lean_ctor_set(v___x_268_, 3, v_l_242_);
lean_ctor_set(v___x_268_, 2, v_v_261_);
lean_ctor_set(v___x_268_, 1, v_k_260_);
lean_ctor_set(v___x_268_, 0, v___x_156_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_l_242_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_l_242_);
v___x_272_ = v_reuseFailAlloc_279_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 4, v_l_242_);
lean_ctor_set(v___x_263_, 2, v_v_6_);
lean_ctor_set(v___x_263_, 1, v_k_5_);
lean_ctor_set(v___x_263_, 0, v___x_156_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_l_242_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_l_242_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_274_);
lean_ctor_set(v___x_10_, 3, v___x_272_);
lean_ctor_set(v___x_10_, 2, v_v_266_);
lean_ctor_set(v___x_10_, 1, v_k_265_);
lean_ctor_set(v___x_10_, 0, v___x_270_);
v___x_276_ = v___x_10_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_259_);
lean_ctor_set(v___x_10_, 3, v_impl_155_);
lean_ctor_set(v___x_10_, 0, v___x_288_);
v___x_290_ = v___x_10_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_impl_155_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_r_259_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_box_uint64(v_k_1_);
v___x_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v_v_2_);
lean_ctor_set(v___x_295_, 3, v_t_3_);
lean_ctor_set(v___x_295_, 4, v_t_3_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object* v_k_296_, lean_object* v_v_297_, lean_object* v_t_298_){
_start:
{
uint64_t v_k_boxed_299_; lean_object* v_res_300_; 
v_k_boxed_299_ = lean_unbox_uint64(v_k_296_);
lean_dec_ref(v_k_296_);
v_res_300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_boxed_299_, v_v_297_, v_t_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new(){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint64_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint64_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_302_ = l_Std_CancellationToken_new();
v___x_303_ = lean_box(1);
v___x_304_ = 0ULL;
lean_inc_ref(v___x_302_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
v___x_306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v___x_304_, v___x_305_, v___x_303_);
v___x_307_ = 1ULL;
v___x_308_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint64(v___x_308_, sizeof(void*)*1, v___x_307_);
v___x_309_ = l_Std_Mutex_new___redArg(v___x_308_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_302_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set_uint64(v___x_311_, sizeof(void*)*3, v___x_304_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_CancellationContext_new();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object* v_00_u03b2_314_, uint64_t v_k_315_, lean_object* v_v_316_, lean_object* v_t_317_, lean_object* v_hl_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_315_, v_v_316_, v_t_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_k_321_, lean_object* v_v_322_, lean_object* v_t_323_, lean_object* v_hl_324_){
_start:
{
uint64_t v_k_boxed_325_; lean_object* v_res_326_; 
v_k_boxed_325_ = lean_unbox_uint64(v_k_321_);
lean_dec_ref(v_k_321_);
v_res_326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(v_00_u03b2_320_, v_k_boxed_325_, v_v_322_, v_t_323_, v_hl_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(lean_object* v_mutex_327_, lean_object* v_k_328_){
_start:
{
lean_object* v_ref_330_; lean_object* v_mutex_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_ref_330_ = lean_ctor_get(v_mutex_327_, 0);
lean_inc(v_ref_330_);
v_mutex_331_ = lean_ctor_get(v_mutex_327_, 1);
lean_inc(v_mutex_331_);
lean_dec_ref(v_mutex_327_);
v___x_332_ = lean_io_basemutex_lock(v_mutex_331_);
v___x_333_ = lean_apply_2(v_k_328_, v_ref_330_, lean_box(0));
v___x_334_ = lean_io_basemutex_unlock(v_mutex_331_);
lean_dec(v_mutex_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg___boxed(lean_object* v_mutex_335_, lean_object* v_k_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(v_mutex_335_, v_k_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_mutex_341_, lean_object* v_k_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(v_mutex_341_, v_k_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___boxed(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_mutex_347_, lean_object* v_k_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2(v_00_u03b1_345_, v_00_u03b2_346_, v_mutex_347_, v_k_348_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg(uint64_t v_k_351_, lean_object* v_t_352_){
_start:
{
if (lean_obj_tag(v_t_352_) == 0)
{
lean_object* v_k_353_; lean_object* v_l_354_; lean_object* v_r_355_; uint64_t v___x_356_; uint8_t v___x_357_; 
v_k_353_ = lean_ctor_get(v_t_352_, 1);
v_l_354_ = lean_ctor_get(v_t_352_, 3);
v_r_355_ = lean_ctor_get(v_t_352_, 4);
v___x_356_ = lean_unbox_uint64(v_k_353_);
v___x_357_ = lean_uint64_dec_lt(v_k_351_, v___x_356_);
if (v___x_357_ == 0)
{
uint64_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_unbox_uint64(v_k_353_);
v___x_359_ = lean_uint64_dec_eq(v_k_351_, v___x_358_);
if (v___x_359_ == 0)
{
v_t_352_ = v_r_355_;
goto _start;
}
else
{
return v___x_359_;
}
}
else
{
v_t_352_ = v_l_354_;
goto _start;
}
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg___boxed(lean_object* v_k_363_, lean_object* v_t_364_){
_start:
{
uint64_t v_k_boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v_k_boxed_365_ = lean_unbox_uint64(v_k_363_);
lean_dec_ref(v_k_363_);
v_res_366_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg(v_k_boxed_365_, v_t_364_);
lean_dec(v_t_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1(uint64_t v___x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg(v___x_368_, v_x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
v___x_372_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v___x_368_, v___x_371_, v_x_369_);
return v___x_372_;
}
else
{
return v_x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1___boxed(lean_object* v___x_373_, lean_object* v_x_374_){
_start:
{
uint64_t v___x_1603__boxed_375_; lean_object* v_res_376_; 
v___x_1603__boxed_375_ = lean_unbox_uint64(v___x_373_);
lean_dec_ref(v___x_373_);
v_res_376_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1(v___x_1603__boxed_375_, v_x_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0(lean_object* v_x_377_){
_start:
{
lean_inc_ref(v_x_377_);
return v_x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0___boxed(lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__0(v_x_378_);
lean_dec_ref(v_x_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(uint64_t v___x_381_, uint64_t v_k_382_, lean_object* v_t_383_){
_start:
{
if (lean_obj_tag(v_t_383_) == 0)
{
lean_object* v_size_384_; lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v_l_387_; lean_object* v_r_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_412_; 
v_size_384_ = lean_ctor_get(v_t_383_, 0);
v_k_385_ = lean_ctor_get(v_t_383_, 1);
v_v_386_ = lean_ctor_get(v_t_383_, 2);
v_l_387_ = lean_ctor_get(v_t_383_, 3);
v_r_388_ = lean_ctor_get(v_t_383_, 4);
v_isSharedCheck_412_ = !lean_is_exclusive(v_t_383_);
if (v_isSharedCheck_412_ == 0)
{
v___x_390_ = v_t_383_;
v_isShared_391_ = v_isSharedCheck_412_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_r_388_);
lean_inc(v_l_387_);
lean_inc(v_v_386_);
lean_inc(v_k_385_);
lean_inc(v_size_384_);
lean_dec(v_t_383_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_412_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint64_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unbox_uint64(v_k_385_);
v___x_393_ = lean_uint64_dec_lt(v_k_382_, v___x_392_);
if (v___x_393_ == 0)
{
uint64_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_unbox_uint64(v_k_385_);
v___x_395_ = lean_uint64_dec_eq(v_k_382_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(v___x_381_, v_k_382_, v_r_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v___x_396_);
v___x_398_ = v___x_390_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_size_384_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_l_387_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___f_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
lean_dec(v_k_385_);
v___f_400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___closed__0));
v___x_401_ = lean_box_uint64(v___x_381_);
v___f_402_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_402_, 0, v___x_401_);
v___x_403_ = l_Prod_map___redArg(v___f_400_, v___f_402_, v_v_386_);
v___x_404_ = lean_box_uint64(v_k_382_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v___x_403_);
lean_ctor_set(v___x_390_, 1, v___x_404_);
v___x_406_ = v___x_390_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_size_384_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_l_387_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_r_388_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(v___x_381_, v_k_382_, v_l_387_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 3, v___x_408_);
v___x_410_ = v___x_390_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_size_384_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_r_388_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
return v_t_383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object* v___x_413_, lean_object* v_k_414_, lean_object* v_t_415_){
_start:
{
uint64_t v___x_1620__boxed_416_; uint64_t v_k_boxed_417_; lean_object* v_res_418_; 
v___x_1620__boxed_416_ = lean_unbox_uint64(v___x_413_);
lean_dec_ref(v___x_413_);
v_k_boxed_417_ = lean_unbox_uint64(v_k_414_);
lean_dec_ref(v_k_414_);
v_res_418_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(v___x_1620__boxed_416_, v_k_boxed_417_, v_t_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object* v_token_419_, uint64_t v_id_420_, lean_object* v_state_421_, lean_object* v_root_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Std_CancellationToken_isCancelled(v_token_419_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_tokens_428_; uint64_t v_id_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_446_; 
v___x_426_ = l_Std_CancellationToken_new();
v___x_427_ = lean_st_ref_get(v___y_423_);
v_tokens_428_ = lean_ctor_get(v___x_427_, 0);
v_id_429_ = lean_ctor_get_uint64(v___x_427_, sizeof(void*)*1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_446_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_tokens_428_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; lean_object* v___x_440_; 
v___x_433_ = lean_box(1);
lean_inc_ref(v___x_426_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_426_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_429_, v___x_434_, v_tokens_428_);
v___x_436_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1(v_id_429_, v_id_420_, v___x_435_);
v___x_437_ = 1ULL;
v___x_438_ = lean_uint64_add(v_id_429_, v___x_437_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_436_);
v___x_440_ = v___x_431_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_436_);
v___x_440_ = v_reuseFailAlloc_445_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_ctor_set_uint64(v___x_440_, sizeof(void*)*1, v___x_438_);
v___x_441_ = lean_st_ref_swap(v___y_423_, v___x_440_);
lean_dec(v___x_441_);
v___x_442_ = lean_box_uint64(v_id_420_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_444_, 0, v_state_421_);
lean_ctor_set(v___x_444_, 1, v___x_426_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set_uint64(v___x_444_, sizeof(void*)*3, v_id_429_);
return v___x_444_;
}
}
}
else
{
lean_dec_ref(v_state_421_);
lean_inc_ref(v_root_422_);
return v_root_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object* v_token_447_, lean_object* v_id_448_, lean_object* v_state_449_, lean_object* v_root_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint64_t v_id_boxed_453_; lean_object* v_res_454_; 
v_id_boxed_453_ = lean_unbox_uint64(v_id_448_);
lean_dec_ref(v_id_448_);
v_res_454_ = l_Std_CancellationContext_fork___lam__0(v_token_447_, v_id_boxed_453_, v_state_449_, v_root_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v_root_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object* v_root_455_){
_start:
{
lean_object* v_state_457_; lean_object* v_token_458_; uint64_t v_id_459_; lean_object* v___x_460_; lean_object* v___f_461_; lean_object* v___x_462_; 
v_state_457_ = lean_ctor_get(v_root_455_, 0);
lean_inc_ref_n(v_state_457_, 2);
v_token_458_ = lean_ctor_get(v_root_455_, 1);
lean_inc_ref(v_token_458_);
v_id_459_ = lean_ctor_get_uint64(v_root_455_, sizeof(void*)*3);
v___x_460_ = lean_box_uint64(v_id_459_);
v___f_461_ = lean_alloc_closure((void*)(l_Std_CancellationContext_fork___lam__0___boxed), 6, 4);
lean_closure_set(v___f_461_, 0, v_token_458_);
lean_closure_set(v___f_461_, 1, v___x_460_);
lean_closure_set(v___f_461_, 2, v_state_457_);
lean_closure_set(v___f_461_, 3, v_root_455_);
v___x_462_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(v_state_457_, v___f_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object* v_root_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_CancellationContext_fork(v_root_463_);
return v_res_465_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0(lean_object* v_00_u03b2_466_, uint64_t v_k_467_, lean_object* v_t_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___redArg(v_k_467_, v_t_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object* v_00_u03b2_470_, lean_object* v_k_471_, lean_object* v_t_472_){
_start:
{
uint64_t v_k_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v_k_boxed_473_ = lean_unbox_uint64(v_k_471_);
lean_dec_ref(v_k_471_);
v_res_474_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_CancellationContext_fork_spec__0(v_00_u03b2_470_, v_k_boxed_473_, v_t_472_);
lean_dec(v_t_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(uint64_t v_k_476_, lean_object* v_t_477_){
_start:
{
if (lean_obj_tag(v_t_477_) == 0)
{
lean_object* v_k_478_; lean_object* v_v_479_; lean_object* v_l_480_; lean_object* v_r_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_1138_; 
v_k_478_ = lean_ctor_get(v_t_477_, 1);
v_v_479_ = lean_ctor_get(v_t_477_, 2);
v_l_480_ = lean_ctor_get(v_t_477_, 3);
v_r_481_ = lean_ctor_get(v_t_477_, 4);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_t_477_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_t_477_, 0);
lean_dec(v_unused_1139_);
v___x_483_ = v_t_477_;
v_isShared_484_ = v_isSharedCheck_1138_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_r_481_);
lean_inc(v_l_480_);
lean_inc(v_v_479_);
lean_inc(v_k_478_);
lean_dec(v_t_477_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_1138_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint64_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unbox_uint64(v_k_478_);
v___x_486_ = lean_uint64_dec_lt(v_k_476_, v___x_485_);
if (v___x_486_ == 0)
{
uint64_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_unbox_uint64(v_k_478_);
v___x_488_ = lean_uint64_dec_eq(v_k_476_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v_impl_489_; lean_object* v___x_490_; 
v_impl_489_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v_k_476_, v_r_481_);
v___x_490_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_489_) == 0)
{
if (lean_obj_tag(v_l_480_) == 0)
{
lean_object* v_size_491_; lean_object* v_size_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_l_495_; lean_object* v_r_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_size_491_ = lean_ctor_get(v_impl_489_, 0);
v_size_492_ = lean_ctor_get(v_l_480_, 0);
v_k_493_ = lean_ctor_get(v_l_480_, 1);
v_v_494_ = lean_ctor_get(v_l_480_, 2);
v_l_495_ = lean_ctor_get(v_l_480_, 3);
v_r_496_ = lean_ctor_get(v_l_480_, 4);
lean_inc(v_r_496_);
v___x_497_ = lean_unsigned_to_nat(3u);
v___x_498_ = lean_nat_mul(v___x_497_, v_size_491_);
v___x_499_ = lean_nat_dec_lt(v___x_498_, v_size_492_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec(v_r_496_);
v___x_500_ = lean_nat_add(v___x_490_, v_size_492_);
v___x_501_ = lean_nat_add(v___x_500_, v_size_491_);
lean_dec(v___x_500_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_impl_489_);
lean_ctor_set(v___x_483_, 0, v___x_501_);
v___x_503_ = v___x_483_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_impl_489_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_l_495_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_inc(v_size_492_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_480_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_l_480_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_575_);
v___x_506_ = v_l_480_;
v_isShared_507_ = v_isSharedCheck_570_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_l_480_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_570_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_size_508_; lean_object* v_size_509_; lean_object* v_k_510_; lean_object* v_v_511_; lean_object* v_l_512_; lean_object* v_r_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_size_508_ = lean_ctor_get(v_l_495_, 0);
v_size_509_ = lean_ctor_get(v_r_496_, 0);
v_k_510_ = lean_ctor_get(v_r_496_, 1);
v_v_511_ = lean_ctor_get(v_r_496_, 2);
v_l_512_ = lean_ctor_get(v_r_496_, 3);
v_r_513_ = lean_ctor_get(v_r_496_, 4);
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = lean_nat_mul(v___x_514_, v_size_508_);
v___x_516_ = lean_nat_dec_lt(v_size_509_, v___x_515_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_545_; 
lean_inc(v_r_513_);
lean_inc(v_l_512_);
lean_inc(v_v_511_);
lean_inc(v_k_510_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_r_496_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_546_ = lean_ctor_get(v_r_496_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_r_496_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_r_496_, 2);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_r_496_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_r_496_, 0);
lean_dec(v_unused_550_);
v___x_518_ = v_r_496_;
v_isShared_519_ = v_isSharedCheck_545_;
goto v_resetjp_517_;
}
else
{
lean_dec(v_r_496_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_545_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___x_533_; lean_object* v___y_535_; 
v___x_520_ = lean_nat_add(v___x_490_, v_size_492_);
lean_dec(v_size_492_);
v___x_521_ = lean_nat_add(v___x_520_, v_size_491_);
lean_dec(v___x_520_);
v___x_533_ = lean_nat_add(v___x_490_, v_size_508_);
if (lean_obj_tag(v_l_512_) == 0)
{
lean_object* v_size_543_; 
v_size_543_ = lean_ctor_get(v_l_512_, 0);
lean_inc(v_size_543_);
v___y_535_ = v_size_543_;
goto v___jp_534_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___y_535_ = v___x_544_;
goto v___jp_534_;
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_nat_add(v___y_523_, v___y_525_);
lean_dec(v___y_525_);
lean_dec(v___y_523_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 4, v_impl_489_);
lean_ctor_set(v___x_518_, 3, v_r_513_);
lean_ctor_set(v___x_518_, 2, v_v_479_);
lean_ctor_set(v___x_518_, 1, v_k_478_);
lean_ctor_set(v___x_518_, 0, v___x_526_);
v___x_528_ = v___x_518_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_r_513_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_impl_489_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_528_);
lean_ctor_set(v___x_506_, 3, v___y_524_);
lean_ctor_set(v___x_506_, 2, v_v_511_);
lean_ctor_set(v___x_506_, 1, v_k_510_);
lean_ctor_set(v___x_506_, 0, v___x_521_);
v___x_530_ = v___x_506_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_k_510_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_v_511_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v___y_524_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_nat_add(v___x_533_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v___x_533_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_l_512_);
lean_ctor_set(v___x_483_, 3, v_l_495_);
lean_ctor_set(v___x_483_, 2, v_v_494_);
lean_ctor_set(v___x_483_, 1, v_k_493_);
lean_ctor_set(v___x_483_, 0, v___x_536_);
v___x_538_ = v___x_483_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_l_495_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_l_512_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_nat_add(v___x_490_, v_size_491_);
if (lean_obj_tag(v_r_513_) == 0)
{
lean_object* v_size_540_; 
v_size_540_ = lean_ctor_get(v_r_513_, 0);
lean_inc(v_size_540_);
v___y_523_ = v___x_539_;
v___y_524_ = v___x_538_;
v___y_525_ = v_size_540_;
goto v___jp_522_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___y_523_ = v___x_539_;
v___y_524_ = v___x_538_;
v___y_525_ = v___x_541_;
goto v___jp_522_;
}
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_del_object(v___x_483_);
v___x_551_ = lean_nat_add(v___x_490_, v_size_492_);
lean_dec(v_size_492_);
v___x_552_ = lean_nat_add(v___x_551_, v_size_491_);
lean_dec(v___x_551_);
v___x_553_ = lean_nat_add(v___x_490_, v_size_491_);
v___x_554_ = lean_nat_add(v___x_553_, v_size_509_);
lean_dec(v___x_553_);
lean_inc_ref(v_impl_489_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_impl_489_);
lean_ctor_set(v___x_506_, 3, v_r_496_);
lean_ctor_set(v___x_506_, 2, v_v_479_);
lean_ctor_set(v___x_506_, 1, v_k_478_);
lean_ctor_set(v___x_506_, 0, v___x_554_);
v___x_556_ = v___x_506_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_impl_489_);
v___x_556_ = v_reuseFailAlloc_569_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v_impl_489_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_564_ = lean_ctor_get(v_impl_489_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_impl_489_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_impl_489_, 2);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_impl_489_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_impl_489_, 0);
lean_dec(v_unused_568_);
v___x_558_ = v_impl_489_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_dec(v_impl_489_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_556_);
lean_ctor_set(v___x_558_, 3, v_l_495_);
lean_ctor_set(v___x_558_, 2, v_v_494_);
lean_ctor_set(v___x_558_, 1, v_k_493_);
lean_ctor_set(v___x_558_, 0, v___x_552_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_l_495_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v___x_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v_size_576_ = lean_ctor_get(v_impl_489_, 0);
v___x_577_ = lean_nat_add(v___x_490_, v_size_576_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_impl_489_);
lean_ctor_set(v___x_483_, 0, v___x_577_);
v___x_579_ = v___x_483_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_impl_489_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
if (lean_obj_tag(v_l_480_) == 0)
{
lean_object* v_l_581_; 
v_l_581_ = lean_ctor_get(v_l_480_, 3);
if (lean_obj_tag(v_l_581_) == 0)
{
lean_object* v_r_582_; 
lean_inc_ref(v_l_581_);
v_r_582_ = lean_ctor_get(v_l_480_, 4);
lean_inc(v_r_582_);
if (lean_obj_tag(v_r_582_) == 0)
{
lean_object* v_size_583_; lean_object* v_k_584_; lean_object* v_v_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_598_; 
v_size_583_ = lean_ctor_get(v_l_480_, 0);
v_k_584_ = lean_ctor_get(v_l_480_, 1);
v_v_585_ = lean_ctor_get(v_l_480_, 2);
v_isSharedCheck_598_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_599_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_600_);
v___x_587_ = v_l_480_;
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_v_585_);
lean_inc(v_k_584_);
lean_inc(v_size_583_);
lean_dec(v_l_480_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_size_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_size_589_ = lean_ctor_get(v_r_582_, 0);
v___x_590_ = lean_nat_add(v___x_490_, v_size_583_);
lean_dec(v_size_583_);
v___x_591_ = lean_nat_add(v___x_490_, v_size_589_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v_impl_489_);
lean_ctor_set(v___x_587_, 3, v_r_582_);
lean_ctor_set(v___x_587_, 2, v_v_479_);
lean_ctor_set(v___x_587_, 1, v_k_478_);
lean_ctor_set(v___x_587_, 0, v___x_591_);
v___x_593_ = v___x_587_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_r_582_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_impl_489_);
v___x_593_ = v_reuseFailAlloc_597_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v___x_593_);
lean_ctor_set(v___x_483_, 3, v_l_581_);
lean_ctor_set(v___x_483_, 2, v_v_585_);
lean_ctor_set(v___x_483_, 1, v_k_584_);
lean_ctor_set(v___x_483_, 0, v___x_590_);
v___x_595_ = v___x_483_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_l_581_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_k_601_ = lean_ctor_get(v_l_480_, 1);
v_v_602_ = lean_ctor_get(v_l_480_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_614_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_616_);
v___x_604_ = v_l_480_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_dec(v_l_480_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(3u);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 3, v_r_582_);
lean_ctor_set(v___x_604_, 2, v_v_479_);
lean_ctor_set(v___x_604_, 1, v_k_478_);
lean_ctor_set(v___x_604_, 0, v___x_490_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_r_582_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_r_582_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v___x_608_);
lean_ctor_set(v___x_483_, 3, v_l_581_);
lean_ctor_set(v___x_483_, 2, v_v_602_);
lean_ctor_set(v___x_483_, 1, v_k_601_);
lean_ctor_set(v___x_483_, 0, v___x_606_);
v___x_610_ = v___x_483_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_l_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
else
{
lean_object* v_r_617_; 
v_r_617_ = lean_ctor_get(v_l_480_, 4);
lean_inc(v_r_617_);
if (lean_obj_tag(v_r_617_) == 0)
{
lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_642_; 
lean_inc(v_l_581_);
v_k_618_ = lean_ctor_get(v_l_480_, 1);
v_v_619_ = lean_ctor_get(v_l_480_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_643_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_645_);
v___x_621_ = v_l_480_;
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_v_619_);
lean_inc(v_k_618_);
lean_dec(v_l_480_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_k_623_; lean_object* v_v_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_638_; 
v_k_623_ = lean_ctor_get(v_r_617_, 1);
v_v_624_ = lean_ctor_get(v_r_617_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_r_617_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_639_ = lean_ctor_get(v_r_617_, 4);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_617_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_617_, 0);
lean_dec(v_unused_641_);
v___x_626_ = v_r_617_;
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_v_624_);
lean_inc(v_k_623_);
lean_dec(v_r_617_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(3u);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_581_);
lean_ctor_set(v___x_626_, 3, v_l_581_);
lean_ctor_set(v___x_626_, 2, v_v_619_);
lean_ctor_set(v___x_626_, 1, v_k_618_);
lean_ctor_set(v___x_626_, 0, v___x_490_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_581_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_l_581_);
v___x_630_ = v_reuseFailAlloc_637_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v_l_581_);
lean_ctor_set(v___x_621_, 2, v_v_479_);
lean_ctor_set(v___x_621_, 1, v_k_478_);
lean_ctor_set(v___x_621_, 0, v___x_490_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_581_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_581_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v___x_632_);
lean_ctor_set(v___x_483_, 3, v___x_630_);
lean_ctor_set(v___x_483_, 2, v_v_624_);
lean_ctor_set(v___x_483_, 1, v_k_623_);
lean_ctor_set(v___x_483_, 0, v___x_628_);
v___x_634_ = v___x_483_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(2u);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_r_617_);
lean_ctor_set(v___x_483_, 0, v___x_646_);
v___x_648_ = v___x_483_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_r_617_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_651_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_l_480_);
lean_ctor_set(v___x_483_, 0, v___x_490_);
v___x_651_ = v___x_483_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_l_480_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_del_object(v___x_483_);
lean_dec(v_v_479_);
lean_dec(v_k_478_);
if (lean_obj_tag(v_l_480_) == 0)
{
if (lean_obj_tag(v_r_481_) == 0)
{
lean_object* v_size_653_; lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v_l_656_; lean_object* v_r_657_; lean_object* v_size_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_size_653_ = lean_ctor_get(v_l_480_, 0);
v_k_654_ = lean_ctor_get(v_l_480_, 1);
v_v_655_ = lean_ctor_get(v_l_480_, 2);
v_l_656_ = lean_ctor_get(v_l_480_, 3);
v_r_657_ = lean_ctor_get(v_l_480_, 4);
lean_inc(v_r_657_);
v_size_658_ = lean_ctor_get(v_r_481_, 0);
v_k_659_ = lean_ctor_get(v_r_481_, 1);
v_v_660_ = lean_ctor_get(v_r_481_, 2);
v_l_661_ = lean_ctor_get(v_r_481_, 3);
lean_inc(v_l_661_);
v_r_662_ = lean_ctor_get(v_r_481_, 4);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_dec_lt(v_size_653_, v_size_658_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_800_; 
lean_inc(v_l_656_);
lean_inc(v_v_655_);
lean_inc(v_k_654_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_801_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_l_480_, 2);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_l_480_, 1);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_805_);
v___x_666_ = v_l_480_;
v_isShared_667_ = v_isSharedCheck_800_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_l_480_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_800_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_tree_669_; 
v___x_668_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_654_, v_v_655_, v_l_656_, v_r_657_);
v_tree_669_ = lean_ctor_get(v___x_668_, 2);
if (lean_obj_tag(v_tree_669_) == 0)
{
lean_object* v_k_670_; lean_object* v_v_671_; lean_object* v_size_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
lean_inc_ref(v_tree_669_);
v_k_670_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_k_670_);
v_v_671_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_v_671_);
lean_dec_ref(v___x_668_);
v_size_672_ = lean_ctor_get(v_tree_669_, 0);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = lean_nat_mul(v___x_673_, v_size_672_);
v___x_675_ = lean_nat_dec_lt(v___x_674_, v_size_658_);
lean_dec(v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec(v_l_661_);
v___x_676_ = lean_nat_add(v___x_663_, v_size_672_);
v___x_677_ = lean_nat_add(v___x_676_, v_size_658_);
lean_dec(v___x_676_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_r_481_);
lean_ctor_set(v___x_666_, 3, v_tree_669_);
lean_ctor_set(v___x_666_, 2, v_v_671_);
lean_ctor_set(v___x_666_, 1, v_k_670_);
lean_ctor_set(v___x_666_, 0, v___x_677_);
v___x_679_ = v___x_666_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_670_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_671_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_tree_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_r_481_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_735_; 
lean_inc(v_r_662_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_inc(v_size_658_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_736_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_r_481_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_r_481_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_740_);
v___x_682_ = v_r_481_;
v_isShared_683_ = v_isSharedCheck_735_;
goto v_resetjp_681_;
}
else
{
lean_dec(v_r_481_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_735_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_size_684_; lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v_l_687_; lean_object* v_r_688_; lean_object* v_size_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_size_684_ = lean_ctor_get(v_l_661_, 0);
v_k_685_ = lean_ctor_get(v_l_661_, 1);
v_v_686_ = lean_ctor_get(v_l_661_, 2);
v_l_687_ = lean_ctor_get(v_l_661_, 3);
v_r_688_ = lean_ctor_get(v_l_661_, 4);
v_size_689_ = lean_ctor_get(v_r_662_, 0);
v___x_690_ = lean_unsigned_to_nat(2u);
v___x_691_ = lean_nat_mul(v___x_690_, v_size_689_);
v___x_692_ = lean_nat_dec_lt(v_size_684_, v___x_691_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_720_; 
lean_inc(v_r_688_);
lean_inc(v_l_687_);
lean_inc(v_v_686_);
lean_inc(v_k_685_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_l_661_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_721_ = lean_ctor_get(v_l_661_, 4);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_l_661_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_l_661_, 2);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_l_661_, 1);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_661_, 0);
lean_dec(v_unused_725_);
v___x_694_ = v_l_661_;
v_isShared_695_ = v_isSharedCheck_720_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_l_661_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_720_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_710_; 
v___x_696_ = lean_nat_add(v___x_663_, v_size_672_);
v___x_697_ = lean_nat_add(v___x_696_, v_size_658_);
lean_dec(v_size_658_);
if (lean_obj_tag(v_l_687_) == 0)
{
lean_object* v_size_718_; 
v_size_718_ = lean_ctor_get(v_l_687_, 0);
lean_inc(v_size_718_);
v___y_710_ = v_size_718_;
goto v___jp_709_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___y_710_ = v___x_719_;
goto v___jp_709_;
}
v___jp_698_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_nat_add(v___y_699_, v___y_701_);
lean_dec(v___y_701_);
lean_dec(v___y_699_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v_r_662_);
lean_ctor_set(v___x_694_, 3, v_r_688_);
lean_ctor_set(v___x_694_, 2, v_v_660_);
lean_ctor_set(v___x_694_, 1, v_k_659_);
lean_ctor_set(v___x_694_, 0, v___x_702_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_r_688_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_r_662_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 4, v___x_704_);
lean_ctor_set(v___x_682_, 3, v___y_700_);
lean_ctor_set(v___x_682_, 2, v_v_686_);
lean_ctor_set(v___x_682_, 1, v_k_685_);
lean_ctor_set(v___x_682_, 0, v___x_697_);
v___x_706_ = v___x_682_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_k_685_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_v_686_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v___y_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_nat_add(v___x_696_, v___y_710_);
lean_dec(v___y_710_);
lean_dec(v___x_696_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_l_687_);
lean_ctor_set(v___x_666_, 3, v_tree_669_);
lean_ctor_set(v___x_666_, 2, v_v_671_);
lean_ctor_set(v___x_666_, 1, v_k_670_);
lean_ctor_set(v___x_666_, 0, v___x_711_);
v___x_713_ = v___x_666_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_670_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_671_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_tree_669_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_l_687_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_nat_add(v___x_663_, v_size_689_);
if (lean_obj_tag(v_r_688_) == 0)
{
lean_object* v_size_715_; 
v_size_715_ = lean_ctor_get(v_r_688_, 0);
lean_inc(v_size_715_);
v___y_699_ = v___x_714_;
v___y_700_ = v___x_713_;
v___y_701_ = v_size_715_;
goto v___jp_698_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___y_699_ = v___x_714_;
v___y_700_ = v___x_713_;
v___y_701_ = v___x_716_;
goto v___jp_698_;
}
}
}
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_726_ = lean_nat_add(v___x_663_, v_size_672_);
v___x_727_ = lean_nat_add(v___x_726_, v_size_658_);
lean_dec(v_size_658_);
v___x_728_ = lean_nat_add(v___x_726_, v_size_684_);
lean_dec(v___x_726_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 4, v_l_661_);
lean_ctor_set(v___x_682_, 3, v_tree_669_);
lean_ctor_set(v___x_682_, 2, v_v_671_);
lean_ctor_set(v___x_682_, 1, v_k_670_);
lean_ctor_set(v___x_682_, 0, v___x_728_);
v___x_730_ = v___x_682_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_670_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_671_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_tree_669_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_l_661_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_r_662_);
lean_ctor_set(v___x_666_, 3, v___x_730_);
lean_ctor_set(v___x_666_, 2, v_v_660_);
lean_ctor_set(v___x_666_, 1, v_k_659_);
lean_ctor_set(v___x_666_, 0, v___x_727_);
v___x_732_ = v___x_666_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_r_662_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_794_; 
lean_inc(v_r_662_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_inc(v_size_658_);
v_isSharedCheck_794_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_795_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_r_481_, 2);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_r_481_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_799_);
v___x_742_ = v_r_481_;
v_isShared_743_ = v_isSharedCheck_794_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_r_481_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_794_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
if (lean_obj_tag(v_l_661_) == 0)
{
if (lean_obj_tag(v_r_662_) == 0)
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v_size_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc(v_tree_669_);
v_k_744_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_k_744_);
v_v_745_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_v_745_);
lean_dec_ref(v___x_668_);
v_size_746_ = lean_ctor_get(v_l_661_, 0);
v___x_747_ = lean_nat_add(v___x_663_, v_size_658_);
lean_dec(v_size_658_);
v___x_748_ = lean_nat_add(v___x_663_, v_size_746_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v_l_661_);
lean_ctor_set(v___x_742_, 3, v_tree_669_);
lean_ctor_set(v___x_742_, 2, v_v_745_);
lean_ctor_set(v___x_742_, 1, v_k_744_);
lean_ctor_set(v___x_742_, 0, v___x_748_);
v___x_750_ = v___x_742_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_745_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_tree_669_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_l_661_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_r_662_);
lean_ctor_set(v___x_666_, 3, v___x_750_);
lean_ctor_set(v___x_666_, 2, v_v_660_);
lean_ctor_set(v___x_666_, 1, v_k_659_);
lean_ctor_set(v___x_666_, 0, v___x_747_);
v___x_752_ = v___x_666_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_r_662_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_size_658_);
v_k_755_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_k_755_);
v_v_756_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_v_756_);
lean_dec_ref(v___x_668_);
v_k_757_ = lean_ctor_get(v_l_661_, 1);
v_v_758_ = lean_ctor_get(v_l_661_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_l_661_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_773_ = lean_ctor_get(v_l_661_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_l_661_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_l_661_, 0);
lean_dec(v_unused_775_);
v___x_760_ = v_l_661_;
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_v_758_);
lean_inc(v_k_757_);
lean_dec(v_l_661_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(3u);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_r_662_);
lean_ctor_set(v___x_760_, 3, v_r_662_);
lean_ctor_set(v___x_760_, 2, v_v_756_);
lean_ctor_set(v___x_760_, 1, v_k_755_);
lean_ctor_set(v___x_760_, 0, v___x_663_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_r_662_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_r_662_);
v___x_764_ = v_reuseFailAlloc_771_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v_r_662_);
lean_ctor_set(v___x_742_, 0, v___x_663_);
v___x_766_ = v___x_742_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_r_662_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_662_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v___x_766_);
lean_ctor_set(v___x_666_, 3, v___x_764_);
lean_ctor_set(v___x_666_, 2, v_v_758_);
lean_ctor_set(v___x_666_, 1, v_k_757_);
lean_ctor_set(v___x_666_, 0, v___x_762_);
v___x_768_ = v___x_666_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_662_) == 0)
{
lean_object* v_k_776_; lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_size_658_);
v_k_776_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_k_776_);
v_v_777_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_v_777_);
lean_dec_ref(v___x_668_);
v___x_778_ = lean_unsigned_to_nat(3u);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v_l_661_);
lean_ctor_set(v___x_742_, 2, v_v_777_);
lean_ctor_set(v___x_742_, 1, v_k_776_);
lean_ctor_set(v___x_742_, 0, v___x_663_);
v___x_780_ = v___x_742_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_776_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_l_661_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_r_662_);
lean_ctor_set(v___x_666_, 3, v___x_780_);
lean_ctor_set(v___x_666_, 2, v_v_660_);
lean_ctor_set(v___x_666_, 1, v_k_659_);
lean_ctor_set(v___x_666_, 0, v___x_778_);
v___x_782_ = v___x_666_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_r_662_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_k_785_; lean_object* v_v_786_; lean_object* v___x_788_; 
v_k_785_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_k_785_);
v_v_786_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_v_786_);
lean_dec_ref(v___x_668_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v_r_662_);
v___x_788_ = v___x_742_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_size_658_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_r_662_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_r_662_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(2u);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v___x_788_);
lean_ctor_set(v___x_666_, 3, v_r_662_);
lean_ctor_set(v___x_666_, 2, v_v_786_);
lean_ctor_set(v___x_666_, 1, v_k_785_);
lean_ctor_set(v___x_666_, 0, v___x_789_);
v___x_791_ = v___x_666_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_r_662_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v___x_788_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_r_662_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_959_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_r_481_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_r_481_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_963_);
v___x_807_ = v_r_481_;
v_isShared_808_ = v_isSharedCheck_958_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_r_481_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_958_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v_tree_810_; 
v___x_809_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_659_, v_v_660_, v_l_661_, v_r_662_);
v_tree_810_ = lean_ctor_get(v___x_809_, 2);
lean_inc(v_tree_810_);
if (lean_obj_tag(v_tree_810_) == 0)
{
lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v_size_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_k_811_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_k_811_);
v_v_812_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_v_812_);
lean_dec_ref(v___x_809_);
v_size_813_ = lean_ctor_get(v_tree_810_, 0);
v___x_814_ = lean_unsigned_to_nat(3u);
v___x_815_ = lean_nat_mul(v___x_814_, v_size_813_);
v___x_816_ = lean_nat_dec_lt(v___x_815_, v_size_653_);
lean_dec(v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
lean_dec(v_r_657_);
v___x_817_ = lean_nat_add(v___x_663_, v_size_653_);
v___x_818_ = lean_nat_add(v___x_817_, v_size_813_);
lean_dec(v___x_817_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_tree_810_);
lean_ctor_set(v___x_807_, 3, v_l_480_);
lean_ctor_set(v___x_807_, 2, v_v_812_);
lean_ctor_set(v___x_807_, 1, v_k_811_);
lean_ctor_set(v___x_807_, 0, v___x_818_);
v___x_820_ = v___x_807_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_tree_810_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_887_; 
lean_inc(v_l_656_);
lean_inc(v_v_655_);
lean_inc(v_k_654_);
lean_inc(v_size_653_);
v_isSharedCheck_887_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_888_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_l_480_, 2);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_l_480_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_892_);
v___x_823_ = v_l_480_;
v_isShared_824_ = v_isSharedCheck_887_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_l_480_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_887_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_size_825_; lean_object* v_size_826_; lean_object* v_k_827_; lean_object* v_v_828_; lean_object* v_l_829_; lean_object* v_r_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_size_825_ = lean_ctor_get(v_l_656_, 0);
v_size_826_ = lean_ctor_get(v_r_657_, 0);
v_k_827_ = lean_ctor_get(v_r_657_, 1);
v_v_828_ = lean_ctor_get(v_r_657_, 2);
v_l_829_ = lean_ctor_get(v_r_657_, 3);
v_r_830_ = lean_ctor_get(v_r_657_, 4);
v___x_831_ = lean_unsigned_to_nat(2u);
v___x_832_ = lean_nat_mul(v___x_831_, v_size_825_);
v___x_833_ = lean_nat_dec_lt(v_size_826_, v___x_832_);
lean_dec(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_r_830_);
lean_inc(v_l_829_);
lean_inc(v_v_828_);
lean_inc(v_k_827_);
lean_del_object(v___x_823_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_r_657_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_872_ = lean_ctor_get(v_r_657_, 4);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_r_657_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_r_657_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_r_657_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_r_657_, 0);
lean_dec(v_unused_876_);
v___x_835_ = v_r_657_;
v_isShared_836_ = v_isSharedCheck_871_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_r_657_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_871_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___x_859_; lean_object* v___y_861_; 
v___x_837_ = lean_nat_add(v___x_663_, v_size_653_);
lean_dec(v_size_653_);
v___x_838_ = lean_nat_add(v___x_837_, v_size_813_);
lean_dec(v___x_837_);
v___x_859_ = lean_nat_add(v___x_663_, v_size_825_);
if (lean_obj_tag(v_l_829_) == 0)
{
lean_object* v_size_869_; 
v_size_869_ = lean_ctor_get(v_l_829_, 0);
lean_inc(v_size_869_);
v___y_861_ = v_size_869_;
goto v___jp_860_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___y_861_ = v___x_870_;
goto v___jp_860_;
}
v___jp_839_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_nat_add(v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec(v___y_841_);
lean_inc_ref(v_tree_810_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 4, v_tree_810_);
lean_ctor_set(v___x_835_, 3, v_r_830_);
lean_ctor_set(v___x_835_, 2, v_v_812_);
lean_ctor_set(v___x_835_, 1, v_k_811_);
lean_ctor_set(v___x_835_, 0, v___x_843_);
v___x_845_ = v___x_835_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_r_830_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_tree_810_);
v___x_845_ = v_reuseFailAlloc_858_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_isSharedCheck_852_ = !lean_is_exclusive(v_tree_810_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; lean_object* v_unused_854_; lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; 
v_unused_853_ = lean_ctor_get(v_tree_810_, 4);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_tree_810_, 3);
lean_dec(v_unused_854_);
v_unused_855_ = lean_ctor_get(v_tree_810_, 2);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_tree_810_, 1);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_tree_810_, 0);
lean_dec(v_unused_857_);
v___x_847_ = v_tree_810_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_tree_810_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 4, v___x_845_);
lean_ctor_set(v___x_847_, 3, v___y_840_);
lean_ctor_set(v___x_847_, 2, v_v_828_);
lean_ctor_set(v___x_847_, 1, v_k_827_);
lean_ctor_set(v___x_847_, 0, v___x_838_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_827_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_828_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v___y_840_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v___x_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_nat_add(v___x_859_, v___y_861_);
lean_dec(v___y_861_);
lean_dec(v___x_859_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_l_829_);
lean_ctor_set(v___x_807_, 3, v_l_656_);
lean_ctor_set(v___x_807_, 2, v_v_655_);
lean_ctor_set(v___x_807_, 1, v_k_654_);
lean_ctor_set(v___x_807_, 0, v___x_862_);
v___x_864_ = v___x_807_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_l_829_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; 
v___x_865_ = lean_nat_add(v___x_663_, v_size_813_);
if (lean_obj_tag(v_r_830_) == 0)
{
lean_object* v_size_866_; 
v_size_866_ = lean_ctor_get(v_r_830_, 0);
lean_inc(v_size_866_);
v___y_840_ = v___x_864_;
v___y_841_ = v___x_865_;
v___y_842_ = v_size_866_;
goto v___jp_839_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___y_840_ = v___x_864_;
v___y_841_ = v___x_865_;
v___y_842_ = v___x_867_;
goto v___jp_839_;
}
}
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_877_ = lean_nat_add(v___x_663_, v_size_653_);
lean_dec(v_size_653_);
v___x_878_ = lean_nat_add(v___x_877_, v_size_813_);
lean_dec(v___x_877_);
v___x_879_ = lean_nat_add(v___x_663_, v_size_813_);
v___x_880_ = lean_nat_add(v___x_879_, v_size_826_);
lean_dec(v___x_879_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_tree_810_);
lean_ctor_set(v___x_807_, 3, v_r_657_);
lean_ctor_set(v___x_807_, 2, v_v_812_);
lean_ctor_set(v___x_807_, 1, v_k_811_);
lean_ctor_set(v___x_807_, 0, v___x_880_);
v___x_882_ = v___x_807_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_r_657_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_tree_810_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 4, v___x_882_);
lean_ctor_set(v___x_823_, 0, v___x_878_);
v___x_884_ = v___x_823_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_656_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_916_; 
lean_inc_ref(v_l_656_);
lean_inc(v_v_655_);
lean_inc(v_k_654_);
lean_inc(v_size_653_);
v_isSharedCheck_916_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; lean_object* v_unused_921_; 
v_unused_917_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_l_480_, 2);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_l_480_, 1);
lean_dec(v_unused_920_);
v_unused_921_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_921_);
v___x_894_ = v_l_480_;
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_l_480_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (lean_obj_tag(v_r_657_) == 0)
{
lean_object* v_k_896_; lean_object* v_v_897_; lean_object* v_size_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v_k_896_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_k_896_);
v_v_897_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_v_897_);
lean_dec_ref(v___x_809_);
v_size_898_ = lean_ctor_get(v_r_657_, 0);
v___x_899_ = lean_nat_add(v___x_663_, v_size_653_);
lean_dec(v_size_653_);
v___x_900_ = lean_nat_add(v___x_663_, v_size_898_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_tree_810_);
lean_ctor_set(v___x_807_, 3, v_r_657_);
lean_ctor_set(v___x_807_, 2, v_v_897_);
lean_ctor_set(v___x_807_, 1, v_k_896_);
lean_ctor_set(v___x_807_, 0, v___x_900_);
v___x_902_ = v___x_807_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_896_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_897_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_r_657_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_tree_810_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v___x_902_);
lean_ctor_set(v___x_894_, 0, v___x_899_);
v___x_904_ = v___x_894_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_k_907_; lean_object* v_v_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_size_653_);
v_k_907_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_k_907_);
v_v_908_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_v_908_);
lean_dec_ref(v___x_809_);
v___x_909_ = lean_unsigned_to_nat(3u);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_r_657_);
lean_ctor_set(v___x_807_, 3, v_r_657_);
lean_ctor_set(v___x_807_, 2, v_v_908_);
lean_ctor_set(v___x_807_, 1, v_k_907_);
lean_ctor_set(v___x_807_, 0, v___x_663_);
v___x_911_ = v___x_807_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_k_907_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_v_908_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_r_657_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_r_657_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v___x_911_);
lean_ctor_set(v___x_894_, 0, v___x_909_);
v___x_913_ = v___x_894_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_657_) == 0)
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_l_656_);
lean_inc(v_v_655_);
lean_inc(v_k_654_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_l_480_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; 
v_unused_947_ = lean_ctor_get(v_l_480_, 4);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_l_480_, 3);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_l_480_, 2);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_l_480_, 1);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_l_480_, 0);
lean_dec(v_unused_951_);
v___x_923_ = v_l_480_;
v_isShared_924_ = v_isSharedCheck_946_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_l_480_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_946_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_942_; 
v_k_925_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_k_925_);
v_v_926_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_v_926_);
lean_dec_ref(v___x_809_);
v_k_927_ = lean_ctor_get(v_r_657_, 1);
v_v_928_ = lean_ctor_get(v_r_657_, 2);
v_isSharedCheck_942_ = !lean_is_exclusive(v_r_657_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_943_ = lean_ctor_get(v_r_657_, 4);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_r_657_, 3);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_r_657_, 0);
lean_dec(v_unused_945_);
v___x_930_ = v_r_657_;
v_isShared_931_ = v_isSharedCheck_942_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_v_928_);
lean_inc(v_k_927_);
lean_dec(v_r_657_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_942_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(3u);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v_l_656_);
lean_ctor_set(v___x_930_, 3, v_l_656_);
lean_ctor_set(v___x_930_, 2, v_v_655_);
lean_ctor_set(v___x_930_, 1, v_k_654_);
lean_ctor_set(v___x_930_, 0, v___x_663_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_l_656_);
v___x_934_ = v_reuseFailAlloc_941_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_l_656_);
lean_ctor_set(v___x_807_, 3, v_l_656_);
lean_ctor_set(v___x_807_, 2, v_v_926_);
lean_ctor_set(v___x_807_, 1, v_k_925_);
lean_ctor_set(v___x_807_, 0, v___x_663_);
v___x_936_ = v___x_807_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_k_925_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_v_926_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_l_656_);
v___x_936_ = v_reuseFailAlloc_940_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v___x_936_);
lean_ctor_set(v___x_923_, 3, v___x_934_);
lean_ctor_set(v___x_923_, 2, v_v_928_);
lean_ctor_set(v___x_923_, 1, v_k_927_);
lean_ctor_set(v___x_923_, 0, v___x_932_);
v___x_938_ = v___x_923_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
else
{
lean_object* v_k_952_; lean_object* v_v_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v_k_952_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_k_952_);
v_v_953_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_v_953_);
lean_dec_ref(v___x_809_);
v___x_954_ = lean_unsigned_to_nat(2u);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_r_657_);
lean_ctor_set(v___x_807_, 3, v_l_480_);
lean_ctor_set(v___x_807_, 2, v_v_953_);
lean_ctor_set(v___x_807_, 1, v_k_952_);
lean_ctor_set(v___x_807_, 0, v___x_954_);
v___x_956_ = v___x_807_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_952_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_953_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_l_480_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_r_657_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
}
else
{
return v_l_480_;
}
}
else
{
return v_r_481_;
}
}
}
else
{
lean_object* v_impl_964_; lean_object* v___x_965_; 
v_impl_964_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v_k_476_, v_l_480_);
v___x_965_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_964_) == 0)
{
if (lean_obj_tag(v_r_481_) == 0)
{
lean_object* v_size_966_; lean_object* v_size_967_; lean_object* v_k_968_; lean_object* v_v_969_; lean_object* v_l_970_; lean_object* v_r_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_size_966_ = lean_ctor_get(v_impl_964_, 0);
v_size_967_ = lean_ctor_get(v_r_481_, 0);
v_k_968_ = lean_ctor_get(v_r_481_, 1);
v_v_969_ = lean_ctor_get(v_r_481_, 2);
v_l_970_ = lean_ctor_get(v_r_481_, 3);
lean_inc(v_l_970_);
v_r_971_ = lean_ctor_get(v_r_481_, 4);
v___x_972_ = lean_unsigned_to_nat(3u);
v___x_973_ = lean_nat_mul(v___x_972_, v_size_966_);
v___x_974_ = lean_nat_dec_lt(v___x_973_, v_size_967_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_l_970_);
v___x_975_ = lean_nat_add(v___x_965_, v_size_966_);
v___x_976_ = lean_nat_add(v___x_975_, v_size_967_);
lean_dec(v___x_975_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 3, v_impl_964_);
lean_ctor_set(v___x_483_, 0, v___x_976_);
v___x_978_ = v___x_483_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_impl_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_r_481_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1043_; 
lean_inc(v_r_971_);
lean_inc(v_v_969_);
lean_inc(v_k_968_);
lean_inc(v_size_967_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; lean_object* v_unused_1046_; lean_object* v_unused_1047_; lean_object* v_unused_1048_; 
v_unused_1044_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_r_481_, 2);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v_r_481_, 1);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_1048_);
v___x_981_ = v_r_481_;
v_isShared_982_ = v_isSharedCheck_1043_;
goto v_resetjp_980_;
}
else
{
lean_dec(v_r_481_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1043_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_size_983_; lean_object* v_k_984_; lean_object* v_v_985_; lean_object* v_l_986_; lean_object* v_r_987_; lean_object* v_size_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_size_983_ = lean_ctor_get(v_l_970_, 0);
v_k_984_ = lean_ctor_get(v_l_970_, 1);
v_v_985_ = lean_ctor_get(v_l_970_, 2);
v_l_986_ = lean_ctor_get(v_l_970_, 3);
v_r_987_ = lean_ctor_get(v_l_970_, 4);
v_size_988_ = lean_ctor_get(v_r_971_, 0);
v___x_989_ = lean_unsigned_to_nat(2u);
v___x_990_ = lean_nat_mul(v___x_989_, v_size_988_);
v___x_991_ = lean_nat_dec_lt(v_size_983_, v___x_990_);
lean_dec(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1019_; 
lean_inc(v_r_987_);
lean_inc(v_l_986_);
lean_inc(v_v_985_);
lean_inc(v_k_984_);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_l_970_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; 
v_unused_1020_ = lean_ctor_get(v_l_970_, 4);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_l_970_, 3);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_l_970_, 2);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_l_970_, 1);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_970_, 0);
lean_dec(v_unused_1024_);
v___x_993_ = v_l_970_;
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_l_970_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1009_; 
v___x_995_ = lean_nat_add(v___x_965_, v_size_966_);
v___x_996_ = lean_nat_add(v___x_995_, v_size_967_);
lean_dec(v_size_967_);
if (lean_obj_tag(v_l_986_) == 0)
{
lean_object* v_size_1017_; 
v_size_1017_ = lean_ctor_get(v_l_986_, 0);
lean_inc(v_size_1017_);
v___y_1009_ = v_size_1017_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___y_1009_ = v___x_1018_;
goto v___jp_1008_;
}
v___jp_997_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_nat_add(v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 4, v_r_971_);
lean_ctor_set(v___x_993_, 3, v_r_987_);
lean_ctor_set(v___x_993_, 2, v_v_969_);
lean_ctor_set(v___x_993_, 1, v_k_968_);
lean_ctor_set(v___x_993_, 0, v___x_1001_);
v___x_1003_ = v___x_993_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_968_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_969_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_r_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_r_971_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v___x_1003_);
lean_ctor_set(v___x_981_, 3, v___y_998_);
lean_ctor_set(v___x_981_, 2, v_v_985_);
lean_ctor_set(v___x_981_, 1, v_k_984_);
lean_ctor_set(v___x_981_, 0, v___x_996_);
v___x_1005_ = v___x_981_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_984_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_985_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___y_998_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_nat_add(v___x_995_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec(v___x_995_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_l_986_);
lean_ctor_set(v___x_483_, 3, v_impl_964_);
lean_ctor_set(v___x_483_, 0, v___x_1010_);
v___x_1012_ = v___x_483_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_impl_964_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_l_986_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_nat_add(v___x_965_, v_size_988_);
if (lean_obj_tag(v_r_987_) == 0)
{
lean_object* v_size_1014_; 
v_size_1014_ = lean_ctor_get(v_r_987_, 0);
lean_inc(v_size_1014_);
v___y_998_ = v___x_1012_;
v___y_999_ = v___x_1013_;
v___y_1000_ = v_size_1014_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v___y_998_ = v___x_1012_;
v___y_999_ = v___x_1013_;
v___y_1000_ = v___x_1015_;
goto v___jp_997_;
}
}
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_del_object(v___x_483_);
v___x_1025_ = lean_nat_add(v___x_965_, v_size_966_);
v___x_1026_ = lean_nat_add(v___x_1025_, v_size_967_);
lean_dec(v_size_967_);
v___x_1027_ = lean_nat_add(v___x_1025_, v_size_983_);
lean_dec(v___x_1025_);
lean_inc_ref(v_impl_964_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v_l_970_);
lean_ctor_set(v___x_981_, 3, v_impl_964_);
lean_ctor_set(v___x_981_, 2, v_v_479_);
lean_ctor_set(v___x_981_, 1, v_k_478_);
lean_ctor_set(v___x_981_, 0, v___x_1027_);
v___x_1029_ = v___x_981_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_impl_964_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_l_970_);
v___x_1029_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_isSharedCheck_1036_ = !lean_is_exclusive(v_impl_964_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; lean_object* v_unused_1038_; lean_object* v_unused_1039_; lean_object* v_unused_1040_; lean_object* v_unused_1041_; 
v_unused_1037_ = lean_ctor_get(v_impl_964_, 4);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_impl_964_, 3);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v_impl_964_, 2);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v_impl_964_, 1);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_impl_964_, 0);
lean_dec(v_unused_1041_);
v___x_1031_ = v_impl_964_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v_impl_964_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v_r_971_);
lean_ctor_set(v___x_1031_, 3, v___x_1029_);
lean_ctor_set(v___x_1031_, 2, v_v_969_);
lean_ctor_set(v___x_1031_, 1, v_k_968_);
lean_ctor_set(v___x_1031_, 0, v___x_1026_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_k_968_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_v_969_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_r_971_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v_size_1049_ = lean_ctor_get(v_impl_964_, 0);
v___x_1050_ = lean_nat_add(v___x_965_, v_size_1049_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 3, v_impl_964_);
lean_ctor_set(v___x_483_, 0, v___x_1050_);
v___x_1052_ = v___x_483_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_impl_964_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_r_481_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
if (lean_obj_tag(v_r_481_) == 0)
{
lean_object* v_l_1054_; 
v_l_1054_ = lean_ctor_get(v_r_481_, 3);
lean_inc(v_l_1054_);
if (lean_obj_tag(v_l_1054_) == 0)
{
lean_object* v_r_1055_; 
v_r_1055_ = lean_ctor_get(v_r_481_, 4);
lean_inc(v_r_1055_);
if (lean_obj_tag(v_r_1055_) == 0)
{
lean_object* v_size_1056_; lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1071_; 
v_size_1056_ = lean_ctor_get(v_r_481_, 0);
v_k_1057_ = lean_ctor_get(v_r_481_, 1);
v_v_1058_ = lean_ctor_get(v_r_481_, 2);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1072_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_1073_);
v___x_1060_ = v_r_481_;
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_v_1058_);
lean_inc(v_k_1057_);
lean_inc(v_size_1056_);
lean_dec(v_r_481_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_size_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_size_1062_ = lean_ctor_get(v_l_1054_, 0);
v___x_1063_ = lean_nat_add(v___x_965_, v_size_1056_);
lean_dec(v_size_1056_);
v___x_1064_ = lean_nat_add(v___x_965_, v_size_1062_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 4, v_l_1054_);
lean_ctor_set(v___x_1060_, 3, v_impl_964_);
lean_ctor_set(v___x_1060_, 2, v_v_479_);
lean_ctor_set(v___x_1060_, 1, v_k_478_);
lean_ctor_set(v___x_1060_, 0, v___x_1064_);
v___x_1066_ = v___x_1060_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_impl_964_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_l_1054_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_r_1055_);
lean_ctor_set(v___x_483_, 3, v___x_1066_);
lean_ctor_set(v___x_483_, 2, v_v_1058_);
lean_ctor_set(v___x_483_, 1, v_k_1057_);
lean_ctor_set(v___x_483_, 0, v___x_1063_);
v___x_1068_ = v___x_483_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_r_1055_);
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
else
{
lean_object* v_k_1074_; lean_object* v_v_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1098_; 
v_k_1074_ = lean_ctor_get(v_r_481_, 1);
v_v_1075_ = lean_ctor_get(v_r_481_, 2);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1099_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_1101_);
v___x_1077_ = v_r_481_;
v_isShared_1078_ = v_isSharedCheck_1098_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_v_1075_);
lean_inc(v_k_1074_);
lean_dec(v_r_481_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1098_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1094_; 
v_k_1079_ = lean_ctor_get(v_l_1054_, 1);
v_v_1080_ = lean_ctor_get(v_l_1054_, 2);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_l_1054_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1095_ = lean_ctor_get(v_l_1054_, 4);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_l_1054_, 3);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_l_1054_, 0);
lean_dec(v_unused_1097_);
v___x_1082_ = v_l_1054_;
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
lean_dec(v_l_1054_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(3u);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 4, v_r_1055_);
lean_ctor_set(v___x_1082_, 3, v_r_1055_);
lean_ctor_set(v___x_1082_, 2, v_v_479_);
lean_ctor_set(v___x_1082_, 1, v_k_478_);
lean_ctor_set(v___x_1082_, 0, v___x_965_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_r_1055_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_r_1055_);
v___x_1086_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 3, v_r_1055_);
lean_ctor_set(v___x_1077_, 0, v___x_965_);
v___x_1088_ = v___x_1077_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_k_1074_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_v_1075_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_r_1055_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_r_1055_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v___x_1088_);
lean_ctor_set(v___x_483_, 3, v___x_1086_);
lean_ctor_set(v___x_483_, 2, v_v_1080_);
lean_ctor_set(v___x_483_, 1, v_k_1079_);
lean_ctor_set(v___x_483_, 0, v___x_1084_);
v___x_1090_ = v___x_483_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1102_; 
v_r_1102_ = lean_ctor_get(v_r_481_, 4);
lean_inc(v_r_1102_);
if (lean_obj_tag(v_r_1102_) == 0)
{
lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1115_; 
v_k_1103_ = lean_ctor_get(v_r_481_, 1);
v_v_1104_ = lean_ctor_get(v_r_481_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1116_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_481_, 0);
lean_dec(v_unused_1118_);
v___x_1106_ = v_r_481_;
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_v_1104_);
lean_inc(v_k_1103_);
lean_dec(v_r_481_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_unsigned_to_nat(3u);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_l_1054_);
lean_ctor_set(v___x_1106_, 2, v_v_479_);
lean_ctor_set(v___x_1106_, 1, v_k_478_);
lean_ctor_set(v___x_1106_, 0, v___x_965_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1054_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_l_1054_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_r_1102_);
lean_ctor_set(v___x_483_, 3, v___x_1110_);
lean_ctor_set(v___x_483_, 2, v_v_1104_);
lean_ctor_set(v___x_483_, 1, v_k_1103_);
lean_ctor_set(v___x_483_, 0, v___x_1108_);
v___x_1112_ = v___x_483_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_r_1102_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_size_1119_; lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1132_; 
v_size_1119_ = lean_ctor_get(v_r_481_, 0);
v_k_1120_ = lean_ctor_get(v_r_481_, 1);
v_v_1121_ = lean_ctor_get(v_r_481_, 2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_r_481_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; lean_object* v_unused_1134_; 
v_unused_1133_ = lean_ctor_get(v_r_481_, 4);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_r_481_, 3);
lean_dec(v_unused_1134_);
v___x_1123_ = v_r_481_;
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_v_1121_);
lean_inc(v_k_1120_);
lean_inc(v_size_1119_);
lean_dec(v_r_481_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 3, v_r_1102_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_size_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_1120_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_r_1102_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_r_1102_);
v___x_1126_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(2u);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v___x_1126_);
lean_ctor_set(v___x_483_, 3, v_r_1102_);
lean_ctor_set(v___x_483_, 0, v___x_1127_);
v___x_1129_ = v___x_483_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_r_1102_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v___x_1126_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
else
{
lean_object* v___x_1136_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 3, v_r_481_);
lean_ctor_set(v___x_483_, 0, v___x_965_);
v___x_1136_ = v___x_483_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_r_481_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_r_481_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
else
{
return v_t_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg___boxed(lean_object* v_k_1140_, lean_object* v_t_1141_){
_start:
{
uint64_t v_k_boxed_1142_; lean_object* v_res_1143_; 
v_k_boxed_1142_ = lean_unbox_uint64(v_k_1140_);
lean_dec_ref(v_k_1140_);
v_res_1143_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v_k_boxed_1142_, v_t_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object* v_t_1144_, uint64_t v_k_1145_){
_start:
{
if (lean_obj_tag(v_t_1144_) == 0)
{
lean_object* v_k_1146_; lean_object* v_v_1147_; lean_object* v_l_1148_; lean_object* v_r_1149_; uint64_t v___x_1150_; uint8_t v___x_1151_; 
v_k_1146_ = lean_ctor_get(v_t_1144_, 1);
v_v_1147_ = lean_ctor_get(v_t_1144_, 2);
v_l_1148_ = lean_ctor_get(v_t_1144_, 3);
v_r_1149_ = lean_ctor_get(v_t_1144_, 4);
v___x_1150_ = lean_unbox_uint64(v_k_1146_);
v___x_1151_ = lean_uint64_dec_lt(v_k_1145_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint64_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_unbox_uint64(v_k_1146_);
v___x_1153_ = lean_uint64_dec_eq(v_k_1145_, v___x_1152_);
if (v___x_1153_ == 0)
{
v_t_1144_ = v_r_1149_;
goto _start;
}
else
{
lean_object* v___x_1155_; 
lean_inc(v_v_1147_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_v_1147_);
return v___x_1155_;
}
}
else
{
v_t_1144_ = v_l_1148_;
goto _start;
}
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object* v_t_1158_, lean_object* v_k_1159_){
_start:
{
uint64_t v_k_boxed_1160_; lean_object* v_res_1161_; 
v_k_boxed_1160_ = lean_unbox_uint64(v_k_1159_);
lean_dec_ref(v_k_1159_);
v_res_1161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1158_, v_k_boxed_1160_);
lean_dec(v_t_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object* v_state_1162_, uint64_t v_id_1163_, lean_object* v_reason_1164_){
_start:
{
lean_object* v_tokens_1166_; lean_object* v___x_1167_; 
v_tokens_1166_ = lean_ctor_get(v_state_1162_, 0);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1166_, v_id_1163_);
if (lean_obj_tag(v___x_1167_) == 1)
{
lean_object* v_val_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v_val_1172_; lean_object* v___x_1184_; lean_object* v_a_1185_; 
v_val_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_fst_1169_ = lean_ctor_get(v_val_1168_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v_val_1168_, 1);
lean_inc(v_snd_1170_);
lean_dec(v_val_1168_);
lean_inc(v_reason_1164_);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_reason_1164_, v_state_1162_, v_snd_1170_);
lean_dec(v_snd_1170_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
v_val_1172_ = v_a_1185_;
goto v___jp_1171_;
v___jp_1171_:
{
lean_object* v___x_1173_; lean_object* v_tokens_1174_; uint64_t v_id_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v___x_1173_ = l_Std_CancellationToken_cancel(v_fst_1169_, v_reason_1164_);
v_tokens_1174_ = lean_ctor_get(v_val_1172_, 0);
v_id_1175_ = lean_ctor_get_uint64(v_val_1172_, sizeof(void*)*1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_val_1172_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v_val_1172_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_tokens_1174_);
lean_dec(v_val_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v_id_1163_, v_tokens_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
lean_ctor_set_uint64(v_reuseFailAlloc_1182_, sizeof(void*)*1, v_id_1175_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_dec(v___x_1167_);
lean_dec(v_reason_1164_);
return v_state_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object* v_reason_1186_, lean_object* v_init_1187_, lean_object* v_x_1188_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_k_1190_; lean_object* v_l_1191_; lean_object* v_r_1192_; lean_object* v___x_1193_; lean_object* v_a_1194_; uint64_t v___x_1195_; lean_object* v___x_1196_; 
v_k_1190_ = lean_ctor_get(v_x_1188_, 1);
v_l_1191_ = lean_ctor_get(v_x_1188_, 3);
v_r_1192_ = lean_ctor_get(v_x_1188_, 4);
lean_inc_n(v_reason_1186_, 2);
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_reason_1186_, v_init_1187_, v_l_1191_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = lean_unbox_uint64(v_k_1190_);
v___x_1196_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_a_1194_, v___x_1195_, v_reason_1186_);
v_init_1187_ = v___x_1196_;
v_x_1188_ = v_r_1192_;
goto _start;
}
else
{
lean_object* v___x_1198_; 
lean_dec(v_reason_1186_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_init_1187_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object* v_reason_1199_, lean_object* v_init_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_reason_1199_, v_init_1200_, v_x_1201_);
lean_dec(v_x_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object* v_state_1204_, lean_object* v_id_1205_, lean_object* v_reason_1206_, lean_object* v_a_1207_){
_start:
{
uint64_t v_id_boxed_1208_; lean_object* v_res_1209_; 
v_id_boxed_1208_ = lean_unbox_uint64(v_id_1205_);
lean_dec_ref(v_id_1205_);
v_res_1209_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_state_1204_, v_id_boxed_1208_, v_reason_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object* v_00_u03b4_1210_, lean_object* v_t_1211_, uint64_t v_k_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1211_, v_k_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object* v_00_u03b4_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_){
_start:
{
uint64_t v_k_boxed_1217_; lean_object* v_res_1218_; 
v_k_boxed_1217_ = lean_unbox_uint64(v_k_1216_);
lean_dec_ref(v_k_1216_);
v_res_1218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_1214_, v_t_1215_, v_k_boxed_1217_);
lean_dec(v_t_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object* v_00_u03b2_1219_, uint64_t v_k_1220_, lean_object* v_t_1221_, lean_object* v_h_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v_k_1220_, v_t_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object* v_00_u03b2_1224_, lean_object* v_k_1225_, lean_object* v_t_1226_, lean_object* v_h_1227_){
_start:
{
uint64_t v_k_boxed_1228_; lean_object* v_res_1229_; 
v_k_boxed_1228_ = lean_unbox_uint64(v_k_1225_);
lean_dec_ref(v_k_1225_);
v_res_1229_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_00_u03b2_1224_, v_k_boxed_1228_, v_t_1226_, v_h_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1(uint64_t v___x_1230_, lean_object* v_x_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___redArg(v___x_1230_, v_x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1___boxed(lean_object* v___x_1233_, lean_object* v_x_1234_){
_start:
{
uint64_t v___x_815__boxed_1235_; lean_object* v_res_1236_; 
v___x_815__boxed_1235_ = lean_unbox_uint64(v___x_1233_);
lean_dec_ref(v___x_1233_);
v_res_1236_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1(v___x_815__boxed_1235_, v_x_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(uint64_t v___x_1237_, uint64_t v_k_1238_, lean_object* v_t_1239_){
_start:
{
if (lean_obj_tag(v_t_1239_) == 0)
{
lean_object* v_size_1240_; lean_object* v_k_1241_; lean_object* v_v_1242_; lean_object* v_l_1243_; lean_object* v_r_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1268_; 
v_size_1240_ = lean_ctor_get(v_t_1239_, 0);
v_k_1241_ = lean_ctor_get(v_t_1239_, 1);
v_v_1242_ = lean_ctor_get(v_t_1239_, 2);
v_l_1243_ = lean_ctor_get(v_t_1239_, 3);
v_r_1244_ = lean_ctor_get(v_t_1239_, 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_t_1239_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1246_ = v_t_1239_;
v_isShared_1247_ = v_isSharedCheck_1268_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_r_1244_);
lean_inc(v_l_1243_);
lean_inc(v_v_1242_);
lean_inc(v_k_1241_);
lean_inc(v_size_1240_);
lean_dec(v_t_1239_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1268_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
uint64_t v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = lean_unbox_uint64(v_k_1241_);
v___x_1249_ = lean_uint64_dec_lt(v_k_1238_, v___x_1248_);
if (v___x_1249_ == 0)
{
uint64_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_unbox_uint64(v_k_1241_);
v___x_1251_ = lean_uint64_dec_eq(v_k_1238_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(v___x_1237_, v_k_1238_, v_r_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 4, v___x_1252_);
v___x_1254_ = v___x_1246_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_size_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_k_1241_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_v_1242_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_l_1243_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_dec(v_k_1241_);
v___f_1256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__1___closed__0));
v___x_1257_ = lean_box_uint64(v___x_1237_);
v___f_1258_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1258_, 0, v___x_1257_);
v___x_1259_ = l_Prod_map___redArg(v___f_1256_, v___f_1258_, v_v_1242_);
v___x_1260_ = lean_box_uint64(v_k_1238_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 2, v___x_1259_);
lean_ctor_set(v___x_1246_, 1, v___x_1260_);
v___x_1262_ = v___x_1246_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_size_1240_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_l_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_r_1244_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(v___x_1237_, v_k_1238_, v_l_1243_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 3, v___x_1264_);
v___x_1266_ = v___x_1246_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_size_1240_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1241_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1242_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_r_1244_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
return v_t_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0___boxed(lean_object* v___x_1269_, lean_object* v_k_1270_, lean_object* v_t_1271_){
_start:
{
uint64_t v___x_824__boxed_1272_; uint64_t v_k_boxed_1273_; lean_object* v_res_1274_; 
v___x_824__boxed_1272_ = lean_unbox_uint64(v___x_1269_);
lean_dec_ref(v___x_1269_);
v_k_boxed_1273_ = lean_unbox_uint64(v_k_1270_);
lean_dec_ref(v_k_1270_);
v_res_1274_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(v___x_824__boxed_1272_, v_k_boxed_1273_, v_t_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t v_id_1275_, lean_object* v_reason_1276_, lean_object* v_parent_x3f_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___y_1283_; 
v___x_1280_ = lean_st_ref_get(v___y_1278_);
v___x_1281_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v___x_1280_, v_id_1275_, v_reason_1276_);
if (lean_obj_tag(v_parent_x3f_1277_) == 0)
{
v___y_1283_ = v___x_1281_;
goto v___jp_1282_;
}
else
{
lean_object* v_val_1286_; lean_object* v_tokens_1287_; uint64_t v_id_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1297_; 
v_val_1286_ = lean_ctor_get(v_parent_x3f_1277_, 0);
v_tokens_1287_ = lean_ctor_get(v___x_1281_, 0);
v_id_1288_ = lean_ctor_get_uint64(v___x_1281_, sizeof(void*)*1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1290_ = v___x_1281_;
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_tokens_1287_);
lean_dec(v___x_1281_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
uint64_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = lean_unbox_uint64(v_val_1286_);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__0(v_id_1275_, v___x_1292_, v_tokens_1287_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set_uint64(v_reuseFailAlloc_1296_, sizeof(void*)*1, v_id_1288_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v___y_1283_ = v___x_1295_;
goto v___jp_1282_;
}
}
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_st_ref_swap(v___y_1278_, v___y_1283_);
lean_dec(v___x_1285_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object* v_id_1298_, lean_object* v_reason_1299_, lean_object* v_parent_x3f_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint64_t v_id_boxed_1303_; lean_object* v_res_1304_; 
v_id_boxed_1303_ = lean_unbox_uint64(v_id_1298_);
lean_dec_ref(v_id_1298_);
v_res_1304_ = l_Std_CancellationContext_cancel___lam__0(v_id_boxed_1303_, v_reason_1299_, v_parent_x3f_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec(v_parent_x3f_1300_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object* v_x_1305_, lean_object* v_reason_1306_){
_start:
{
lean_object* v_state_1308_; lean_object* v_token_1309_; uint64_t v_id_1310_; lean_object* v_parent_x3f_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; uint8_t v___x_1314_; 
v_state_1308_ = lean_ctor_get(v_x_1305_, 0);
lean_inc_ref(v_state_1308_);
v_token_1309_ = lean_ctor_get(v_x_1305_, 1);
lean_inc_ref(v_token_1309_);
v_id_1310_ = lean_ctor_get_uint64(v_x_1305_, sizeof(void*)*3);
v_parent_x3f_1311_ = lean_ctor_get(v_x_1305_, 2);
lean_inc(v_parent_x3f_1311_);
lean_dec_ref(v_x_1305_);
v___x_1312_ = lean_box_uint64(v_id_1310_);
v___f_1313_ = lean_alloc_closure((void*)(l_Std_CancellationContext_cancel___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1313_, 0, v___x_1312_);
lean_closure_set(v___f_1313_, 1, v_reason_1306_);
lean_closure_set(v___f_1313_, 2, v_parent_x3f_1311_);
v___x_1314_ = l_Std_CancellationToken_isCancelled(v_token_1309_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(v_state_1308_, v___f_1313_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; 
lean_dec_ref(v___f_1313_);
lean_dec_ref(v_state_1308_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object* v_x_1317_, lean_object* v_reason_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_CancellationContext_cancel(v_x_1317_, v_reason_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object* v_x_1321_){
_start:
{
lean_object* v_token_1323_; uint8_t v___x_1324_; 
v_token_1323_ = lean_ctor_get(v_x_1321_, 1);
lean_inc_ref(v_token_1323_);
lean_dec_ref(v_x_1321_);
v___x_1324_ = l_Std_CancellationToken_isCancelled(v_token_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object* v_x_1325_, lean_object* v_a_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Std_CancellationContext_isCancelled(v_x_1325_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object* v_x_1329_){
_start:
{
lean_object* v_token_1331_; lean_object* v___x_1332_; 
v_token_1331_ = lean_ctor_get(v_x_1329_, 1);
lean_inc_ref(v_token_1331_);
lean_dec_ref(v_x_1329_);
v___x_1332_ = l_Std_CancellationToken_getCancellationReason(v_token_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object* v_x_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_CancellationContext_getCancellationReason(v_x_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object* v_x_1336_){
_start:
{
lean_object* v_token_1338_; lean_object* v___x_1339_; 
v_token_1338_ = lean_ctor_get(v_x_1336_, 1);
lean_inc_ref(v_token_1338_);
lean_dec_ref(v_x_1336_);
v___x_1339_ = l_Std_CancellationToken_wait(v_token_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object* v_x_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Std_CancellationContext_done(v_x_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object* v_x_1343_){
_start:
{
lean_object* v_token_1344_; lean_object* v___x_1345_; 
v_token_1344_ = lean_ctor_get(v_x_1343_, 1);
lean_inc_ref(v_token_1344_);
lean_dec_ref(v_x_1343_);
v___x_1345_ = l_Std_CancellationToken_selector(v_token_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object* v_state_1346_, uint64_t v_id_1347_){
_start:
{
lean_object* v_tokens_1348_; lean_object* v___x_1349_; 
v_tokens_1348_ = lean_ctor_get(v_state_1346_, 0);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1348_, v_id_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_val_1351_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1349_, 1);
v_snd_1352_ = lean_ctor_get(v_val_1351_, 1);
lean_inc(v_snd_1352_);
lean_dec(v_val_1351_);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(v_state_1346_, v___x_1354_, v_snd_1352_);
lean_dec(v_snd_1352_);
v___x_1356_ = lean_nat_add(v___x_1353_, v___x_1355_);
lean_dec(v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(lean_object* v_state_1357_, lean_object* v_init_1358_, lean_object* v_x_1359_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
lean_object* v_k_1360_; lean_object* v_l_1361_; lean_object* v_r_1362_; lean_object* v___x_1363_; uint64_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_k_1360_ = lean_ctor_get(v_x_1359_, 1);
v_l_1361_ = lean_ctor_get(v_x_1359_, 3);
v_r_1362_ = lean_ctor_get(v_x_1359_, 4);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(v_state_1357_, v_init_1358_, v_l_1361_);
v___x_1364_ = lean_unbox_uint64(v_k_1360_);
v___x_1365_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1357_, v___x_1364_);
v___x_1366_ = lean_nat_add(v___x_1363_, v___x_1365_);
lean_dec(v___x_1365_);
lean_dec(v___x_1363_);
v_init_1358_ = v___x_1366_;
v_x_1359_ = v_r_1362_;
goto _start;
}
else
{
return v_init_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0___boxed(lean_object* v_state_1368_, lean_object* v_init_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(v_state_1368_, v_init_1369_, v_x_1370_);
lean_dec(v_x_1370_);
lean_dec_ref(v_state_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object* v_state_1372_, lean_object* v_id_1373_){
_start:
{
uint64_t v_id_boxed_1374_; lean_object* v_res_1375_; 
v_id_boxed_1374_ = lean_unbox_uint64(v_id_1373_);
lean_dec_ref(v_id_1373_);
v_res_1375_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1372_, v_id_boxed_1374_);
lean_dec_ref(v_state_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object* v_state_1376_, lean_object* v_init_1377_, lean_object* v_t_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_spec__0(v_state_1376_, v_init_1377_, v_t_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object* v_state_1380_, lean_object* v_init_1381_, lean_object* v_t_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1380_, v_init_1381_, v_t_1382_);
lean_dec(v_t_1382_);
lean_dec_ref(v_state_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t v_id_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_st_ref_get(v___y_1385_);
v___x_1388_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v___x_1387_, v_id_1384_);
lean_dec(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object* v_id_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint64_t v_id_boxed_1392_; lean_object* v_res_1393_; 
v_id_boxed_1392_ = lean_unbox_uint64(v_id_1389_);
lean_dec_ref(v_id_1389_);
v_res_1393_ = l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_1392_, v___y_1390_);
lean_dec(v___y_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object* v_x_1394_){
_start:
{
lean_object* v_state_1396_; uint64_t v_id_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_state_1396_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_state_1396_);
v_id_1397_ = lean_ctor_get_uint64(v_x_1394_, sizeof(void*)*3);
lean_dec_ref(v_x_1394_);
v___x_1398_ = lean_box_uint64(v_id_1397_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_CancellationContext_countAliveTokens___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1399_, 0, v___x_1398_);
v___x_1400_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__2___redArg(v_state_1396_, v___f_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object* v_x_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_CancellationContext_countAliveTokens(v_x_1401_);
return v_res_1403_;
}
}
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_CancellationContext(builtin);
}
#ifdef __cplusplus
}
#endif
