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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
lean_object* l_Std_CancellationToken_new();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_CancellationContext_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_CancellationContext_new___closed__0 = (const lean_object*)&l_Std_CancellationContext_new___closed__0_value;
LEAN_EXPORT lean_object* l_Std_CancellationContext_new();
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(uint64_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t v_k_1_, lean_object* v_v_2_, lean_object* v_t_3_){
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
v___x_53_ = lean_nat_add(v___y_50_, v___y_52_);
lean_dec(v___y_52_);
lean_dec(v___y_50_);
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
lean_ctor_set(v___x_33_, 3, v___y_51_);
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
lean_ctor_set(v_reuseFailAlloc_58_, 3, v___y_51_);
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
v___y_50_ = v___x_65_;
v___y_51_ = v___x_64_;
v___y_52_ = v_size_66_;
goto v___jp_49_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___y_50_ = v___x_65_;
v___y_51_ = v___x_64_;
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_1_ = stack[0].m_num;
lean_object* v_v_2_ = stack[1].m_obj;
lean_object* v_t_3_ = stack[2].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1_, v_v_2_, v_t_3_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object* v_k_297_, lean_object* v_v_298_, lean_object* v_t_299_){
_start:
{
uint64_t v_k_boxed_300_; lean_object* v_res_301_; 
v_k_boxed_300_ = lean_unbox_uint64(v_k_297_);
lean_dec_ref(v_k_297_);
v_res_301_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_boxed_300_, v_v_298_, v_t_299_);
return v_res_301_;
}
}
lean_object* l_Std_CancellationContext_new(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint64_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint64_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_305_ = l_Std_CancellationToken_new();
v___x_306_ = lean_box(1);
v___x_307_ = 0ULL;
v___x_308_ = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(v___x_305_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_305_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v___x_307_, v___x_309_, v___x_306_);
v___x_311_ = 1ULL;
v___x_312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint64(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = l_Std_Mutex_new___redArg(v___x_312_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_305_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_ctor_set_uint64(v___x_315_, sizeof(void*)*3, v___x_307_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_316_;
v_res_316_ = l_Std_CancellationContext_new();
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_CancellationContext_new();
return v_res_318_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object* v_00_u03b2_319_, uint64_t v_k_320_, lean_object* v_v_321_, lean_object* v_t_322_, lean_object* v_hl_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_320_, v_v_321_, v_t_322_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_320_ = stack[1].m_num;
lean_object* v_v_321_ = stack[2].m_obj;
lean_object* v_t_322_ = stack[3].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_box(0), v_k_320_, v_v_321_, v_t_322_, lean_box(0));
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object* v_00_u03b2_326_, lean_object* v_k_327_, lean_object* v_v_328_, lean_object* v_t_329_, lean_object* v_hl_330_){
_start:
{
uint64_t v_k_boxed_331_; lean_object* v_res_332_; 
v_k_boxed_331_ = lean_unbox_uint64(v_k_327_);
lean_dec_ref(v_k_327_);
v_res_332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(v_00_u03b2_326_, v_k_boxed_331_, v_v_328_, v_t_329_, v_hl_330_);
return v_res_332_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object* v_mutex_333_, lean_object* v_k_334_){
_start:
{
lean_object* v_ref_336_; lean_object* v_mutex_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_ref_336_ = lean_ctor_get(v_mutex_333_, 0);
lean_inc(v_ref_336_);
v_mutex_337_ = lean_ctor_get(v_mutex_333_, 1);
lean_inc(v_mutex_337_);
lean_dec_ref(v_mutex_333_);
v___x_338_ = lean_io_basemutex_lock(v_mutex_337_);
v___x_339_ = lean_apply_2(v_k_334_, v_ref_336_, lean_box(0));
v___x_340_ = lean_io_basemutex_unlock(v_mutex_337_);
lean_dec(v_mutex_337_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_333_ = stack[0].m_obj;
lean_object* v_k_334_ = stack[1].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_333_, v_k_334_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object* v_mutex_342_, lean_object* v_k_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_342_, v_k_343_);
return v_res_345_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_mutex_348_, lean_object* v_k_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_348_, v_k_349_);
return v___x_351_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_348_ = stack[2].m_obj;
lean_object* v_k_349_ = stack[3].m_obj;
lean_object* v_res_352_;
v_res_352_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_box(0), lean_box(0), v_mutex_348_, v_k_349_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_mutex_355_, lean_object* v_k_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(v_00_u03b1_353_, v_00_u03b2_354_, v_mutex_355_, v_k_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object* v_x_359_){
_start:
{
lean_inc_ref(v_x_359_);
return v_x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_360_);
lean_dec_ref(v_x_360_);
return v_res_361_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t v___x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_box_uint64(v___x_362_);
v___x_365_ = lean_array_push(v_x_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_362_ = stack[0].m_num;
lean_object* v_x_363_ = stack[1].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_362_, v_x_363_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object* v___x_367_, lean_object* v_x_368_){
_start:
{
uint64_t v___x_1232__boxed_369_; lean_object* v_res_370_; 
v___x_1232__boxed_369_ = lean_unbox_uint64(v___x_367_);
lean_dec_ref(v___x_367_);
v_res_370_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1232__boxed_369_, v_x_368_);
return v_res_370_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t v___x_372_, uint64_t v_k_373_, lean_object* v_t_374_){
_start:
{
if (lean_obj_tag(v_t_374_) == 0)
{
lean_object* v_size_375_; lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v_l_378_; lean_object* v_r_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_403_; 
v_size_375_ = lean_ctor_get(v_t_374_, 0);
v_k_376_ = lean_ctor_get(v_t_374_, 1);
v_v_377_ = lean_ctor_get(v_t_374_, 2);
v_l_378_ = lean_ctor_get(v_t_374_, 3);
v_r_379_ = lean_ctor_get(v_t_374_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v_t_374_);
if (v_isSharedCheck_403_ == 0)
{
v___x_381_ = v_t_374_;
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_r_379_);
lean_inc(v_l_378_);
lean_inc(v_v_377_);
lean_inc(v_k_376_);
lean_inc(v_size_375_);
lean_dec(v_t_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint64_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_unbox_uint64(v_k_376_);
v___x_384_ = lean_uint64_dec_lt(v_k_373_, v___x_383_);
if (v___x_384_ == 0)
{
uint64_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_unbox_uint64(v_k_376_);
v___x_386_ = lean_uint64_dec_eq(v_k_373_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_372_, v_k_373_, v_r_379_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v___x_387_);
v___x_389_ = v___x_381_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_size_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_v_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_l_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec(v_k_376_);
v___f_391_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
v___x_392_ = lean_box_uint64(v___x_372_);
v___f_393_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(v___f_393_, 0, v___x_392_);
v___x_394_ = l_Prod_map___redArg(v___f_391_, v___f_393_, v_v_377_);
v___x_395_ = lean_box_uint64(v_k_373_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 2, v___x_394_);
lean_ctor_set(v___x_381_, 1, v___x_395_);
v___x_397_ = v___x_381_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_size_375_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_378_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_r_379_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_372_, v_k_373_, v_l_378_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 3, v___x_399_);
v___x_401_ = v___x_381_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_size_375_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_376_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_377_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_r_379_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
return v_t_374_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_372_ = stack[0].m_num;
uint64_t v_k_373_ = stack[1].m_num;
lean_object* v_t_374_ = stack[2].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_372_, v_k_373_, v_t_374_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object* v___x_405_, lean_object* v_k_406_, lean_object* v_t_407_){
_start:
{
uint64_t v___x_1250__boxed_408_; uint64_t v_k_boxed_409_; lean_object* v_res_410_; 
v___x_1250__boxed_408_ = lean_unbox_uint64(v___x_405_);
lean_dec_ref(v___x_405_);
v_k_boxed_409_ = lean_unbox_uint64(v_k_406_);
lean_dec_ref(v_k_406_);
v_res_410_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1250__boxed_408_, v_k_boxed_409_, v_t_407_);
return v_res_410_;
}
}
lean_object* l_Std_CancellationContext_fork___lam__0(lean_object* v_token_411_, uint64_t v_id_412_, lean_object* v_state_413_, lean_object* v_root_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_Std_CancellationToken_isCancelled(v_token_411_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_tokens_420_; uint64_t v_id_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_438_; 
v___x_418_ = l_Std_CancellationToken_new();
v___x_419_ = lean_st_ref_get(v___y_415_);
v_tokens_420_ = lean_ctor_get(v___x_419_, 0);
v_id_421_ = lean_ctor_get_uint64(v___x_419_, sizeof(void*)*1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_438_ == 0)
{
v___x_423_ = v___x_419_;
v_isShared_424_ = v_isSharedCheck_438_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_tokens_420_);
lean_dec(v___x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_438_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; lean_object* v___x_432_; 
v___x_425_ = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(v___x_418_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_418_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_421_, v___x_426_, v_tokens_420_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_421_, v_id_412_, v___x_427_);
v___x_429_ = 1ULL;
v___x_430_ = lean_uint64_add(v_id_421_, v___x_429_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_428_);
v___x_432_ = v___x_423_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_428_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_ctor_set_uint64(v___x_432_, sizeof(void*)*1, v___x_430_);
v___x_433_ = lean_st_ref_swap(v___y_415_, v___x_432_);
lean_dec(v___x_433_);
v___x_434_ = lean_box_uint64(v_id_412_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_436_, 0, v_state_413_);
lean_ctor_set(v___x_436_, 1, v___x_418_);
lean_ctor_set(v___x_436_, 2, v___x_435_);
lean_ctor_set_uint64(v___x_436_, sizeof(void*)*3, v_id_421_);
return v___x_436_;
}
}
}
else
{
lean_dec_ref(v_state_413_);
lean_inc_ref(v_root_414_);
return v_root_414_;
}
}
}
LEAN_EXPORT void l_Std_CancellationContext_fork___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_411_ = stack[0].m_obj;
uint64_t v_id_412_ = stack[1].m_num;
lean_object* v_state_413_ = stack[2].m_obj;
lean_object* v_root_414_ = stack[3].m_obj;
lean_object* v___y_415_ = stack[4].m_obj;
lean_object* v_res_439_;
v_res_439_ = l_Std_CancellationContext_fork___lam__0(v_token_411_, v_id_412_, v_state_413_, v_root_414_, v___y_415_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object* v_token_440_, lean_object* v_id_441_, lean_object* v_state_442_, lean_object* v_root_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint64_t v_id_boxed_446_; lean_object* v_res_447_; 
v_id_boxed_446_ = lean_unbox_uint64(v_id_441_);
lean_dec_ref(v_id_441_);
v_res_447_ = l_Std_CancellationContext_fork___lam__0(v_token_440_, v_id_boxed_446_, v_state_442_, v_root_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v_root_443_);
return v_res_447_;
}
}
lean_object* l_Std_CancellationContext_fork(lean_object* v_root_448_){
_start:
{
lean_object* v_state_450_; lean_object* v_token_451_; uint64_t v_id_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v_state_450_ = lean_ctor_get(v_root_448_, 0);
lean_inc_ref_n(v_state_450_, 2);
v_token_451_ = lean_ctor_get(v_root_448_, 1);
lean_inc_ref(v_token_451_);
v_id_452_ = lean_ctor_get_uint64(v_root_448_, sizeof(void*)*3);
v___x_453_ = lean_box_uint64(v_id_452_);
v___f_454_ = lean_alloc_closure((void*)(l_Std_CancellationContext_fork___lam__0___boxed), 6, 4);
lean_closure_set(v___f_454_, 0, v_token_451_);
lean_closure_set(v___f_454_, 1, v___x_453_);
lean_closure_set(v___f_454_, 2, v_state_450_);
lean_closure_set(v___f_454_, 3, v_root_448_);
v___x_455_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_450_, v___f_454_);
return v___x_455_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_fork_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_448_ = stack[0].m_obj;
lean_object* v_res_456_;
v_res_456_ = l_Std_CancellationContext_fork(v_root_448_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object* v_root_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_CancellationContext_fork(v_root_457_);
return v_res_459_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t v_k_460_, lean_object* v_t_461_){
_start:
{
if (lean_obj_tag(v_t_461_) == 0)
{
lean_object* v_k_462_; lean_object* v_v_463_; lean_object* v_l_464_; lean_object* v_r_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_1122_; 
v_k_462_ = lean_ctor_get(v_t_461_, 1);
v_v_463_ = lean_ctor_get(v_t_461_, 2);
v_l_464_ = lean_ctor_get(v_t_461_, 3);
v_r_465_ = lean_ctor_get(v_t_461_, 4);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_t_461_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_t_461_, 0);
lean_dec(v_unused_1123_);
v___x_467_ = v_t_461_;
v_isShared_468_ = v_isSharedCheck_1122_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_r_465_);
lean_inc(v_l_464_);
lean_inc(v_v_463_);
lean_inc(v_k_462_);
lean_dec(v_t_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_1122_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint64_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_unbox_uint64(v_k_462_);
v___x_470_ = lean_uint64_dec_lt(v_k_460_, v___x_469_);
if (v___x_470_ == 0)
{
uint64_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_unbox_uint64(v_k_462_);
v___x_472_ = lean_uint64_dec_eq(v_k_460_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v_impl_473_; lean_object* v___x_474_; 
v_impl_473_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_460_, v_r_465_);
v___x_474_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_473_) == 0)
{
if (lean_obj_tag(v_l_464_) == 0)
{
lean_object* v_size_475_; lean_object* v_size_476_; lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v_l_479_; lean_object* v_r_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_size_475_ = lean_ctor_get(v_impl_473_, 0);
v_size_476_ = lean_ctor_get(v_l_464_, 0);
v_k_477_ = lean_ctor_get(v_l_464_, 1);
v_v_478_ = lean_ctor_get(v_l_464_, 2);
v_l_479_ = lean_ctor_get(v_l_464_, 3);
v_r_480_ = lean_ctor_get(v_l_464_, 4);
lean_inc(v_r_480_);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_nat_mul(v___x_481_, v_size_475_);
v___x_483_ = lean_nat_dec_lt(v___x_482_, v_size_476_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec(v_r_480_);
v___x_484_ = lean_nat_add(v___x_474_, v_size_476_);
v___x_485_ = lean_nat_add(v___x_484_, v_size_475_);
lean_dec(v___x_484_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_impl_473_);
lean_ctor_set(v___x_467_, 0, v___x_485_);
v___x_487_ = v___x_467_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_impl_473_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_554_; 
lean_inc(v_l_479_);
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_inc(v_size_476_);
v_isSharedCheck_554_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_l_464_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_l_464_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_559_);
v___x_490_ = v_l_464_;
v_isShared_491_ = v_isSharedCheck_554_;
goto v_resetjp_489_;
}
else
{
lean_dec(v_l_464_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_554_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_size_492_; lean_object* v_size_493_; lean_object* v_k_494_; lean_object* v_v_495_; lean_object* v_l_496_; lean_object* v_r_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_size_492_ = lean_ctor_get(v_l_479_, 0);
v_size_493_ = lean_ctor_get(v_r_480_, 0);
v_k_494_ = lean_ctor_get(v_r_480_, 1);
v_v_495_ = lean_ctor_get(v_r_480_, 2);
v_l_496_ = lean_ctor_get(v_r_480_, 3);
v_r_497_ = lean_ctor_get(v_r_480_, 4);
v___x_498_ = lean_unsigned_to_nat(2u);
v___x_499_ = lean_nat_mul(v___x_498_, v_size_492_);
v___x_500_ = lean_nat_dec_lt(v_size_493_, v___x_499_);
lean_dec(v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_529_; 
lean_inc(v_r_497_);
lean_inc(v_l_496_);
lean_inc(v_v_495_);
lean_inc(v_k_494_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_r_480_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_530_ = lean_ctor_get(v_r_480_, 4);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_r_480_, 3);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_r_480_, 2);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_r_480_, 1);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_r_480_, 0);
lean_dec(v_unused_534_);
v___x_502_ = v_r_480_;
v_isShared_503_ = v_isSharedCheck_529_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_r_480_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_529_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___x_517_; lean_object* v___y_519_; 
v___x_504_ = lean_nat_add(v___x_474_, v_size_476_);
lean_dec(v_size_476_);
v___x_505_ = lean_nat_add(v___x_504_, v_size_475_);
lean_dec(v___x_504_);
v___x_517_ = lean_nat_add(v___x_474_, v_size_492_);
if (lean_obj_tag(v_l_496_) == 0)
{
lean_object* v_size_527_; 
v_size_527_ = lean_ctor_get(v_l_496_, 0);
lean_inc(v_size_527_);
v___y_519_ = v_size_527_;
goto v___jp_518_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___y_519_ = v___x_528_;
goto v___jp_518_;
}
v___jp_506_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_nat_add(v___y_507_, v___y_509_);
lean_dec(v___y_509_);
lean_dec(v___y_507_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 4, v_impl_473_);
lean_ctor_set(v___x_502_, 3, v_r_497_);
lean_ctor_set(v___x_502_, 2, v_v_463_);
lean_ctor_set(v___x_502_, 1, v_k_462_);
lean_ctor_set(v___x_502_, 0, v___x_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_r_497_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_impl_473_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 4, v___x_512_);
lean_ctor_set(v___x_490_, 3, v___y_508_);
lean_ctor_set(v___x_490_, 2, v_v_495_);
lean_ctor_set(v___x_490_, 1, v_k_494_);
lean_ctor_set(v___x_490_, 0, v___x_505_);
v___x_514_ = v___x_490_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_k_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_v_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v___y_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_nat_add(v___x_517_, v___y_519_);
lean_dec(v___y_519_);
lean_dec(v___x_517_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_l_496_);
lean_ctor_set(v___x_467_, 3, v_l_479_);
lean_ctor_set(v___x_467_, 2, v_v_478_);
lean_ctor_set(v___x_467_, 1, v_k_477_);
lean_ctor_set(v___x_467_, 0, v___x_520_);
v___x_522_ = v___x_467_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_l_479_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v_l_496_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_nat_add(v___x_474_, v_size_475_);
if (lean_obj_tag(v_r_497_) == 0)
{
lean_object* v_size_524_; 
v_size_524_ = lean_ctor_get(v_r_497_, 0);
lean_inc(v_size_524_);
v___y_507_ = v___x_523_;
v___y_508_ = v___x_522_;
v___y_509_ = v_size_524_;
goto v___jp_506_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___y_507_ = v___x_523_;
v___y_508_ = v___x_522_;
v___y_509_ = v___x_525_;
goto v___jp_506_;
}
}
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
lean_del_object(v___x_467_);
v___x_535_ = lean_nat_add(v___x_474_, v_size_476_);
lean_dec(v_size_476_);
v___x_536_ = lean_nat_add(v___x_535_, v_size_475_);
lean_dec(v___x_535_);
v___x_537_ = lean_nat_add(v___x_474_, v_size_475_);
v___x_538_ = lean_nat_add(v___x_537_, v_size_493_);
lean_dec(v___x_537_);
lean_inc_ref(v_impl_473_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 4, v_impl_473_);
lean_ctor_set(v___x_490_, 3, v_r_480_);
lean_ctor_set(v___x_490_, 2, v_v_463_);
lean_ctor_set(v___x_490_, 1, v_k_462_);
lean_ctor_set(v___x_490_, 0, v___x_538_);
v___x_540_ = v___x_490_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_r_480_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_impl_473_);
v___x_540_ = v_reuseFailAlloc_553_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_isSharedCheck_547_ = !lean_is_exclusive(v_impl_473_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_548_ = lean_ctor_get(v_impl_473_, 4);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_impl_473_, 3);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_impl_473_, 2);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_impl_473_, 1);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_impl_473_, 0);
lean_dec(v_unused_552_);
v___x_542_ = v_impl_473_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_impl_473_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v___x_540_);
lean_ctor_set(v___x_542_, 3, v_l_479_);
lean_ctor_set(v___x_542_, 2, v_v_478_);
lean_ctor_set(v___x_542_, 1, v_k_477_);
lean_ctor_set(v___x_542_, 0, v___x_536_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_l_479_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v___x_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v_size_560_ = lean_ctor_get(v_impl_473_, 0);
v___x_561_ = lean_nat_add(v___x_474_, v_size_560_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_impl_473_);
lean_ctor_set(v___x_467_, 0, v___x_561_);
v___x_563_ = v___x_467_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_impl_473_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
if (lean_obj_tag(v_l_464_) == 0)
{
lean_object* v_l_565_; 
v_l_565_ = lean_ctor_get(v_l_464_, 3);
if (lean_obj_tag(v_l_565_) == 0)
{
lean_object* v_r_566_; 
lean_inc_ref(v_l_565_);
v_r_566_ = lean_ctor_get(v_l_464_, 4);
lean_inc(v_r_566_);
if (lean_obj_tag(v_r_566_) == 0)
{
lean_object* v_size_567_; lean_object* v_k_568_; lean_object* v_v_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_582_; 
v_size_567_ = lean_ctor_get(v_l_464_, 0);
v_k_568_ = lean_ctor_get(v_l_464_, 1);
v_v_569_ = lean_ctor_get(v_l_464_, 2);
v_isSharedCheck_582_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; lean_object* v_unused_584_; 
v_unused_583_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_584_);
v___x_571_ = v_l_464_;
v_isShared_572_ = v_isSharedCheck_582_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_v_569_);
lean_inc(v_k_568_);
lean_inc(v_size_567_);
lean_dec(v_l_464_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_582_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_size_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v_size_573_ = lean_ctor_get(v_r_566_, 0);
v___x_574_ = lean_nat_add(v___x_474_, v_size_567_);
lean_dec(v_size_567_);
v___x_575_ = lean_nat_add(v___x_474_, v_size_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 4, v_impl_473_);
lean_ctor_set(v___x_571_, 3, v_r_566_);
lean_ctor_set(v___x_571_, 2, v_v_463_);
lean_ctor_set(v___x_571_, 1, v_k_462_);
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_r_566_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_impl_473_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_577_);
lean_ctor_set(v___x_467_, 3, v_l_565_);
lean_ctor_set(v___x_467_, 2, v_v_569_);
lean_ctor_set(v___x_467_, 1, v_k_568_);
lean_ctor_set(v___x_467_, 0, v___x_574_);
v___x_579_ = v___x_467_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_k_585_; lean_object* v_v_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
v_k_585_ = lean_ctor_get(v_l_464_, 1);
v_v_586_ = lean_ctor_get(v_l_464_, 2);
v_isSharedCheck_597_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_598_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_600_);
v___x_588_ = v_l_464_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_v_586_);
lean_inc(v_k_585_);
lean_dec(v_l_464_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(3u);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 3, v_r_566_);
lean_ctor_set(v___x_588_, 2, v_v_463_);
lean_ctor_set(v___x_588_, 1, v_k_462_);
lean_ctor_set(v___x_588_, 0, v___x_474_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_r_566_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_r_566_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_592_);
lean_ctor_set(v___x_467_, 3, v_l_565_);
lean_ctor_set(v___x_467_, 2, v_v_586_);
lean_ctor_set(v___x_467_, 1, v_k_585_);
lean_ctor_set(v___x_467_, 0, v___x_590_);
v___x_594_ = v___x_467_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_k_585_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_v_586_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
else
{
lean_object* v_r_601_; 
v_r_601_ = lean_ctor_get(v_l_464_, 4);
lean_inc(v_r_601_);
if (lean_obj_tag(v_r_601_) == 0)
{
lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_626_; 
lean_inc(v_l_565_);
v_k_602_ = lean_ctor_get(v_l_464_, 1);
v_v_603_ = lean_ctor_get(v_l_464_, 2);
v_isSharedCheck_626_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_627_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_629_);
v___x_605_ = v_l_464_;
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_l_464_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_k_607_; lean_object* v_v_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
v_k_607_ = lean_ctor_get(v_r_601_, 1);
v_v_608_ = lean_ctor_get(v_r_601_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_r_601_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v_r_601_, 4);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_r_601_, 3);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_r_601_, 0);
lean_dec(v_unused_625_);
v___x_610_ = v_r_601_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_v_608_);
lean_inc(v_k_607_);
lean_dec(v_r_601_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(3u);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v_l_565_);
lean_ctor_set(v___x_610_, 3, v_l_565_);
lean_ctor_set(v___x_610_, 2, v_v_603_);
lean_ctor_set(v___x_610_, 1, v_k_602_);
lean_ctor_set(v___x_610_, 0, v___x_474_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_l_565_);
v___x_614_ = v_reuseFailAlloc_621_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_l_565_);
lean_ctor_set(v___x_605_, 2, v_v_463_);
lean_ctor_set(v___x_605_, 1, v_k_462_);
lean_ctor_set(v___x_605_, 0, v___x_474_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_l_565_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_616_);
lean_ctor_set(v___x_467_, 3, v___x_614_);
lean_ctor_set(v___x_467_, 2, v_v_608_);
lean_ctor_set(v___x_467_, 1, v_k_607_);
lean_ctor_set(v___x_467_, 0, v___x_612_);
v___x_618_ = v___x_467_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(2u);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_r_601_);
lean_ctor_set(v___x_467_, 0, v___x_630_);
v___x_632_ = v___x_467_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_r_601_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v___x_635_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_l_464_);
lean_ctor_set(v___x_467_, 0, v___x_474_);
v___x_635_ = v___x_467_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_464_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_del_object(v___x_467_);
lean_dec(v_v_463_);
lean_dec(v_k_462_);
if (lean_obj_tag(v_l_464_) == 0)
{
if (lean_obj_tag(v_r_465_) == 0)
{
lean_object* v_size_637_; lean_object* v_k_638_; lean_object* v_v_639_; lean_object* v_l_640_; lean_object* v_r_641_; lean_object* v_size_642_; lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_size_637_ = lean_ctor_get(v_l_464_, 0);
v_k_638_ = lean_ctor_get(v_l_464_, 1);
v_v_639_ = lean_ctor_get(v_l_464_, 2);
v_l_640_ = lean_ctor_get(v_l_464_, 3);
v_r_641_ = lean_ctor_get(v_l_464_, 4);
lean_inc(v_r_641_);
v_size_642_ = lean_ctor_get(v_r_465_, 0);
v_k_643_ = lean_ctor_get(v_r_465_, 1);
v_v_644_ = lean_ctor_get(v_r_465_, 2);
v_l_645_ = lean_ctor_get(v_r_465_, 3);
lean_inc(v_l_645_);
v_r_646_ = lean_ctor_get(v_r_465_, 4);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_dec_lt(v_size_637_, v_size_642_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_784_; 
lean_inc(v_l_640_);
lean_inc(v_v_639_);
lean_inc(v_k_638_);
v_isSharedCheck_784_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_785_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_464_, 2);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_l_464_, 1);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_789_);
v___x_650_ = v_l_464_;
v_isShared_651_ = v_isSharedCheck_784_;
goto v_resetjp_649_;
}
else
{
lean_dec(v_l_464_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_784_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v_tree_653_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_638_, v_v_639_, v_l_640_, v_r_641_);
v_tree_653_ = lean_ctor_get(v___x_652_, 2);
if (lean_obj_tag(v_tree_653_) == 0)
{
lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v_size_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
lean_inc_ref(v_tree_653_);
v_k_654_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_k_654_);
v_v_655_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_v_655_);
lean_dec_ref(v___x_652_);
v_size_656_ = lean_ctor_get(v_tree_653_, 0);
v___x_657_ = lean_unsigned_to_nat(3u);
v___x_658_ = lean_nat_mul(v___x_657_, v_size_656_);
v___x_659_ = lean_nat_dec_lt(v___x_658_, v_size_642_);
lean_dec(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v_l_645_);
v___x_660_ = lean_nat_add(v___x_647_, v_size_656_);
v___x_661_ = lean_nat_add(v___x_660_, v_size_642_);
lean_dec(v___x_660_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_r_465_);
lean_ctor_set(v___x_650_, 3, v_tree_653_);
lean_ctor_set(v___x_650_, 2, v_v_655_);
lean_ctor_set(v___x_650_, 1, v_k_654_);
lean_ctor_set(v___x_650_, 0, v___x_661_);
v___x_663_ = v___x_650_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_tree_653_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_465_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_719_; 
lean_inc(v_r_646_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
lean_inc(v_size_642_);
v_isSharedCheck_719_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_720_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_r_465_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_r_465_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_724_);
v___x_666_ = v_r_465_;
v_isShared_667_ = v_isSharedCheck_719_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_r_465_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_719_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_size_668_; lean_object* v_k_669_; lean_object* v_v_670_; lean_object* v_l_671_; lean_object* v_r_672_; lean_object* v_size_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_size_668_ = lean_ctor_get(v_l_645_, 0);
v_k_669_ = lean_ctor_get(v_l_645_, 1);
v_v_670_ = lean_ctor_get(v_l_645_, 2);
v_l_671_ = lean_ctor_get(v_l_645_, 3);
v_r_672_ = lean_ctor_get(v_l_645_, 4);
v_size_673_ = lean_ctor_get(v_r_646_, 0);
v___x_674_ = lean_unsigned_to_nat(2u);
v___x_675_ = lean_nat_mul(v___x_674_, v_size_673_);
v___x_676_ = lean_nat_dec_lt(v_size_668_, v___x_675_);
lean_dec(v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_r_672_);
lean_inc(v_l_671_);
lean_inc(v_v_670_);
lean_inc(v_k_669_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_l_645_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_705_ = lean_ctor_get(v_l_645_, 4);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_l_645_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_l_645_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_l_645_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_l_645_, 0);
lean_dec(v_unused_709_);
v___x_678_ = v_l_645_;
v_isShared_679_ = v_isSharedCheck_704_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_l_645_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_704_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_694_; 
v___x_680_ = lean_nat_add(v___x_647_, v_size_656_);
v___x_681_ = lean_nat_add(v___x_680_, v_size_642_);
lean_dec(v_size_642_);
if (lean_obj_tag(v_l_671_) == 0)
{
lean_object* v_size_702_; 
v_size_702_ = lean_ctor_get(v_l_671_, 0);
lean_inc(v_size_702_);
v___y_694_ = v_size_702_;
goto v___jp_693_;
}
else
{
lean_object* v___x_703_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___y_694_ = v___x_703_;
goto v___jp_693_;
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_nat_add(v___y_683_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v___y_683_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_r_646_);
lean_ctor_set(v___x_678_, 3, v_r_672_);
lean_ctor_set(v___x_678_, 2, v_v_644_);
lean_ctor_set(v___x_678_, 1, v_k_643_);
lean_ctor_set(v___x_678_, 0, v___x_686_);
v___x_688_ = v___x_678_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_r_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_r_646_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v___x_688_);
lean_ctor_set(v___x_666_, 3, v___y_684_);
lean_ctor_set(v___x_666_, 2, v_v_670_);
lean_ctor_set(v___x_666_, 1, v_k_669_);
lean_ctor_set(v___x_666_, 0, v___x_681_);
v___x_690_ = v___x_666_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_669_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_670_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v___y_684_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_nat_add(v___x_680_, v___y_694_);
lean_dec(v___y_694_);
lean_dec(v___x_680_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_l_671_);
lean_ctor_set(v___x_650_, 3, v_tree_653_);
lean_ctor_set(v___x_650_, 2, v_v_655_);
lean_ctor_set(v___x_650_, 1, v_k_654_);
lean_ctor_set(v___x_650_, 0, v___x_695_);
v___x_697_ = v___x_650_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_tree_653_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_l_671_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = lean_nat_add(v___x_647_, v_size_673_);
if (lean_obj_tag(v_r_672_) == 0)
{
lean_object* v_size_699_; 
v_size_699_ = lean_ctor_get(v_r_672_, 0);
lean_inc(v_size_699_);
v___y_683_ = v___x_698_;
v___y_684_ = v___x_697_;
v___y_685_ = v_size_699_;
goto v___jp_682_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___y_683_ = v___x_698_;
v___y_684_ = v___x_697_;
v___y_685_ = v___x_700_;
goto v___jp_682_;
}
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_710_ = lean_nat_add(v___x_647_, v_size_656_);
v___x_711_ = lean_nat_add(v___x_710_, v_size_642_);
lean_dec(v_size_642_);
v___x_712_ = lean_nat_add(v___x_710_, v_size_668_);
lean_dec(v___x_710_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_l_645_);
lean_ctor_set(v___x_666_, 3, v_tree_653_);
lean_ctor_set(v___x_666_, 2, v_v_655_);
lean_ctor_set(v___x_666_, 1, v_k_654_);
lean_ctor_set(v___x_666_, 0, v___x_712_);
v___x_714_ = v___x_666_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_tree_653_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_l_645_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_r_646_);
lean_ctor_set(v___x_650_, 3, v___x_714_);
lean_ctor_set(v___x_650_, 2, v_v_644_);
lean_ctor_set(v___x_650_, 1, v_k_643_);
lean_ctor_set(v___x_650_, 0, v___x_711_);
v___x_716_ = v___x_650_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_r_646_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_778_; 
lean_inc(v_r_646_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
lean_inc(v_size_642_);
v_isSharedCheck_778_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; 
v_unused_779_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_465_, 2);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_465_, 1);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_783_);
v___x_726_ = v_r_465_;
v_isShared_727_ = v_isSharedCheck_778_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_r_465_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_778_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
if (lean_obj_tag(v_l_645_) == 0)
{
if (lean_obj_tag(v_r_646_) == 0)
{
lean_object* v_k_728_; lean_object* v_v_729_; lean_object* v_size_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_inc(v_tree_653_);
v_k_728_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_k_728_);
v_v_729_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_v_729_);
lean_dec_ref(v___x_652_);
v_size_730_ = lean_ctor_get(v_l_645_, 0);
v___x_731_ = lean_nat_add(v___x_647_, v_size_642_);
lean_dec(v_size_642_);
v___x_732_ = lean_nat_add(v___x_647_, v_size_730_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v_l_645_);
lean_ctor_set(v___x_726_, 3, v_tree_653_);
lean_ctor_set(v___x_726_, 2, v_v_729_);
lean_ctor_set(v___x_726_, 1, v_k_728_);
lean_ctor_set(v___x_726_, 0, v___x_732_);
v___x_734_ = v___x_726_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_k_728_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_v_729_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_tree_653_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_l_645_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_r_646_);
lean_ctor_set(v___x_650_, 3, v___x_734_);
lean_ctor_set(v___x_650_, 2, v_v_644_);
lean_ctor_set(v___x_650_, 1, v_k_643_);
lean_ctor_set(v___x_650_, 0, v___x_731_);
v___x_736_ = v___x_650_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_r_646_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_k_739_; lean_object* v_v_740_; lean_object* v_k_741_; lean_object* v_v_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_size_642_);
v_k_739_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_k_739_);
v_v_740_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_v_740_);
lean_dec_ref(v___x_652_);
v_k_741_ = lean_ctor_get(v_l_645_, 1);
v_v_742_ = lean_ctor_get(v_l_645_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_l_645_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_757_ = lean_ctor_get(v_l_645_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_645_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_645_, 0);
lean_dec(v_unused_759_);
v___x_744_ = v_l_645_;
v_isShared_745_ = v_isSharedCheck_756_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_v_742_);
lean_inc(v_k_741_);
lean_dec(v_l_645_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_756_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(3u);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 4, v_r_646_);
lean_ctor_set(v___x_744_, 3, v_r_646_);
lean_ctor_set(v___x_744_, 2, v_v_740_);
lean_ctor_set(v___x_744_, 1, v_k_739_);
lean_ctor_set(v___x_744_, 0, v___x_647_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_k_739_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_v_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_r_646_);
v___x_748_ = v_reuseFailAlloc_755_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 3, v_r_646_);
lean_ctor_set(v___x_726_, 0, v___x_647_);
v___x_750_ = v___x_726_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_r_646_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v___x_750_);
lean_ctor_set(v___x_650_, 3, v___x_748_);
lean_ctor_set(v___x_650_, 2, v_v_742_);
lean_ctor_set(v___x_650_, 1, v_k_741_);
lean_ctor_set(v___x_650_, 0, v___x_746_);
v___x_752_ = v___x_650_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_741_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_742_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_646_) == 0)
{
lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec(v_size_642_);
v_k_760_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_k_760_);
v_v_761_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_v_761_);
lean_dec_ref(v___x_652_);
v___x_762_ = lean_unsigned_to_nat(3u);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v_l_645_);
lean_ctor_set(v___x_726_, 2, v_v_761_);
lean_ctor_set(v___x_726_, 1, v_k_760_);
lean_ctor_set(v___x_726_, 0, v___x_647_);
v___x_764_ = v___x_726_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_l_645_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_l_645_);
v___x_764_ = v_reuseFailAlloc_768_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_r_646_);
lean_ctor_set(v___x_650_, 3, v___x_764_);
lean_ctor_set(v___x_650_, 2, v_v_644_);
lean_ctor_set(v___x_650_, 1, v_k_643_);
lean_ctor_set(v___x_650_, 0, v___x_762_);
v___x_766_ = v___x_650_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_r_646_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_772_; 
v_k_769_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_k_769_);
v_v_770_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_v_770_);
lean_dec_ref(v___x_652_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 3, v_r_646_);
v___x_772_ = v___x_726_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_r_646_);
v___x_772_ = v_reuseFailAlloc_777_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(2u);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v___x_772_);
lean_ctor_set(v___x_650_, 3, v_r_646_);
lean_ctor_set(v___x_650_, 2, v_v_770_);
lean_ctor_set(v___x_650_, 1, v_k_769_);
lean_ctor_set(v___x_650_, 0, v___x_773_);
v___x_775_ = v___x_650_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v___x_772_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
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
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_r_646_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_943_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_r_465_, 2);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_r_465_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_947_);
v___x_791_ = v_r_465_;
v_isShared_792_ = v_isSharedCheck_942_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_r_465_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_942_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v_tree_794_; 
v___x_793_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_643_, v_v_644_, v_l_645_, v_r_646_);
v_tree_794_ = lean_ctor_get(v___x_793_, 2);
lean_inc(v_tree_794_);
if (lean_obj_tag(v_tree_794_) == 0)
{
lean_object* v_k_795_; lean_object* v_v_796_; lean_object* v_size_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_k_795_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_k_795_);
v_v_796_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_v_796_);
lean_dec_ref(v___x_793_);
v_size_797_ = lean_ctor_get(v_tree_794_, 0);
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_nat_mul(v___x_798_, v_size_797_);
v___x_800_ = lean_nat_dec_lt(v___x_799_, v_size_637_);
lean_dec(v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_r_641_);
v___x_801_ = lean_nat_add(v___x_647_, v_size_637_);
v___x_802_ = lean_nat_add(v___x_801_, v_size_797_);
lean_dec(v___x_801_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_tree_794_);
lean_ctor_set(v___x_791_, 3, v_l_464_);
lean_ctor_set(v___x_791_, 2, v_v_796_);
lean_ctor_set(v___x_791_, 1, v_k_795_);
lean_ctor_set(v___x_791_, 0, v___x_802_);
v___x_804_ = v___x_791_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_tree_794_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_l_640_);
lean_inc(v_v_639_);
lean_inc(v_k_638_);
lean_inc(v_size_637_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_872_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_l_464_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_l_464_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_876_);
v___x_807_ = v_l_464_;
v_isShared_808_ = v_isSharedCheck_871_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_l_464_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_871_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_size_809_; lean_object* v_size_810_; lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v_l_813_; lean_object* v_r_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_size_809_ = lean_ctor_get(v_l_640_, 0);
v_size_810_ = lean_ctor_get(v_r_641_, 0);
v_k_811_ = lean_ctor_get(v_r_641_, 1);
v_v_812_ = lean_ctor_get(v_r_641_, 2);
v_l_813_ = lean_ctor_get(v_r_641_, 3);
v_r_814_ = lean_ctor_get(v_r_641_, 4);
v___x_815_ = lean_unsigned_to_nat(2u);
v___x_816_ = lean_nat_mul(v___x_815_, v_size_809_);
v___x_817_ = lean_nat_dec_lt(v_size_810_, v___x_816_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_855_; 
lean_inc(v_r_814_);
lean_inc(v_l_813_);
lean_inc(v_v_812_);
lean_inc(v_k_811_);
lean_del_object(v___x_807_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_r_641_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_856_ = lean_ctor_get(v_r_641_, 4);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_r_641_, 3);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_r_641_, 2);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_r_641_, 1);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_r_641_, 0);
lean_dec(v_unused_860_);
v___x_819_ = v_r_641_;
v_isShared_820_ = v_isSharedCheck_855_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_r_641_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_855_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___x_843_; lean_object* v___y_845_; 
v___x_821_ = lean_nat_add(v___x_647_, v_size_637_);
lean_dec(v_size_637_);
v___x_822_ = lean_nat_add(v___x_821_, v_size_797_);
lean_dec(v___x_821_);
v___x_843_ = lean_nat_add(v___x_647_, v_size_809_);
if (lean_obj_tag(v_l_813_) == 0)
{
lean_object* v_size_853_; 
v_size_853_ = lean_ctor_get(v_l_813_, 0);
lean_inc(v_size_853_);
v___y_845_ = v_size_853_;
goto v___jp_844_;
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___y_845_ = v___x_854_;
goto v___jp_844_;
}
v___jp_823_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_nat_add(v___y_824_, v___y_826_);
lean_dec(v___y_826_);
lean_dec(v___y_824_);
lean_inc_ref(v_tree_794_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_tree_794_);
lean_ctor_set(v___x_819_, 3, v_r_814_);
lean_ctor_set(v___x_819_, 2, v_v_796_);
lean_ctor_set(v___x_819_, 1, v_k_795_);
lean_ctor_set(v___x_819_, 0, v___x_827_);
v___x_829_ = v___x_819_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_r_814_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_tree_794_);
v___x_829_ = v_reuseFailAlloc_842_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_isSharedCheck_836_ = !lean_is_exclusive(v_tree_794_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_837_ = lean_ctor_get(v_tree_794_, 4);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_tree_794_, 3);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_tree_794_, 2);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_tree_794_, 1);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_tree_794_, 0);
lean_dec(v_unused_841_);
v___x_831_ = v_tree_794_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_tree_794_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v___x_829_);
lean_ctor_set(v___x_831_, 3, v___y_825_);
lean_ctor_set(v___x_831_, 2, v_v_812_);
lean_ctor_set(v___x_831_, 1, v_k_811_);
lean_ctor_set(v___x_831_, 0, v___x_822_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v___y_825_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v___x_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_nat_add(v___x_843_, v___y_845_);
lean_dec(v___y_845_);
lean_dec(v___x_843_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_l_813_);
lean_ctor_set(v___x_791_, 3, v_l_640_);
lean_ctor_set(v___x_791_, 2, v_v_639_);
lean_ctor_set(v___x_791_, 1, v_k_638_);
lean_ctor_set(v___x_791_, 0, v___x_846_);
v___x_848_ = v___x_791_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_l_813_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; 
v___x_849_ = lean_nat_add(v___x_647_, v_size_797_);
if (lean_obj_tag(v_r_814_) == 0)
{
lean_object* v_size_850_; 
v_size_850_ = lean_ctor_get(v_r_814_, 0);
lean_inc(v_size_850_);
v___y_824_ = v___x_849_;
v___y_825_ = v___x_848_;
v___y_826_ = v_size_850_;
goto v___jp_823_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___y_824_ = v___x_849_;
v___y_825_ = v___x_848_;
v___y_826_ = v___x_851_;
goto v___jp_823_;
}
}
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_861_ = lean_nat_add(v___x_647_, v_size_637_);
lean_dec(v_size_637_);
v___x_862_ = lean_nat_add(v___x_861_, v_size_797_);
lean_dec(v___x_861_);
v___x_863_ = lean_nat_add(v___x_647_, v_size_797_);
v___x_864_ = lean_nat_add(v___x_863_, v_size_810_);
lean_dec(v___x_863_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_tree_794_);
lean_ctor_set(v___x_791_, 3, v_r_641_);
lean_ctor_set(v___x_791_, 2, v_v_796_);
lean_ctor_set(v___x_791_, 1, v_k_795_);
lean_ctor_set(v___x_791_, 0, v___x_864_);
v___x_866_ = v___x_791_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_r_641_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_tree_794_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___x_866_);
lean_ctor_set(v___x_807_, 0, v___x_862_);
v___x_868_ = v___x_807_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_640_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_900_; 
lean_inc_ref(v_l_640_);
lean_inc(v_v_639_);
lean_inc(v_k_638_);
lean_inc(v_size_637_);
v_isSharedCheck_900_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_901_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_l_464_, 2);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_l_464_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_905_);
v___x_878_ = v_l_464_;
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
else
{
lean_dec(v_l_464_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
if (lean_obj_tag(v_r_641_) == 0)
{
lean_object* v_k_880_; lean_object* v_v_881_; lean_object* v_size_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_k_880_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_k_880_);
v_v_881_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_v_881_);
lean_dec_ref(v___x_793_);
v_size_882_ = lean_ctor_get(v_r_641_, 0);
v___x_883_ = lean_nat_add(v___x_647_, v_size_637_);
lean_dec(v_size_637_);
v___x_884_ = lean_nat_add(v___x_647_, v_size_882_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_tree_794_);
lean_ctor_set(v___x_791_, 3, v_r_641_);
lean_ctor_set(v___x_791_, 2, v_v_881_);
lean_ctor_set(v___x_791_, 1, v_k_880_);
lean_ctor_set(v___x_791_, 0, v___x_884_);
v___x_886_ = v___x_791_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_r_641_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_tree_794_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 4, v___x_886_);
lean_ctor_set(v___x_878_, 0, v___x_883_);
v___x_888_ = v___x_878_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
lean_dec(v_size_637_);
v_k_891_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_k_891_);
v_v_892_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_v_892_);
lean_dec_ref(v___x_793_);
v___x_893_ = lean_unsigned_to_nat(3u);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_r_641_);
lean_ctor_set(v___x_791_, 3, v_r_641_);
lean_ctor_set(v___x_791_, 2, v_v_892_);
lean_ctor_set(v___x_791_, 1, v_k_891_);
lean_ctor_set(v___x_791_, 0, v___x_647_);
v___x_895_ = v___x_791_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_r_641_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_r_641_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 4, v___x_895_);
lean_ctor_set(v___x_878_, 0, v___x_893_);
v___x_897_ = v___x_878_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_641_) == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_930_; 
lean_inc(v_l_640_);
lean_inc(v_v_639_);
lean_inc(v_k_638_);
v_isSharedCheck_930_ = !lean_is_exclusive(v_l_464_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_931_ = lean_ctor_get(v_l_464_, 4);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_l_464_, 3);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_l_464_, 2);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_l_464_, 1);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_l_464_, 0);
lean_dec(v_unused_935_);
v___x_907_ = v_l_464_;
v_isShared_908_ = v_isSharedCheck_930_;
goto v_resetjp_906_;
}
else
{
lean_dec(v_l_464_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_930_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_k_909_; lean_object* v_v_910_; lean_object* v_k_911_; lean_object* v_v_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v_k_909_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_k_909_);
v_v_910_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_v_910_);
lean_dec_ref(v___x_793_);
v_k_911_ = lean_ctor_get(v_r_641_, 1);
v_v_912_ = lean_ctor_get(v_r_641_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_r_641_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_927_ = lean_ctor_get(v_r_641_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_r_641_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_r_641_, 0);
lean_dec(v_unused_929_);
v___x_914_ = v_r_641_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_v_912_);
lean_inc(v_k_911_);
lean_dec(v_r_641_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_unsigned_to_nat(3u);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 4, v_l_640_);
lean_ctor_set(v___x_914_, 3, v_l_640_);
lean_ctor_set(v___x_914_, 2, v_v_639_);
lean_ctor_set(v___x_914_, 1, v_k_638_);
lean_ctor_set(v___x_914_, 0, v___x_647_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_l_640_);
v___x_918_ = v_reuseFailAlloc_925_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_l_640_);
lean_ctor_set(v___x_791_, 3, v_l_640_);
lean_ctor_set(v___x_791_, 2, v_v_910_);
lean_ctor_set(v___x_791_, 1, v_k_909_);
lean_ctor_set(v___x_791_, 0, v___x_647_);
v___x_920_ = v___x_791_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_909_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_910_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_l_640_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_l_640_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 4, v___x_920_);
lean_ctor_set(v___x_907_, 3, v___x_918_);
lean_ctor_set(v___x_907_, 2, v_v_912_);
lean_ctor_set(v___x_907_, 1, v_k_911_);
lean_ctor_set(v___x_907_, 0, v___x_916_);
v___x_922_ = v___x_907_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_911_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_912_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
else
{
lean_object* v_k_936_; lean_object* v_v_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_k_936_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_k_936_);
v_v_937_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_v_937_);
lean_dec_ref(v___x_793_);
v___x_938_ = lean_unsigned_to_nat(2u);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_r_641_);
lean_ctor_set(v___x_791_, 3, v_l_464_);
lean_ctor_set(v___x_791_, 2, v_v_937_);
lean_ctor_set(v___x_791_, 1, v_k_936_);
lean_ctor_set(v___x_791_, 0, v___x_938_);
v___x_940_ = v___x_791_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_936_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_937_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_464_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_r_641_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
else
{
return v_l_464_;
}
}
else
{
return v_r_465_;
}
}
}
else
{
lean_object* v_impl_948_; lean_object* v___x_949_; 
v_impl_948_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_460_, v_l_464_);
v___x_949_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_948_) == 0)
{
if (lean_obj_tag(v_r_465_) == 0)
{
lean_object* v_size_950_; lean_object* v_size_951_; lean_object* v_k_952_; lean_object* v_v_953_; lean_object* v_l_954_; lean_object* v_r_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_size_950_ = lean_ctor_get(v_impl_948_, 0);
v_size_951_ = lean_ctor_get(v_r_465_, 0);
v_k_952_ = lean_ctor_get(v_r_465_, 1);
v_v_953_ = lean_ctor_get(v_r_465_, 2);
v_l_954_ = lean_ctor_get(v_r_465_, 3);
lean_inc(v_l_954_);
v_r_955_ = lean_ctor_get(v_r_465_, 4);
v___x_956_ = lean_unsigned_to_nat(3u);
v___x_957_ = lean_nat_mul(v___x_956_, v_size_950_);
v___x_958_ = lean_nat_dec_lt(v___x_957_, v_size_951_);
lean_dec(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec(v_l_954_);
v___x_959_ = lean_nat_add(v___x_949_, v_size_950_);
v___x_960_ = lean_nat_add(v___x_959_, v_size_951_);
lean_dec(v___x_959_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 3, v_impl_948_);
lean_ctor_set(v___x_467_, 0, v___x_960_);
v___x_962_ = v___x_467_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_impl_948_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_r_465_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1027_; 
lean_inc(v_r_955_);
lean_inc(v_v_953_);
lean_inc(v_k_952_);
lean_inc(v_size_951_);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; lean_object* v_unused_1032_; 
v_unused_1028_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_r_465_, 2);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_r_465_, 1);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_1032_);
v___x_965_ = v_r_465_;
v_isShared_966_ = v_isSharedCheck_1027_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_r_465_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1027_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_size_967_; lean_object* v_k_968_; lean_object* v_v_969_; lean_object* v_l_970_; lean_object* v_r_971_; lean_object* v_size_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_size_967_ = lean_ctor_get(v_l_954_, 0);
v_k_968_ = lean_ctor_get(v_l_954_, 1);
v_v_969_ = lean_ctor_get(v_l_954_, 2);
v_l_970_ = lean_ctor_get(v_l_954_, 3);
v_r_971_ = lean_ctor_get(v_l_954_, 4);
v_size_972_ = lean_ctor_get(v_r_955_, 0);
v___x_973_ = lean_unsigned_to_nat(2u);
v___x_974_ = lean_nat_mul(v___x_973_, v_size_972_);
v___x_975_ = lean_nat_dec_lt(v_size_967_, v___x_974_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1003_; 
lean_inc(v_r_971_);
lean_inc(v_l_970_);
lean_inc(v_v_969_);
lean_inc(v_k_968_);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_l_954_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1004_ = lean_ctor_get(v_l_954_, 4);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_l_954_, 3);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_l_954_, 2);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_l_954_, 1);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_l_954_, 0);
lean_dec(v_unused_1008_);
v___x_977_ = v_l_954_;
v_isShared_978_ = v_isSharedCheck_1003_;
goto v_resetjp_976_;
}
else
{
lean_dec(v_l_954_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1003_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_993_; 
v___x_979_ = lean_nat_add(v___x_949_, v_size_950_);
v___x_980_ = lean_nat_add(v___x_979_, v_size_951_);
lean_dec(v_size_951_);
if (lean_obj_tag(v_l_970_) == 0)
{
lean_object* v_size_1001_; 
v_size_1001_ = lean_ctor_get(v_l_970_, 0);
lean_inc(v_size_1001_);
v___y_993_ = v_size_1001_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___y_993_ = v___x_1002_;
goto v___jp_992_;
}
v___jp_981_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_nat_add(v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec(v___y_983_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v_r_955_);
lean_ctor_set(v___x_977_, 3, v_r_971_);
lean_ctor_set(v___x_977_, 2, v_v_953_);
lean_ctor_set(v___x_977_, 1, v_k_952_);
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_952_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_953_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_r_971_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_r_955_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v___x_987_);
lean_ctor_set(v___x_965_, 3, v___y_982_);
lean_ctor_set(v___x_965_, 2, v_v_969_);
lean_ctor_set(v___x_965_, 1, v_k_968_);
lean_ctor_set(v___x_965_, 0, v___x_980_);
v___x_989_ = v___x_965_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_968_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_969_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v___y_982_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_nat_add(v___x_979_, v___y_993_);
lean_dec(v___y_993_);
lean_dec(v___x_979_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_l_970_);
lean_ctor_set(v___x_467_, 3, v_impl_948_);
lean_ctor_set(v___x_467_, 0, v___x_994_);
v___x_996_ = v___x_467_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_impl_948_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_l_970_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = lean_nat_add(v___x_949_, v_size_972_);
if (lean_obj_tag(v_r_971_) == 0)
{
lean_object* v_size_998_; 
v_size_998_ = lean_ctor_get(v_r_971_, 0);
lean_inc(v_size_998_);
v___y_982_ = v___x_996_;
v___y_983_ = v___x_997_;
v___y_984_ = v_size_998_;
goto v___jp_981_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___y_982_ = v___x_996_;
v___y_983_ = v___x_997_;
v___y_984_ = v___x_999_;
goto v___jp_981_;
}
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_del_object(v___x_467_);
v___x_1009_ = lean_nat_add(v___x_949_, v_size_950_);
v___x_1010_ = lean_nat_add(v___x_1009_, v_size_951_);
lean_dec(v_size_951_);
v___x_1011_ = lean_nat_add(v___x_1009_, v_size_967_);
lean_dec(v___x_1009_);
lean_inc_ref(v_impl_948_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_l_954_);
lean_ctor_set(v___x_965_, 3, v_impl_948_);
lean_ctor_set(v___x_965_, 2, v_v_463_);
lean_ctor_set(v___x_965_, 1, v_k_462_);
lean_ctor_set(v___x_965_, 0, v___x_1011_);
v___x_1013_ = v___x_965_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_impl_948_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_l_954_);
v___x_1013_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v_impl_948_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; 
v_unused_1021_ = lean_ctor_get(v_impl_948_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_impl_948_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_impl_948_, 2);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_impl_948_, 1);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_impl_948_, 0);
lean_dec(v_unused_1025_);
v___x_1015_ = v_impl_948_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_dec(v_impl_948_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 4, v_r_955_);
lean_ctor_set(v___x_1015_, 3, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v_v_953_);
lean_ctor_set(v___x_1015_, 1, v_k_952_);
lean_ctor_set(v___x_1015_, 0, v___x_1010_);
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_952_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_953_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_r_955_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v_size_1033_ = lean_ctor_get(v_impl_948_, 0);
v___x_1034_ = lean_nat_add(v___x_949_, v_size_1033_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 3, v_impl_948_);
lean_ctor_set(v___x_467_, 0, v___x_1034_);
v___x_1036_ = v___x_467_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_impl_948_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_r_465_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
if (lean_obj_tag(v_r_465_) == 0)
{
lean_object* v_l_1038_; 
v_l_1038_ = lean_ctor_get(v_r_465_, 3);
lean_inc(v_l_1038_);
if (lean_obj_tag(v_l_1038_) == 0)
{
lean_object* v_r_1039_; 
v_r_1039_ = lean_ctor_get(v_r_465_, 4);
lean_inc(v_r_1039_);
if (lean_obj_tag(v_r_1039_) == 0)
{
lean_object* v_size_1040_; lean_object* v_k_1041_; lean_object* v_v_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1055_; 
v_size_1040_ = lean_ctor_get(v_r_465_, 0);
v_k_1041_ = lean_ctor_get(v_r_465_, 1);
v_v_1042_ = lean_ctor_get(v_r_465_, 2);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; lean_object* v_unused_1057_; 
v_unused_1056_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_1057_);
v___x_1044_ = v_r_465_;
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_v_1042_);
lean_inc(v_k_1041_);
lean_inc(v_size_1040_);
lean_dec(v_r_465_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_size_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_size_1046_ = lean_ctor_get(v_l_1038_, 0);
v___x_1047_ = lean_nat_add(v___x_949_, v_size_1040_);
lean_dec(v_size_1040_);
v___x_1048_ = lean_nat_add(v___x_949_, v_size_1046_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v_l_1038_);
lean_ctor_set(v___x_1044_, 3, v_impl_948_);
lean_ctor_set(v___x_1044_, 2, v_v_463_);
lean_ctor_set(v___x_1044_, 1, v_k_462_);
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_impl_948_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_l_1038_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_r_1039_);
lean_ctor_set(v___x_467_, 3, v___x_1050_);
lean_ctor_set(v___x_467_, 2, v_v_1042_);
lean_ctor_set(v___x_467_, 1, v_k_1041_);
lean_ctor_set(v___x_467_, 0, v___x_1047_);
v___x_1052_ = v___x_467_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_1041_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_1042_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_r_1039_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_k_1058_; lean_object* v_v_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1082_; 
v_k_1058_ = lean_ctor_get(v_r_465_, 1);
v_v_1059_ = lean_ctor_get(v_r_465_, 2);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; 
v_unused_1083_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_1085_);
v___x_1061_ = v_r_465_;
v_isShared_1062_ = v_isSharedCheck_1082_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_v_1059_);
lean_inc(v_k_1058_);
lean_dec(v_r_465_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1082_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_k_1063_; lean_object* v_v_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1078_; 
v_k_1063_ = lean_ctor_get(v_l_1038_, 1);
v_v_1064_ = lean_ctor_get(v_l_1038_, 2);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_l_1038_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; lean_object* v_unused_1080_; lean_object* v_unused_1081_; 
v_unused_1079_ = lean_ctor_get(v_l_1038_, 4);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_l_1038_, 3);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_l_1038_, 0);
lean_dec(v_unused_1081_);
v___x_1066_ = v_l_1038_;
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_v_1064_);
lean_inc(v_k_1063_);
lean_dec(v_l_1038_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_unsigned_to_nat(3u);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 4, v_r_1039_);
lean_ctor_set(v___x_1066_, 3, v_r_1039_);
lean_ctor_set(v___x_1066_, 2, v_v_463_);
lean_ctor_set(v___x_1066_, 1, v_k_462_);
lean_ctor_set(v___x_1066_, 0, v___x_949_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_r_1039_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_r_1039_);
v___x_1070_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 3, v_r_1039_);
lean_ctor_set(v___x_1061_, 0, v___x_949_);
v___x_1072_ = v___x_1061_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_1058_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_1059_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_r_1039_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_r_1039_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_1072_);
lean_ctor_set(v___x_467_, 3, v___x_1070_);
lean_ctor_set(v___x_467_, 2, v_v_1064_);
lean_ctor_set(v___x_467_, 1, v_k_1063_);
lean_ctor_set(v___x_467_, 0, v___x_1068_);
v___x_1074_ = v___x_467_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_1063_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1086_; 
v_r_1086_ = lean_ctor_get(v_r_465_, 4);
lean_inc(v_r_1086_);
if (lean_obj_tag(v_r_1086_) == 0)
{
lean_object* v_k_1087_; lean_object* v_v_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1099_; 
v_k_1087_ = lean_ctor_get(v_r_465_, 1);
v_v_1088_ = lean_ctor_get(v_r_465_, 2);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1100_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_r_465_, 0);
lean_dec(v_unused_1102_);
v___x_1090_ = v_r_465_;
v_isShared_1091_ = v_isSharedCheck_1099_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_v_1088_);
lean_inc(v_k_1087_);
lean_dec(v_r_465_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1099_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_unsigned_to_nat(3u);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v_l_1038_);
lean_ctor_set(v___x_1090_, 2, v_v_463_);
lean_ctor_set(v___x_1090_, 1, v_k_462_);
lean_ctor_set(v___x_1090_, 0, v___x_949_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_l_1038_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_l_1038_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v_r_1086_);
lean_ctor_set(v___x_467_, 3, v___x_1094_);
lean_ctor_set(v___x_467_, 2, v_v_1088_);
lean_ctor_set(v___x_467_, 1, v_k_1087_);
lean_ctor_set(v___x_467_, 0, v___x_1092_);
v___x_1096_ = v___x_467_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_r_1086_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_size_1103_; lean_object* v_k_1104_; lean_object* v_v_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1116_; 
v_size_1103_ = lean_ctor_get(v_r_465_, 0);
v_k_1104_ = lean_ctor_get(v_r_465_, 1);
v_v_1105_ = lean_ctor_get(v_r_465_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_r_465_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1117_ = lean_ctor_get(v_r_465_, 4);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_465_, 3);
lean_dec(v_unused_1118_);
v___x_1107_ = v_r_465_;
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_v_1105_);
lean_inc(v_k_1104_);
lean_inc(v_size_1103_);
lean_dec(v_r_465_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 3, v_r_1086_);
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_size_1103_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_1104_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_1105_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_r_1086_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_r_1086_);
v___x_1110_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(2u);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_1110_);
lean_ctor_set(v___x_467_, 3, v_r_1086_);
lean_ctor_set(v___x_467_, 0, v___x_1111_);
v___x_1113_ = v___x_467_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_r_1086_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v___x_1110_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v___x_1120_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 3, v_r_465_);
lean_ctor_set(v___x_467_, 0, v___x_949_);
v___x_1120_ = v___x_467_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_r_465_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_r_465_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
else
{
return v_t_461_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_460_ = stack[0].m_num;
lean_object* v_t_461_ = stack[1].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_460_, v_t_461_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object* v_k_1125_, lean_object* v_t_1126_){
_start:
{
uint64_t v_k_boxed_1127_; lean_object* v_res_1128_; 
v_k_boxed_1127_ = lean_unbox_uint64(v_k_1125_);
lean_dec_ref(v_k_1125_);
v_res_1128_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_1127_, v_t_1126_);
return v_res_1128_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object* v_t_1129_, uint64_t v_k_1130_){
_start:
{
if (lean_obj_tag(v_t_1129_) == 0)
{
lean_object* v_k_1131_; lean_object* v_v_1132_; lean_object* v_l_1133_; lean_object* v_r_1134_; uint64_t v___x_1135_; uint8_t v___x_1136_; 
v_k_1131_ = lean_ctor_get(v_t_1129_, 1);
v_v_1132_ = lean_ctor_get(v_t_1129_, 2);
v_l_1133_ = lean_ctor_get(v_t_1129_, 3);
v_r_1134_ = lean_ctor_get(v_t_1129_, 4);
v___x_1135_ = lean_unbox_uint64(v_k_1131_);
v___x_1136_ = lean_uint64_dec_lt(v_k_1130_, v___x_1135_);
if (v___x_1136_ == 0)
{
uint64_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_unbox_uint64(v_k_1131_);
v___x_1138_ = lean_uint64_dec_eq(v_k_1130_, v___x_1137_);
if (v___x_1138_ == 0)
{
v_t_1129_ = v_r_1134_;
goto _start;
}
else
{
lean_object* v___x_1140_; 
lean_inc(v_v_1132_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_v_1132_);
return v___x_1140_;
}
}
else
{
v_t_1129_ = v_l_1133_;
goto _start;
}
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1129_ = stack[0].m_obj;
uint64_t v_k_1130_ = stack[1].m_num;
lean_object* v_res_1143_;
v_res_1143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1129_, v_k_1130_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object* v_t_1144_, lean_object* v_k_1145_){
_start:
{
uint64_t v_k_boxed_1146_; lean_object* v_res_1147_; 
v_k_boxed_1146_ = lean_unbox_uint64(v_k_1145_);
lean_dec_ref(v_k_1145_);
v_res_1147_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1144_, v_k_boxed_1146_);
lean_dec(v_t_1144_);
return v_res_1147_;
}
}
lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object* v_state_1148_, uint64_t v_id_1149_, lean_object* v_reason_1150_){
_start:
{
lean_object* v_tokens_1152_; lean_object* v___x_1153_; 
v_tokens_1152_ = lean_ctor_get(v_state_1148_, 0);
v___x_1153_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1152_, v_id_1149_);
if (lean_obj_tag(v___x_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; size_t v_sz_1157_; size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_tokens_1161_; uint64_t v_id_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_val_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v_fst_1155_ = lean_ctor_get(v_val_1154_, 0);
lean_inc(v_fst_1155_);
v_snd_1156_ = lean_ctor_get(v_val_1154_, 1);
lean_inc(v_snd_1156_);
lean_dec(v_val_1154_);
v_sz_1157_ = lean_array_size(v_snd_1156_);
v___x_1158_ = ((size_t)0ULL);
lean_inc(v_reason_1150_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1150_, v_snd_1156_, v_sz_1157_, v___x_1158_, v_state_1148_);
lean_dec(v_snd_1156_);
v___x_1160_ = l_Std_CancellationToken_cancel(v_fst_1155_, v_reason_1150_);
v_tokens_1161_ = lean_ctor_get(v___x_1159_, 0);
v_id_1162_ = lean_ctor_get_uint64(v___x_1159_, sizeof(void*)*1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v___x_1159_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_tokens_1161_);
lean_dec(v___x_1159_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_1149_, v_tokens_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set_uint64(v_reuseFailAlloc_1169_, sizeof(void*)*1, v_id_1162_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_dec(v___x_1153_);
lean_dec(v_reason_1150_);
return v_state_1148_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_1148_ = stack[0].m_obj;
uint64_t v_id_1149_ = stack[1].m_num;
lean_object* v_reason_1150_ = stack[2].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_state_1148_, v_id_1149_, v_reason_1150_);
stack->m_obj
 = v_res_1171_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object* v_reason_1172_, lean_object* v_as_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_b_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1178_ == 0)
{
lean_dec(v_reason_1172_);
return v_b_1176_;
}
else
{
lean_object* v_a_1179_; uint64_t v___x_1180_; lean_object* v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; 
v_a_1179_ = lean_array_uget_borrowed(v_as_1173_, v_i_1175_);
v___x_1180_ = lean_unbox_uint64(v_a_1179_);
lean_inc(v_reason_1172_);
v___x_1181_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_b_1176_, v___x_1180_, v_reason_1172_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1175_, v___x_1182_);
v_i_1175_ = v___x_1183_;
v_b_1176_ = v___x_1181_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_reason_1172_ = stack[0].m_obj;
lean_object* v_as_1173_ = stack[1].m_obj;
size_t v_sz_1174_ = stack[2].m_num;
size_t v_i_1175_ = stack[3].m_num;
lean_object* v_b_1176_ = stack[4].m_obj;
lean_object* v_res_1185_;
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1172_, v_as_1173_, v_sz_1174_, v_i_1175_, v_b_1176_);
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object* v_reason_1186_, lean_object* v_as_1187_, lean_object* v_sz_1188_, lean_object* v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1188_);
lean_dec(v_sz_1188_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1186_, v_as_1187_, v_sz_boxed_1192_, v_i_boxed_1193_, v_b_1190_);
lean_dec_ref(v_as_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object* v_state_1195_, lean_object* v_id_1196_, lean_object* v_reason_1197_, lean_object* v_a_1198_){
_start:
{
uint64_t v_id_boxed_1199_; lean_object* v_res_1200_; 
v_id_boxed_1199_ = lean_unbox_uint64(v_id_1196_);
lean_dec_ref(v_id_1196_);
v_res_1200_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_state_1195_, v_id_boxed_1199_, v_reason_1197_);
return v_res_1200_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object* v_00_u03b4_1201_, lean_object* v_t_1202_, uint64_t v_k_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1202_, v_k_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1202_ = stack[1].m_obj;
uint64_t v_k_1203_ = stack[2].m_num;
lean_object* v_res_1205_;
v_res_1205_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_box(0), v_t_1202_, v_k_1203_);
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object* v_00_u03b4_1206_, lean_object* v_t_1207_, lean_object* v_k_1208_){
_start:
{
uint64_t v_k_boxed_1209_; lean_object* v_res_1210_; 
v_k_boxed_1209_ = lean_unbox_uint64(v_k_1208_);
lean_dec_ref(v_k_1208_);
v_res_1210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_1206_, v_t_1207_, v_k_boxed_1209_);
lean_dec(v_t_1207_);
return v_res_1210_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object* v_00_u03b2_1211_, uint64_t v_k_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1212_, v_t_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_1212_ = stack[1].m_num;
lean_object* v_t_1213_ = stack[2].m_obj;
lean_object* v_res_1216_;
v_res_1216_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_box(0), v_k_1212_, v_t_1213_, lean_box(0));
stack->m_obj
 = v_res_1216_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object* v_00_u03b2_1217_, lean_object* v_k_1218_, lean_object* v_t_1219_, lean_object* v_h_1220_){
_start:
{
uint64_t v_k_boxed_1221_; lean_object* v_res_1222_; 
v_k_boxed_1221_ = lean_unbox_uint64(v_k_1218_);
lean_dec_ref(v_k_1218_);
v_res_1222_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_1217_, v_k_boxed_1221_, v_t_1219_, v_h_1220_);
return v_res_1222_;
}
}
lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(lean_object* v_xs_1223_, uint64_t v_v_1224_, lean_object* v_i_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_get_size(v_xs_1223_);
v___x_1227_ = lean_nat_dec_lt(v_i_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec(v_i_1225_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; uint64_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = lean_array_fget_borrowed(v_xs_1223_, v_i_1225_);
v___x_1230_ = lean_unbox_uint64(v___x_1229_);
v___x_1231_ = lean_uint64_dec_eq(v___x_1230_, v_v_1224_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_i_1225_, v___x_1232_);
lean_dec(v_i_1225_);
v_i_1225_ = v___x_1233_;
goto _start;
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_i_1225_);
return v___x_1235_;
}
}
}
}
LEAN_EXPORT void l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1223_ = stack[0].m_obj;
uint64_t v_v_1224_ = stack[1].m_num;
lean_object* v_i_1225_ = stack[2].m_obj;
lean_object* v_res_1236_;
v_res_1236_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(v_xs_1223_, v_v_1224_, v_i_1225_);
stack->m_obj
 = v_res_1236_;
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_1237_, lean_object* v_v_1238_, lean_object* v_i_1239_){
_start:
{
uint64_t v_v_boxed_1240_; lean_object* v_res_1241_; 
v_v_boxed_1240_ = lean_unbox_uint64(v_v_1238_);
lean_dec_ref(v_v_1238_);
v_res_1241_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(v_xs_1237_, v_v_boxed_1240_, v_i_1239_);
lean_dec_ref(v_xs_1237_);
return v_res_1241_;
}
}
lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(lean_object* v_xs_1242_, uint64_t v_v_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(v_xs_1242_, v_v_1243_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT void l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1242_ = stack[0].m_obj;
uint64_t v_v_1243_ = stack[1].m_num;
lean_object* v_res_1246_;
v_res_1246_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(v_xs_1242_, v_v_1243_);
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0___boxed(lean_object* v_xs_1247_, lean_object* v_v_1248_){
_start:
{
uint64_t v_v_boxed_1249_; lean_object* v_res_1250_; 
v_v_boxed_1249_ = lean_unbox_uint64(v_v_1248_);
lean_dec_ref(v_v_1248_);
v_res_1250_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(v_xs_1247_, v_v_boxed_1249_);
lean_dec_ref(v_xs_1247_);
return v_res_1250_;
}
}
lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(lean_object* v_as_1251_, uint64_t v_a_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(v_as_1251_, v_a_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
return v_as_1251_;
}
else
{
lean_object* v_val_1254_; lean_object* v___x_1255_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = l_Array_eraseIdx___redArg(v_as_1251_, v_val_1254_);
return v___x_1255_;
}
}
}
LEAN_EXPORT void l_Array_erase___at___00Std_CancellationContext_cancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1251_ = stack[0].m_obj;
uint64_t v_a_1252_ = stack[1].m_num;
lean_object* v_res_1256_;
v_res_1256_ = l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(v_as_1251_, v_a_1252_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0___boxed(lean_object* v_as_1257_, lean_object* v_a_1258_){
_start:
{
uint64_t v_a_boxed_1259_; lean_object* v_res_1260_; 
v_a_boxed_1259_ = lean_unbox_uint64(v_a_1258_);
lean_dec_ref(v_a_1258_);
v_res_1260_ = l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(v_as_1257_, v_a_boxed_1259_);
return v_res_1260_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(uint64_t v___x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(v_x_1262_, v___x_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_1261_ = stack[0].m_num;
lean_object* v_x_1262_ = stack[1].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(v___x_1261_, v_x_1262_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1___boxed(lean_object* v___x_1265_, lean_object* v_x_1266_){
_start:
{
uint64_t v___x_860__boxed_1267_; lean_object* v_res_1268_; 
v___x_860__boxed_1267_ = lean_unbox_uint64(v___x_1265_);
lean_dec_ref(v___x_1265_);
v_res_1268_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(v___x_860__boxed_1267_, v_x_1266_);
return v_res_1268_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(uint64_t v___x_1269_, uint64_t v_k_1270_, lean_object* v_t_1271_){
_start:
{
if (lean_obj_tag(v_t_1271_) == 0)
{
lean_object* v_size_1272_; lean_object* v_k_1273_; lean_object* v_v_1274_; lean_object* v_l_1275_; lean_object* v_r_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1300_; 
v_size_1272_ = lean_ctor_get(v_t_1271_, 0);
v_k_1273_ = lean_ctor_get(v_t_1271_, 1);
v_v_1274_ = lean_ctor_get(v_t_1271_, 2);
v_l_1275_ = lean_ctor_get(v_t_1271_, 3);
v_r_1276_ = lean_ctor_get(v_t_1271_, 4);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_t_1271_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1278_ = v_t_1271_;
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_r_1276_);
lean_inc(v_l_1275_);
lean_inc(v_v_1274_);
lean_inc(v_k_1273_);
lean_inc(v_size_1272_);
lean_dec(v_t_1271_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
uint64_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_unbox_uint64(v_k_1273_);
v___x_1281_ = lean_uint64_dec_lt(v_k_1270_, v___x_1280_);
if (v___x_1281_ == 0)
{
uint64_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_unbox_uint64(v_k_1273_);
v___x_1283_ = lean_uint64_dec_eq(v_k_1270_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_1269_, v_k_1270_, v_r_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v___x_1284_);
v___x_1286_ = v___x_1278_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_size_1272_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1273_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1274_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1275_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
lean_dec(v_k_1273_);
v___f_1288_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
v___x_1289_ = lean_box_uint64(v___x_1269_);
v___f_1290_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1290_, 0, v___x_1289_);
v___x_1291_ = l_Prod_map___redArg(v___f_1288_, v___f_1290_, v_v_1274_);
v___x_1292_ = lean_box_uint64(v_k_1270_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 2, v___x_1291_);
lean_ctor_set(v___x_1278_, 1, v___x_1292_);
v___x_1294_ = v___x_1278_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_size_1272_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_l_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_r_1276_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_1269_, v_k_1270_, v_l_1275_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 3, v___x_1296_);
v___x_1298_ = v___x_1278_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_size_1272_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_k_1273_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_v_1274_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_r_1276_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
return v_t_1271_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_1269_ = stack[0].m_num;
uint64_t v_k_1270_ = stack[1].m_num;
lean_object* v_t_1271_ = stack[2].m_obj;
lean_object* v_res_1301_;
v_res_1301_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_1269_, v_k_1270_, v_t_1271_);
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___boxed(lean_object* v___x_1302_, lean_object* v_k_1303_, lean_object* v_t_1304_){
_start:
{
uint64_t v___x_874__boxed_1305_; uint64_t v_k_boxed_1306_; lean_object* v_res_1307_; 
v___x_874__boxed_1305_ = lean_unbox_uint64(v___x_1302_);
lean_dec_ref(v___x_1302_);
v_k_boxed_1306_ = lean_unbox_uint64(v_k_1303_);
lean_dec_ref(v_k_1303_);
v_res_1307_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_874__boxed_1305_, v_k_boxed_1306_, v_t_1304_);
return v_res_1307_;
}
}
lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t v_id_1308_, lean_object* v_reason_1309_, lean_object* v_parent_x3f_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___y_1316_; 
v___x_1313_ = lean_st_ref_get(v___y_1311_);
v___x_1314_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v___x_1313_, v_id_1308_, v_reason_1309_);
if (lean_obj_tag(v_parent_x3f_1310_) == 0)
{
v___y_1316_ = v___x_1314_;
goto v___jp_1315_;
}
else
{
lean_object* v_val_1319_; lean_object* v_tokens_1320_; uint64_t v_id_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1330_; 
v_val_1319_ = lean_ctor_get(v_parent_x3f_1310_, 0);
v_tokens_1320_ = lean_ctor_get(v___x_1314_, 0);
v_id_1321_ = lean_ctor_get_uint64(v___x_1314_, sizeof(void*)*1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1323_ = v___x_1314_;
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_tokens_1320_);
lean_dec(v___x_1314_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint64_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = lean_unbox_uint64(v_val_1319_);
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v_id_1308_, v___x_1325_, v_tokens_1320_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
lean_ctor_set_uint64(v_reuseFailAlloc_1329_, sizeof(void*)*1, v_id_1321_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
v___y_1316_ = v___x_1328_;
goto v___jp_1315_;
}
}
}
v___jp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_st_ref_swap(v___y_1311_, v___y_1316_);
lean_dec(v___x_1318_);
return v___x_1317_;
}
}
}
LEAN_EXPORT void l_Std_CancellationContext_cancel___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_id_1308_ = stack[0].m_num;
lean_object* v_reason_1309_ = stack[1].m_obj;
lean_object* v_parent_x3f_1310_ = stack[2].m_obj;
lean_object* v___y_1311_ = stack[3].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l_Std_CancellationContext_cancel___lam__0(v_id_1308_, v_reason_1309_, v_parent_x3f_1310_, v___y_1311_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object* v_id_1332_, lean_object* v_reason_1333_, lean_object* v_parent_x3f_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint64_t v_id_boxed_1337_; lean_object* v_res_1338_; 
v_id_boxed_1337_ = lean_unbox_uint64(v_id_1332_);
lean_dec_ref(v_id_1332_);
v_res_1338_ = l_Std_CancellationContext_cancel___lam__0(v_id_boxed_1337_, v_reason_1333_, v_parent_x3f_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec(v_parent_x3f_1334_);
return v_res_1338_;
}
}
lean_object* l_Std_CancellationContext_cancel(lean_object* v_x_1339_, lean_object* v_reason_1340_){
_start:
{
lean_object* v_state_1342_; lean_object* v_token_1343_; uint64_t v_id_1344_; lean_object* v_parent_x3f_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; uint8_t v___x_1348_; 
v_state_1342_ = lean_ctor_get(v_x_1339_, 0);
lean_inc_ref(v_state_1342_);
v_token_1343_ = lean_ctor_get(v_x_1339_, 1);
lean_inc_ref(v_token_1343_);
v_id_1344_ = lean_ctor_get_uint64(v_x_1339_, sizeof(void*)*3);
v_parent_x3f_1345_ = lean_ctor_get(v_x_1339_, 2);
lean_inc(v_parent_x3f_1345_);
lean_dec_ref(v_x_1339_);
v___x_1346_ = lean_box_uint64(v_id_1344_);
v___f_1347_ = lean_alloc_closure((void*)(l_Std_CancellationContext_cancel___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1347_, 0, v___x_1346_);
lean_closure_set(v___f_1347_, 1, v_reason_1340_);
lean_closure_set(v___f_1347_, 2, v_parent_x3f_1345_);
v___x_1348_ = l_Std_CancellationToken_isCancelled(v_token_1343_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1342_, v___f_1347_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
lean_dec_ref(v___f_1347_);
lean_dec_ref(v_state_1342_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
}
}
LEAN_EXPORT void l_Std_CancellationContext_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1339_ = stack[0].m_obj;
lean_object* v_reason_1340_ = stack[1].m_obj;
lean_object* v_res_1351_;
v_res_1351_ = l_Std_CancellationContext_cancel(v_x_1339_, v_reason_1340_);
stack->m_obj
 = v_res_1351_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object* v_x_1352_, lean_object* v_reason_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_CancellationContext_cancel(v_x_1352_, v_reason_1353_);
return v_res_1355_;
}
}
uint8_t l_Std_CancellationContext_isCancelled(lean_object* v_x_1356_){
_start:
{
lean_object* v_token_1358_; uint8_t v___x_1359_; 
v_token_1358_ = lean_ctor_get(v_x_1356_, 1);
lean_inc_ref(v_token_1358_);
lean_dec_ref(v_x_1356_);
v___x_1359_ = l_Std_CancellationToken_isCancelled(v_token_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_isCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1356_ = stack[0].m_obj;
uint8_t v_res_1360_;
v_res_1360_ = l_Std_CancellationContext_isCancelled(v_x_1356_);
stack->m_num = v_res_1360_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object* v_x_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_res_1363_; lean_object* v_r_1364_; 
v_res_1363_ = l_Std_CancellationContext_isCancelled(v_x_1361_);
v_r_1364_ = lean_box(v_res_1363_);
return v_r_1364_;
}
}
lean_object* l_Std_CancellationContext_getCancellationReason(lean_object* v_x_1365_){
_start:
{
lean_object* v_token_1367_; lean_object* v___x_1368_; 
v_token_1367_ = lean_ctor_get(v_x_1365_, 1);
lean_inc_ref(v_token_1367_);
lean_dec_ref(v_x_1365_);
v___x_1368_ = l_Std_CancellationToken_getCancellationReason(v_token_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_getCancellationReason_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1365_ = stack[0].m_obj;
lean_object* v_res_1369_;
v_res_1369_ = l_Std_CancellationContext_getCancellationReason(v_x_1365_);
stack->m_obj
 = v_res_1369_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object* v_x_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_CancellationContext_getCancellationReason(v_x_1370_);
return v_res_1372_;
}
}
lean_object* l_Std_CancellationContext_done(lean_object* v_x_1373_){
_start:
{
lean_object* v_token_1375_; lean_object* v___x_1376_; 
v_token_1375_ = lean_ctor_get(v_x_1373_, 1);
lean_inc_ref(v_token_1375_);
lean_dec_ref(v_x_1373_);
v___x_1376_ = l_Std_CancellationToken_wait(v_token_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_done_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1373_ = stack[0].m_obj;
lean_object* v_res_1377_;
v_res_1377_ = l_Std_CancellationContext_done(v_x_1373_);
stack->m_obj
 = v_res_1377_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object* v_x_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_CancellationContext_done(v_x_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object* v_x_1381_){
_start:
{
lean_object* v_token_1382_; lean_object* v___x_1383_; 
v_token_1382_ = lean_ctor_get(v_x_1381_, 1);
lean_inc_ref(v_token_1382_);
lean_dec_ref(v_x_1381_);
v___x_1383_ = l_Std_CancellationToken_selector(v_token_1382_);
return v___x_1383_;
}
}
lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object* v_state_1384_, uint64_t v_id_1385_){
_start:
{
lean_object* v_tokens_1386_; lean_object* v___x_1387_; 
v_tokens_1386_ = lean_ctor_get(v_state_1384_, 0);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1386_, v_id_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_val_1389_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1387_, 1);
v_snd_1390_ = lean_ctor_get(v_val_1389_, 1);
lean_inc(v_snd_1390_);
lean_dec(v_val_1389_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_array_get_size(v_snd_1390_);
v___x_1393_ = lean_nat_dec_lt(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_snd_1390_);
v___x_1394_ = lean_unsigned_to_nat(1u);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_dec_le(v___x_1392_, v___x_1392_);
if (v___x_1396_ == 0)
{
if (v___x_1393_ == 0)
{
lean_dec(v_snd_1390_);
return v___x_1395_;
}
else
{
size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_of_nat(v___x_1392_);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1384_, v_snd_1390_, v___x_1397_, v___x_1398_, v___x_1391_);
lean_dec(v_snd_1390_);
v___x_1400_ = lean_nat_add(v___x_1395_, v___x_1399_);
lean_dec(v___x_1399_);
return v___x_1400_;
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_of_nat(v___x_1392_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1384_, v_snd_1390_, v___x_1401_, v___x_1402_, v___x_1391_);
lean_dec(v_snd_1390_);
v___x_1404_ = lean_nat_add(v___x_1395_, v___x_1403_);
lean_dec(v___x_1403_);
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_1384_ = stack[0].m_obj;
uint64_t v_id_1385_ = stack[1].m_num;
lean_object* v_res_1405_;
v_res_1405_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1384_, v_id_1385_);
stack->m_obj
 = v_res_1405_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object* v_state_1406_, lean_object* v_as_1407_, size_t v_i_1408_, size_t v_stop_1409_, lean_object* v_b_1410_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_eq(v_i_1408_, v_stop_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; uint64_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; 
v___x_1412_ = lean_array_uget_borrowed(v_as_1407_, v_i_1408_);
v___x_1413_ = lean_unbox_uint64(v___x_1412_);
v___x_1414_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1406_, v___x_1413_);
v___x_1415_ = lean_nat_add(v_b_1410_, v___x_1414_);
lean_dec(v___x_1414_);
lean_dec(v_b_1410_);
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1408_, v___x_1416_);
v_i_1408_ = v___x_1417_;
v_b_1410_ = v___x_1415_;
goto _start;
}
else
{
return v_b_1410_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_1406_ = stack[0].m_obj;
lean_object* v_as_1407_ = stack[1].m_obj;
size_t v_i_1408_ = stack[2].m_num;
size_t v_stop_1409_ = stack[3].m_num;
lean_object* v_b_1410_ = stack[4].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1406_, v_as_1407_, v_i_1408_, v_stop_1409_, v_b_1410_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object* v_state_1420_, lean_object* v_as_1421_, lean_object* v_i_1422_, lean_object* v_stop_1423_, lean_object* v_b_1424_){
_start:
{
size_t v_i_boxed_1425_; size_t v_stop_boxed_1426_; lean_object* v_res_1427_; 
v_i_boxed_1425_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_stop_boxed_1426_ = lean_unbox_usize(v_stop_1423_);
lean_dec(v_stop_1423_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1420_, v_as_1421_, v_i_boxed_1425_, v_stop_boxed_1426_, v_b_1424_);
lean_dec_ref(v_as_1421_);
lean_dec_ref(v_state_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object* v_state_1428_, lean_object* v_id_1429_){
_start:
{
uint64_t v_id_boxed_1430_; lean_object* v_res_1431_; 
v_id_boxed_1430_ = lean_unbox_uint64(v_id_1429_);
lean_dec_ref(v_id_1429_);
v_res_1431_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1428_, v_id_boxed_1430_);
lean_dec_ref(v_state_1428_);
return v_res_1431_;
}
}
lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t v_id_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_st_ref_get(v___y_1433_);
v___x_1436_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v___x_1435_, v_id_1432_);
lean_dec(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_countAliveTokens___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_id_1432_ = stack[0].m_num;
lean_object* v___y_1433_ = stack[1].m_obj;
lean_object* v_res_1437_;
v_res_1437_ = l_Std_CancellationContext_countAliveTokens___lam__0(v_id_1432_, v___y_1433_);
stack->m_obj
 = v_res_1437_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object* v_id_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint64_t v_id_boxed_1441_; lean_object* v_res_1442_; 
v_id_boxed_1441_ = lean_unbox_uint64(v_id_1438_);
lean_dec_ref(v_id_1438_);
v_res_1442_ = l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_1441_, v___y_1439_);
lean_dec(v___y_1439_);
return v_res_1442_;
}
}
lean_object* l_Std_CancellationContext_countAliveTokens(lean_object* v_x_1443_){
_start:
{
lean_object* v_state_1445_; uint64_t v_id_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; 
v_state_1445_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_state_1445_);
v_id_1446_ = lean_ctor_get_uint64(v_x_1443_, sizeof(void*)*3);
lean_dec_ref(v_x_1443_);
v___x_1447_ = lean_box_uint64(v_id_1446_);
v___f_1448_ = lean_alloc_closure((void*)(l_Std_CancellationContext_countAliveTokens___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1448_, 0, v___x_1447_);
v___x_1449_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1445_, v___f_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT void l_Std_CancellationContext_countAliveTokens_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1443_ = stack[0].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Std_CancellationContext_countAliveTokens(v_x_1443_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object* v_x_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_CancellationContext_countAliveTokens(v_x_1451_);
return v_res_1453_;
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
