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
lean_inc(v_size_19_);
v_k_20_ = lean_ctor_get(v_impl_16_, 1);
lean_inc(v_k_20_);
v_v_21_ = lean_ctor_get(v_impl_16_, 2);
lean_inc(v_v_21_);
v_l_22_ = lean_ctor_get(v_impl_16_, 3);
lean_inc(v_l_22_);
v_r_23_ = lean_ctor_get(v_impl_16_, 4);
lean_inc(v_r_23_);
v___x_24_ = lean_unsigned_to_nat(3u);
v___x_25_ = lean_nat_mul(v___x_24_, v_size_18_);
v___x_26_ = lean_nat_dec_lt(v___x_25_, v_size_19_);
lean_dec(v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
lean_dec(v_r_23_);
lean_dec(v_l_22_);
lean_dec(v_v_21_);
lean_dec(v_k_20_);
v___x_27_ = lean_nat_add(v___x_17_, v_size_18_);
v___x_28_ = lean_nat_add(v___x_27_, v_size_19_);
lean_dec(v_size_19_);
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
lean_inc(v_size_158_);
v_k_159_ = lean_ctor_get(v_impl_155_, 1);
lean_inc(v_k_159_);
v_v_160_ = lean_ctor_get(v_impl_155_, 2);
lean_inc(v_v_160_);
v_l_161_ = lean_ctor_get(v_impl_155_, 3);
lean_inc(v_l_161_);
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
lean_dec(v_l_161_);
lean_dec(v_v_160_);
lean_dec(v_k_159_);
v___x_166_ = lean_nat_add(v___x_156_, v_size_158_);
lean_dec(v_size_158_);
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
v___x_192_ = lean_nat_add(v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec(v___y_190_);
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
lean_ctor_set(v___x_172_, 3, v___y_189_);
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
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___y_189_);
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
v___y_189_ = v___x_204_;
v___y_190_ = v___x_205_;
v___y_191_ = v_size_206_;
goto v___jp_188_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_189_ = v___x_204_;
v___y_190_ = v___x_205_;
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
lean_inc(v_l_242_);
if (lean_obj_tag(v_l_242_) == 0)
{
lean_object* v_r_243_; lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_256_; 
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
lean_object* v___x_304_; lean_object* v___x_305_; uint64_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint64_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_304_ = l_Std_CancellationToken_new();
v___x_305_ = lean_box(1);
v___x_306_ = 0ULL;
v___x_307_ = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(v___x_304_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v___x_306_, v___x_308_, v___x_305_);
v___x_310_ = 1ULL;
v___x_311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set_uint64(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Std_Mutex_new___redArg(v___x_311_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_304_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_ctor_set_uint64(v___x_314_, sizeof(void*)*3, v___x_306_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_CancellationContext_new();
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object* v_00_u03b2_317_, uint64_t v_k_318_, lean_object* v_v_319_, lean_object* v_t_320_, lean_object* v_hl_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_318_, v_v_319_, v_t_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_k_324_, lean_object* v_v_325_, lean_object* v_t_326_, lean_object* v_hl_327_){
_start:
{
uint64_t v_k_boxed_328_; lean_object* v_res_329_; 
v_k_boxed_328_ = lean_unbox_uint64(v_k_324_);
lean_dec_ref(v_k_324_);
v_res_329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(v_00_u03b2_323_, v_k_boxed_328_, v_v_325_, v_t_326_, v_hl_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object* v_mutex_330_, lean_object* v_k_331_){
_start:
{
lean_object* v_ref_333_; lean_object* v_mutex_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_ref_333_ = lean_ctor_get(v_mutex_330_, 0);
lean_inc(v_ref_333_);
v_mutex_334_ = lean_ctor_get(v_mutex_330_, 1);
lean_inc(v_mutex_334_);
lean_dec_ref(v_mutex_330_);
v___x_335_ = lean_io_basemutex_lock(v_mutex_334_);
v___x_336_ = lean_apply_2(v_k_331_, v_ref_333_, lean_box(0));
v___x_337_ = lean_io_basemutex_unlock(v_mutex_334_);
lean_dec(v_mutex_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object* v_mutex_338_, lean_object* v_k_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_338_, v_k_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_mutex_344_, lean_object* v_k_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_344_, v_k_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_mutex_350_, lean_object* v_k_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(v_00_u03b1_348_, v_00_u03b2_349_, v_mutex_350_, v_k_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object* v_x_354_){
_start:
{
lean_inc_ref(v_x_354_);
return v_x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_355_);
lean_dec_ref(v_x_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t v___x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_box_uint64(v___x_357_);
v___x_360_ = lean_array_push(v_x_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object* v___x_361_, lean_object* v_x_362_){
_start:
{
uint64_t v___x_1222__boxed_363_; lean_object* v_res_364_; 
v___x_1222__boxed_363_ = lean_unbox_uint64(v___x_361_);
lean_dec_ref(v___x_361_);
v_res_364_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1222__boxed_363_, v_x_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t v___x_366_, uint64_t v_k_367_, lean_object* v_t_368_){
_start:
{
if (lean_obj_tag(v_t_368_) == 0)
{
lean_object* v_size_369_; lean_object* v_k_370_; lean_object* v_v_371_; lean_object* v_l_372_; lean_object* v_r_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_397_; 
v_size_369_ = lean_ctor_get(v_t_368_, 0);
v_k_370_ = lean_ctor_get(v_t_368_, 1);
v_v_371_ = lean_ctor_get(v_t_368_, 2);
v_l_372_ = lean_ctor_get(v_t_368_, 3);
v_r_373_ = lean_ctor_get(v_t_368_, 4);
v_isSharedCheck_397_ = !lean_is_exclusive(v_t_368_);
if (v_isSharedCheck_397_ == 0)
{
v___x_375_ = v_t_368_;
v_isShared_376_ = v_isSharedCheck_397_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_r_373_);
lean_inc(v_l_372_);
lean_inc(v_v_371_);
lean_inc(v_k_370_);
lean_inc(v_size_369_);
lean_dec(v_t_368_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_397_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint64_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_unbox_uint64(v_k_370_);
v___x_378_ = lean_uint64_dec_lt(v_k_367_, v___x_377_);
if (v___x_378_ == 0)
{
uint64_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_unbox_uint64(v_k_370_);
v___x_380_ = lean_uint64_dec_eq(v_k_367_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_366_, v_k_367_, v_r_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 4, v___x_381_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_369_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_370_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_371_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_l_372_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___f_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
lean_dec(v_k_370_);
v___f_385_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
v___x_386_ = lean_box_uint64(v___x_366_);
v___f_387_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(v___f_387_, 0, v___x_386_);
v___x_388_ = l_Prod_map___redArg(v___f_385_, v___f_387_, v_v_371_);
v___x_389_ = lean_box_uint64(v_k_367_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 2, v___x_388_);
lean_ctor_set(v___x_375_, 1, v___x_389_);
v___x_391_ = v___x_375_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_size_369_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_l_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_r_373_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_366_, v_k_367_, v_l_372_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 3, v___x_393_);
v___x_395_ = v___x_375_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_size_369_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_370_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_371_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_r_373_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
return v_t_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object* v___x_398_, lean_object* v_k_399_, lean_object* v_t_400_){
_start:
{
uint64_t v___x_1234__boxed_401_; uint64_t v_k_boxed_402_; lean_object* v_res_403_; 
v___x_1234__boxed_401_ = lean_unbox_uint64(v___x_398_);
lean_dec_ref(v___x_398_);
v_k_boxed_402_ = lean_unbox_uint64(v_k_399_);
lean_dec_ref(v_k_399_);
v_res_403_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1234__boxed_401_, v_k_boxed_402_, v_t_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object* v_token_404_, uint64_t v_id_405_, lean_object* v_state_406_, lean_object* v_root_407_, lean_object* v___y_408_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Std_CancellationToken_isCancelled(v_token_404_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_tokens_413_; uint64_t v_id_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_431_; 
v___x_411_ = l_Std_CancellationToken_new();
v___x_412_ = lean_st_ref_get(v___y_408_);
v_tokens_413_ = lean_ctor_get(v___x_412_, 0);
v_id_414_ = lean_ctor_get_uint64(v___x_412_, sizeof(void*)*1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_431_ == 0)
{
v___x_416_ = v___x_412_;
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_tokens_413_);
lean_dec(v___x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_431_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; lean_object* v___x_425_; 
v___x_418_ = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(v___x_411_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_411_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_414_, v___x_419_, v_tokens_413_);
v___x_421_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_414_, v_id_405_, v___x_420_);
v___x_422_ = 1ULL;
v___x_423_ = lean_uint64_add(v_id_414_, v___x_422_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_421_);
v___x_425_ = v___x_416_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_421_);
v___x_425_ = v_reuseFailAlloc_430_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_ctor_set_uint64(v___x_425_, sizeof(void*)*1, v___x_423_);
v___x_426_ = lean_st_ref_swap(v___y_408_, v___x_425_);
lean_dec(v___x_426_);
v___x_427_ = lean_box_uint64(v_id_405_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_429_, 0, v_state_406_);
lean_ctor_set(v___x_429_, 1, v___x_411_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
lean_ctor_set_uint64(v___x_429_, sizeof(void*)*3, v_id_414_);
return v___x_429_;
}
}
}
else
{
lean_dec_ref(v_state_406_);
lean_inc_ref(v_root_407_);
return v_root_407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object* v_token_432_, lean_object* v_id_433_, lean_object* v_state_434_, lean_object* v_root_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint64_t v_id_boxed_438_; lean_object* v_res_439_; 
v_id_boxed_438_ = lean_unbox_uint64(v_id_433_);
lean_dec_ref(v_id_433_);
v_res_439_ = l_Std_CancellationContext_fork___lam__0(v_token_432_, v_id_boxed_438_, v_state_434_, v_root_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v_root_435_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object* v_root_440_){
_start:
{
lean_object* v_state_442_; lean_object* v_token_443_; uint64_t v_id_444_; lean_object* v___x_445_; lean_object* v___f_446_; lean_object* v___x_447_; 
v_state_442_ = lean_ctor_get(v_root_440_, 0);
lean_inc_ref_n(v_state_442_, 2);
v_token_443_ = lean_ctor_get(v_root_440_, 1);
lean_inc_ref(v_token_443_);
v_id_444_ = lean_ctor_get_uint64(v_root_440_, sizeof(void*)*3);
v___x_445_ = lean_box_uint64(v_id_444_);
v___f_446_ = lean_alloc_closure((void*)(l_Std_CancellationContext_fork___lam__0___boxed), 6, 4);
lean_closure_set(v___f_446_, 0, v_token_443_);
lean_closure_set(v___f_446_, 1, v___x_445_);
lean_closure_set(v___f_446_, 2, v_state_442_);
lean_closure_set(v___f_446_, 3, v_root_440_);
v___x_447_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_442_, v___f_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object* v_root_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_CancellationContext_fork(v_root_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t v_k_451_, lean_object* v_t_452_){
_start:
{
if (lean_obj_tag(v_t_452_) == 0)
{
lean_object* v_k_453_; lean_object* v_v_454_; lean_object* v_l_455_; lean_object* v_r_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_1113_; 
v_k_453_ = lean_ctor_get(v_t_452_, 1);
v_v_454_ = lean_ctor_get(v_t_452_, 2);
v_l_455_ = lean_ctor_get(v_t_452_, 3);
v_r_456_ = lean_ctor_get(v_t_452_, 4);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_t_452_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v_t_452_, 0);
lean_dec(v_unused_1114_);
v___x_458_ = v_t_452_;
v_isShared_459_ = v_isSharedCheck_1113_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_r_456_);
lean_inc(v_l_455_);
lean_inc(v_v_454_);
lean_inc(v_k_453_);
lean_dec(v_t_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_1113_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint64_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unbox_uint64(v_k_453_);
v___x_461_ = lean_uint64_dec_lt(v_k_451_, v___x_460_);
if (v___x_461_ == 0)
{
uint64_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unbox_uint64(v_k_453_);
v___x_463_ = lean_uint64_dec_eq(v_k_451_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v_impl_464_; lean_object* v___x_465_; 
v_impl_464_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_451_, v_r_456_);
v___x_465_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_464_) == 0)
{
if (lean_obj_tag(v_l_455_) == 0)
{
lean_object* v_size_466_; lean_object* v_size_467_; lean_object* v_k_468_; lean_object* v_v_469_; lean_object* v_l_470_; lean_object* v_r_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_size_466_ = lean_ctor_get(v_impl_464_, 0);
lean_inc(v_size_466_);
v_size_467_ = lean_ctor_get(v_l_455_, 0);
v_k_468_ = lean_ctor_get(v_l_455_, 1);
v_v_469_ = lean_ctor_get(v_l_455_, 2);
v_l_470_ = lean_ctor_get(v_l_455_, 3);
v_r_471_ = lean_ctor_get(v_l_455_, 4);
lean_inc(v_r_471_);
v___x_472_ = lean_unsigned_to_nat(3u);
v___x_473_ = lean_nat_mul(v___x_472_, v_size_466_);
v___x_474_ = lean_nat_dec_lt(v___x_473_, v_size_467_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_r_471_);
v___x_475_ = lean_nat_add(v___x_465_, v_size_467_);
v___x_476_ = lean_nat_add(v___x_475_, v_size_466_);
lean_dec(v_size_466_);
lean_dec(v___x_475_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_impl_464_);
lean_ctor_set(v___x_458_, 0, v___x_476_);
v___x_478_ = v___x_458_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_impl_464_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_545_; 
lean_inc(v_l_470_);
lean_inc(v_v_469_);
lean_inc(v_k_468_);
lean_inc(v_size_467_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_546_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_l_455_, 2);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_l_455_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_550_);
v___x_481_ = v_l_455_;
v_isShared_482_ = v_isSharedCheck_545_;
goto v_resetjp_480_;
}
else
{
lean_dec(v_l_455_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_545_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_size_483_; lean_object* v_size_484_; lean_object* v_k_485_; lean_object* v_v_486_; lean_object* v_l_487_; lean_object* v_r_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_size_483_ = lean_ctor_get(v_l_470_, 0);
v_size_484_ = lean_ctor_get(v_r_471_, 0);
v_k_485_ = lean_ctor_get(v_r_471_, 1);
v_v_486_ = lean_ctor_get(v_r_471_, 2);
v_l_487_ = lean_ctor_get(v_r_471_, 3);
v_r_488_ = lean_ctor_get(v_r_471_, 4);
v___x_489_ = lean_unsigned_to_nat(2u);
v___x_490_ = lean_nat_mul(v___x_489_, v_size_483_);
v___x_491_ = lean_nat_dec_lt(v_size_484_, v___x_490_);
lean_dec(v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_520_; 
lean_inc(v_r_488_);
lean_inc(v_l_487_);
lean_inc(v_v_486_);
lean_inc(v_k_485_);
v_isSharedCheck_520_ = !lean_is_exclusive(v_r_471_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; lean_object* v_unused_524_; lean_object* v_unused_525_; 
v_unused_521_ = lean_ctor_get(v_r_471_, 4);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_r_471_, 3);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v_r_471_, 2);
lean_dec(v_unused_523_);
v_unused_524_ = lean_ctor_get(v_r_471_, 1);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_r_471_, 0);
lean_dec(v_unused_525_);
v___x_493_ = v_r_471_;
v_isShared_494_ = v_isSharedCheck_520_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_r_471_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_520_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___x_508_; lean_object* v___y_510_; 
v___x_495_ = lean_nat_add(v___x_465_, v_size_467_);
lean_dec(v_size_467_);
v___x_496_ = lean_nat_add(v___x_495_, v_size_466_);
lean_dec(v___x_495_);
v___x_508_ = lean_nat_add(v___x_465_, v_size_483_);
if (lean_obj_tag(v_l_487_) == 0)
{
lean_object* v_size_518_; 
v_size_518_ = lean_ctor_get(v_l_487_, 0);
lean_inc(v_size_518_);
v___y_510_ = v_size_518_;
goto v___jp_509_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___y_510_ = v___x_519_;
goto v___jp_509_;
}
v___jp_497_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_nat_add(v___y_498_, v___y_500_);
lean_dec(v___y_500_);
lean_dec(v___y_498_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v_impl_464_);
lean_ctor_set(v___x_493_, 3, v_r_488_);
lean_ctor_set(v___x_493_, 2, v_v_454_);
lean_ctor_set(v___x_493_, 1, v_k_453_);
lean_ctor_set(v___x_493_, 0, v___x_501_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_r_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_impl_464_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 4, v___x_503_);
lean_ctor_set(v___x_481_, 3, v___y_499_);
lean_ctor_set(v___x_481_, 2, v_v_486_);
lean_ctor_set(v___x_481_, 1, v_k_485_);
lean_ctor_set(v___x_481_, 0, v___x_496_);
v___x_505_ = v___x_481_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_k_485_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_v_486_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v___y_499_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_nat_add(v___x_508_, v___y_510_);
lean_dec(v___y_510_);
lean_dec(v___x_508_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_l_487_);
lean_ctor_set(v___x_458_, 3, v_l_470_);
lean_ctor_set(v___x_458_, 2, v_v_469_);
lean_ctor_set(v___x_458_, 1, v_k_468_);
lean_ctor_set(v___x_458_, 0, v___x_511_);
v___x_513_ = v___x_458_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_l_487_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_nat_add(v___x_465_, v_size_466_);
lean_dec(v_size_466_);
if (lean_obj_tag(v_r_488_) == 0)
{
lean_object* v_size_515_; 
v_size_515_ = lean_ctor_get(v_r_488_, 0);
lean_inc(v_size_515_);
v___y_498_ = v___x_514_;
v___y_499_ = v___x_513_;
v___y_500_ = v_size_515_;
goto v___jp_497_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___y_498_ = v___x_514_;
v___y_499_ = v___x_513_;
v___y_500_ = v___x_516_;
goto v___jp_497_;
}
}
}
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_del_object(v___x_458_);
v___x_526_ = lean_nat_add(v___x_465_, v_size_467_);
lean_dec(v_size_467_);
v___x_527_ = lean_nat_add(v___x_526_, v_size_466_);
lean_dec(v___x_526_);
v___x_528_ = lean_nat_add(v___x_465_, v_size_466_);
lean_dec(v_size_466_);
v___x_529_ = lean_nat_add(v___x_528_, v_size_484_);
lean_dec(v___x_528_);
lean_inc_ref(v_impl_464_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 4, v_impl_464_);
lean_ctor_set(v___x_481_, 3, v_r_471_);
lean_ctor_set(v___x_481_, 2, v_v_454_);
lean_ctor_set(v___x_481_, 1, v_k_453_);
lean_ctor_set(v___x_481_, 0, v___x_529_);
v___x_531_ = v___x_481_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_r_471_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_impl_464_);
v___x_531_ = v_reuseFailAlloc_544_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_isSharedCheck_538_ = !lean_is_exclusive(v_impl_464_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_539_ = lean_ctor_get(v_impl_464_, 4);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_464_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_464_, 2);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_impl_464_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_464_, 0);
lean_dec(v_unused_543_);
v___x_533_ = v_impl_464_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_dec(v_impl_464_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v___x_531_);
lean_ctor_set(v___x_533_, 3, v_l_470_);
lean_ctor_set(v___x_533_, 2, v_v_469_);
lean_ctor_set(v___x_533_, 1, v_k_468_);
lean_ctor_set(v___x_533_, 0, v___x_527_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_k_468_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_v_469_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v___x_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_size_551_ = lean_ctor_get(v_impl_464_, 0);
lean_inc(v_size_551_);
v___x_552_ = lean_nat_add(v___x_465_, v_size_551_);
lean_dec(v_size_551_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_impl_464_);
lean_ctor_set(v___x_458_, 0, v___x_552_);
v___x_554_ = v___x_458_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_impl_464_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
if (lean_obj_tag(v_l_455_) == 0)
{
lean_object* v_l_556_; 
v_l_556_ = lean_ctor_get(v_l_455_, 3);
if (lean_obj_tag(v_l_556_) == 0)
{
lean_object* v_r_557_; 
lean_inc_ref(v_l_556_);
v_r_557_ = lean_ctor_get(v_l_455_, 4);
lean_inc(v_r_557_);
if (lean_obj_tag(v_r_557_) == 0)
{
lean_object* v_size_558_; lean_object* v_k_559_; lean_object* v_v_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_573_; 
v_size_558_ = lean_ctor_get(v_l_455_, 0);
v_k_559_ = lean_ctor_get(v_l_455_, 1);
v_v_560_ = lean_ctor_get(v_l_455_, 2);
v_isSharedCheck_573_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_574_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_575_);
v___x_562_ = v_l_455_;
v_isShared_563_ = v_isSharedCheck_573_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_v_560_);
lean_inc(v_k_559_);
lean_inc(v_size_558_);
lean_dec(v_l_455_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_573_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_size_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v_size_564_ = lean_ctor_get(v_r_557_, 0);
v___x_565_ = lean_nat_add(v___x_465_, v_size_558_);
lean_dec(v_size_558_);
v___x_566_ = lean_nat_add(v___x_465_, v_size_564_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v_impl_464_);
lean_ctor_set(v___x_562_, 3, v_r_557_);
lean_ctor_set(v___x_562_, 2, v_v_454_);
lean_ctor_set(v___x_562_, 1, v_k_453_);
lean_ctor_set(v___x_562_, 0, v___x_566_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_r_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_impl_464_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_568_);
lean_ctor_set(v___x_458_, 3, v_l_556_);
lean_ctor_set(v___x_458_, 2, v_v_560_);
lean_ctor_set(v___x_458_, 1, v_k_559_);
lean_ctor_set(v___x_458_, 0, v___x_565_);
v___x_570_ = v___x_458_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_l_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v_k_576_; lean_object* v_v_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_588_; 
v_k_576_ = lean_ctor_get(v_l_455_, 1);
v_v_577_ = lean_ctor_get(v_l_455_, 2);
v_isSharedCheck_588_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_589_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_591_);
v___x_579_ = v_l_455_;
v_isShared_580_ = v_isSharedCheck_588_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_v_577_);
lean_inc(v_k_576_);
lean_dec(v_l_455_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_588_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(3u);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 3, v_r_557_);
lean_ctor_set(v___x_579_, 2, v_v_454_);
lean_ctor_set(v___x_579_, 1, v_k_453_);
lean_ctor_set(v___x_579_, 0, v___x_465_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_r_557_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_r_557_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_583_);
lean_ctor_set(v___x_458_, 3, v_l_556_);
lean_ctor_set(v___x_458_, 2, v_v_577_);
lean_ctor_set(v___x_458_, 1, v_k_576_);
lean_ctor_set(v___x_458_, 0, v___x_581_);
v___x_585_ = v___x_458_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_l_556_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_r_592_; 
v_r_592_ = lean_ctor_get(v_l_455_, 4);
lean_inc(v_r_592_);
if (lean_obj_tag(v_r_592_) == 0)
{
lean_object* v_k_593_; lean_object* v_v_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_617_; 
lean_inc(v_l_556_);
v_k_593_ = lean_ctor_get(v_l_455_, 1);
v_v_594_ = lean_ctor_get(v_l_455_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_618_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_620_);
v___x_596_ = v_l_455_;
v_isShared_597_ = v_isSharedCheck_617_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_v_594_);
lean_inc(v_k_593_);
lean_dec(v_l_455_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_617_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_613_; 
v_k_598_ = lean_ctor_get(v_r_592_, 1);
v_v_599_ = lean_ctor_get(v_r_592_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_614_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_616_);
v___x_601_ = v_r_592_;
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_v_599_);
lean_inc(v_k_598_);
lean_dec(v_r_592_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(3u);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_l_556_);
lean_ctor_set(v___x_601_, 3, v_l_556_);
lean_ctor_set(v___x_601_, 2, v_v_594_);
lean_ctor_set(v___x_601_, 1, v_k_593_);
lean_ctor_set(v___x_601_, 0, v___x_465_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_l_556_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_l_556_);
v___x_605_ = v_reuseFailAlloc_612_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 4, v_l_556_);
lean_ctor_set(v___x_596_, 2, v_v_454_);
lean_ctor_set(v___x_596_, 1, v_k_453_);
lean_ctor_set(v___x_596_, 0, v___x_465_);
v___x_607_ = v___x_596_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_l_556_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_l_556_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_607_);
lean_ctor_set(v___x_458_, 3, v___x_605_);
lean_ctor_set(v___x_458_, 2, v_v_599_);
lean_ctor_set(v___x_458_, 1, v_k_598_);
lean_ctor_set(v___x_458_, 0, v___x_603_);
v___x_609_ = v___x_458_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = lean_unsigned_to_nat(2u);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_r_592_);
lean_ctor_set(v___x_458_, 0, v___x_621_);
v___x_623_ = v___x_458_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_r_592_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v___x_626_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_l_455_);
lean_ctor_set(v___x_458_, 0, v___x_465_);
v___x_626_ = v___x_458_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_l_455_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_del_object(v___x_458_);
lean_dec(v_v_454_);
lean_dec(v_k_453_);
if (lean_obj_tag(v_l_455_) == 0)
{
if (lean_obj_tag(v_r_456_) == 0)
{
lean_object* v_size_628_; lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v_l_631_; lean_object* v_r_632_; lean_object* v_size_633_; lean_object* v_k_634_; lean_object* v_v_635_; lean_object* v_l_636_; lean_object* v_r_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_size_628_ = lean_ctor_get(v_l_455_, 0);
v_k_629_ = lean_ctor_get(v_l_455_, 1);
v_v_630_ = lean_ctor_get(v_l_455_, 2);
v_l_631_ = lean_ctor_get(v_l_455_, 3);
v_r_632_ = lean_ctor_get(v_l_455_, 4);
lean_inc(v_r_632_);
v_size_633_ = lean_ctor_get(v_r_456_, 0);
v_k_634_ = lean_ctor_get(v_r_456_, 1);
v_v_635_ = lean_ctor_get(v_r_456_, 2);
v_l_636_ = lean_ctor_get(v_r_456_, 3);
lean_inc(v_l_636_);
v_r_637_ = lean_ctor_get(v_r_456_, 4);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_dec_lt(v_size_628_, v_size_633_);
if (v___x_639_ == 0)
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_775_; 
lean_inc(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
v_isSharedCheck_775_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; 
v_unused_776_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_l_455_, 2);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_l_455_, 1);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_780_);
v___x_641_ = v_l_455_;
v_isShared_642_ = v_isSharedCheck_775_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_l_455_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_775_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_tree_644_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_629_, v_v_630_, v_l_631_, v_r_632_);
v_tree_644_ = lean_ctor_get(v___x_643_, 2);
lean_inc(v_tree_644_);
if (lean_obj_tag(v_tree_644_) == 0)
{
lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v_size_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_k_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_645_);
v_v_646_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_646_);
lean_dec_ref(v___x_643_);
v_size_647_ = lean_ctor_get(v_tree_644_, 0);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_nat_mul(v___x_648_, v_size_647_);
v___x_650_ = lean_nat_dec_lt(v___x_649_, v_size_633_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec(v_l_636_);
v___x_651_ = lean_nat_add(v___x_638_, v_size_647_);
v___x_652_ = lean_nat_add(v___x_651_, v_size_633_);
lean_dec(v___x_651_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_456_);
lean_ctor_set(v___x_641_, 3, v_tree_644_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_652_);
v___x_654_ = v___x_641_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_tree_644_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_456_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_710_; 
lean_inc(v_r_637_);
lean_inc(v_v_635_);
lean_inc(v_k_634_);
lean_inc(v_size_633_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_711_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_r_456_, 2);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_r_456_, 1);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_715_);
v___x_657_ = v_r_456_;
v_isShared_658_ = v_isSharedCheck_710_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_r_456_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_710_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_size_659_; lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; lean_object* v_size_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_size_659_ = lean_ctor_get(v_l_636_, 0);
v_k_660_ = lean_ctor_get(v_l_636_, 1);
v_v_661_ = lean_ctor_get(v_l_636_, 2);
v_l_662_ = lean_ctor_get(v_l_636_, 3);
v_r_663_ = lean_ctor_get(v_l_636_, 4);
v_size_664_ = lean_ctor_get(v_r_637_, 0);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_nat_mul(v___x_665_, v_size_664_);
v___x_667_ = lean_nat_dec_lt(v_size_659_, v___x_666_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_r_663_);
lean_inc(v_l_662_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_l_636_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_696_ = lean_ctor_get(v_l_636_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_l_636_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_l_636_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_l_636_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_l_636_, 0);
lean_dec(v_unused_700_);
v___x_669_ = v_l_636_;
v_isShared_670_ = v_isSharedCheck_695_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_l_636_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_695_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_685_; 
v___x_671_ = lean_nat_add(v___x_638_, v_size_647_);
v___x_672_ = lean_nat_add(v___x_671_, v_size_633_);
lean_dec(v_size_633_);
if (lean_obj_tag(v_l_662_) == 0)
{
lean_object* v_size_693_; 
v_size_693_ = lean_ctor_get(v_l_662_, 0);
lean_inc(v_size_693_);
v___y_685_ = v_size_693_;
goto v___jp_684_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___y_685_ = v___x_694_;
goto v___jp_684_;
}
v___jp_673_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_nat_add(v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_r_637_);
lean_ctor_set(v___x_669_, 3, v_r_663_);
lean_ctor_set(v___x_669_, 2, v_v_635_);
lean_ctor_set(v___x_669_, 1, v_k_634_);
lean_ctor_set(v___x_669_, 0, v___x_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_r_663_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_r_637_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_679_);
lean_ctor_set(v___x_657_, 3, v___y_674_);
lean_ctor_set(v___x_657_, 2, v_v_661_);
lean_ctor_set(v___x_657_, 1, v_k_660_);
lean_ctor_set(v___x_657_, 0, v___x_672_);
v___x_681_ = v___x_657_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v___y_674_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_nat_add(v___x_671_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v___x_671_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_l_662_);
lean_ctor_set(v___x_641_, 3, v_tree_644_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_686_);
v___x_688_ = v___x_641_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_tree_644_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_l_662_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_nat_add(v___x_638_, v_size_664_);
if (lean_obj_tag(v_r_663_) == 0)
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_r_663_, 0);
lean_inc(v_size_690_);
v___y_674_ = v___x_688_;
v___y_675_ = v___x_689_;
v___y_676_ = v_size_690_;
goto v___jp_673_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_674_ = v___x_688_;
v___y_675_ = v___x_689_;
v___y_676_ = v___x_691_;
goto v___jp_673_;
}
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_701_ = lean_nat_add(v___x_638_, v_size_647_);
v___x_702_ = lean_nat_add(v___x_701_, v_size_633_);
lean_dec(v_size_633_);
v___x_703_ = lean_nat_add(v___x_701_, v_size_659_);
lean_dec(v___x_701_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v_l_636_);
lean_ctor_set(v___x_657_, 3, v_tree_644_);
lean_ctor_set(v___x_657_, 2, v_v_646_);
lean_ctor_set(v___x_657_, 1, v_k_645_);
lean_ctor_set(v___x_657_, 0, v___x_703_);
v___x_705_ = v___x_657_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_tree_644_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_l_636_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_637_);
lean_ctor_set(v___x_641_, 3, v___x_705_);
lean_ctor_set(v___x_641_, 2, v_v_635_);
lean_ctor_set(v___x_641_, 1, v_k_634_);
lean_ctor_set(v___x_641_, 0, v___x_702_);
v___x_707_ = v___x_641_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_r_637_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
else
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_769_; 
lean_inc(v_r_637_);
lean_inc(v_v_635_);
lean_inc(v_k_634_);
lean_inc(v_size_633_);
v_isSharedCheck_769_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; lean_object* v_unused_771_; lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_770_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_r_456_, 2);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_r_456_, 1);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_774_);
v___x_717_ = v_r_456_;
v_isShared_718_ = v_isSharedCheck_769_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_r_456_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_769_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_l_636_) == 0)
{
if (lean_obj_tag(v_r_637_) == 0)
{
lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v_size_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_k_719_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_719_);
v_v_720_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_720_);
lean_dec_ref(v___x_643_);
v_size_721_ = lean_ctor_get(v_l_636_, 0);
v___x_722_ = lean_nat_add(v___x_638_, v_size_633_);
lean_dec(v_size_633_);
v___x_723_ = lean_nat_add(v___x_638_, v_size_721_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v_l_636_);
lean_ctor_set(v___x_717_, 3, v_tree_644_);
lean_ctor_set(v___x_717_, 2, v_v_720_);
lean_ctor_set(v___x_717_, 1, v_k_719_);
lean_ctor_set(v___x_717_, 0, v___x_723_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_719_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_v_720_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_tree_644_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_l_636_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_637_);
lean_ctor_set(v___x_641_, 3, v___x_725_);
lean_ctor_set(v___x_641_, 2, v_v_635_);
lean_ctor_set(v___x_641_, 1, v_k_634_);
lean_ctor_set(v___x_641_, 0, v___x_722_);
v___x_727_ = v___x_641_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_r_637_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_k_730_; lean_object* v_v_731_; lean_object* v_k_732_; lean_object* v_v_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_size_633_);
v_k_730_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_730_);
v_v_731_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_731_);
lean_dec_ref(v___x_643_);
v_k_732_ = lean_ctor_get(v_l_636_, 1);
v_v_733_ = lean_ctor_get(v_l_636_, 2);
v_isSharedCheck_747_ = !lean_is_exclusive(v_l_636_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_748_ = lean_ctor_get(v_l_636_, 4);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_l_636_, 3);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_l_636_, 0);
lean_dec(v_unused_750_);
v___x_735_ = v_l_636_;
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_v_733_);
lean_inc(v_k_732_);
lean_dec(v_l_636_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(3u);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v_r_637_);
lean_ctor_set(v___x_735_, 3, v_r_637_);
lean_ctor_set(v___x_735_, 2, v_v_731_);
lean_ctor_set(v___x_735_, 1, v_k_730_);
lean_ctor_set(v___x_735_, 0, v___x_638_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_730_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_r_637_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_r_637_);
v___x_739_ = v_reuseFailAlloc_746_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 3, v_r_637_);
lean_ctor_set(v___x_717_, 0, v___x_638_);
v___x_741_ = v___x_717_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_r_637_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_637_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v___x_741_);
lean_ctor_set(v___x_641_, 3, v___x_739_);
lean_ctor_set(v___x_641_, 2, v_v_733_);
lean_ctor_set(v___x_641_, 1, v_k_732_);
lean_ctor_set(v___x_641_, 0, v___x_737_);
v___x_743_ = v___x_641_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_637_) == 0)
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_size_633_);
v_k_751_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_751_);
v_v_752_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_752_);
lean_dec_ref(v___x_643_);
v___x_753_ = lean_unsigned_to_nat(3u);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v_l_636_);
lean_ctor_set(v___x_717_, 2, v_v_752_);
lean_ctor_set(v___x_717_, 1, v_k_751_);
lean_ctor_set(v___x_717_, 0, v___x_638_);
v___x_755_ = v___x_717_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_l_636_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_l_636_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_637_);
lean_ctor_set(v___x_641_, 3, v___x_755_);
lean_ctor_set(v___x_641_, 2, v_v_635_);
lean_ctor_set(v___x_641_, 1, v_k_634_);
lean_ctor_set(v___x_641_, 0, v___x_753_);
v___x_757_ = v___x_641_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_r_637_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v___x_763_; 
v_k_760_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_760_);
v_v_761_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_761_);
lean_dec_ref(v___x_643_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 3, v_r_637_);
v___x_763_ = v___x_717_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_size_633_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_r_637_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_r_637_);
v___x_763_ = v_reuseFailAlloc_768_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_unsigned_to_nat(2u);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v___x_763_);
lean_ctor_set(v___x_641_, 3, v_r_637_);
lean_ctor_set(v___x_641_, 2, v_v_761_);
lean_ctor_set(v___x_641_, 1, v_k_760_);
lean_ctor_set(v___x_641_, 0, v___x_764_);
v___x_766_ = v___x_641_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_r_637_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v___x_763_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
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
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_933_; 
lean_inc(v_r_637_);
lean_inc(v_v_635_);
lean_inc(v_k_634_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_934_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_r_456_, 2);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_r_456_, 1);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_938_);
v___x_782_ = v_r_456_;
v_isShared_783_ = v_isSharedCheck_933_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_r_456_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_933_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v_tree_785_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_634_, v_v_635_, v_l_636_, v_r_637_);
v_tree_785_ = lean_ctor_get(v___x_784_, 2);
lean_inc(v_tree_785_);
if (lean_obj_tag(v_tree_785_) == 0)
{
lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v_size_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_k_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_k_786_);
v_v_787_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_v_787_);
lean_dec_ref(v___x_784_);
v_size_788_ = lean_ctor_get(v_tree_785_, 0);
v___x_789_ = lean_unsigned_to_nat(3u);
v___x_790_ = lean_nat_mul(v___x_789_, v_size_788_);
v___x_791_ = lean_nat_dec_lt(v___x_790_, v_size_628_);
lean_dec(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec(v_r_632_);
v___x_792_ = lean_nat_add(v___x_638_, v_size_628_);
v___x_793_ = lean_nat_add(v___x_792_, v_size_788_);
lean_dec(v___x_792_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_tree_785_);
lean_ctor_set(v___x_782_, 3, v_l_455_);
lean_ctor_set(v___x_782_, 2, v_v_787_);
lean_ctor_set(v___x_782_, 1, v_k_786_);
lean_ctor_set(v___x_782_, 0, v___x_793_);
v___x_795_ = v___x_782_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_tree_785_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_862_; 
lean_inc(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_inc(v_size_628_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_863_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_455_, 2);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_l_455_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_867_);
v___x_798_ = v_l_455_;
v_isShared_799_ = v_isSharedCheck_862_;
goto v_resetjp_797_;
}
else
{
lean_dec(v_l_455_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_862_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_size_800_; lean_object* v_size_801_; lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_size_800_ = lean_ctor_get(v_l_631_, 0);
v_size_801_ = lean_ctor_get(v_r_632_, 0);
v_k_802_ = lean_ctor_get(v_r_632_, 1);
v_v_803_ = lean_ctor_get(v_r_632_, 2);
v_l_804_ = lean_ctor_get(v_r_632_, 3);
v_r_805_ = lean_ctor_get(v_r_632_, 4);
v___x_806_ = lean_unsigned_to_nat(2u);
v___x_807_ = lean_nat_mul(v___x_806_, v_size_800_);
v___x_808_ = lean_nat_dec_lt(v_size_801_, v___x_807_);
lean_dec(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_846_; 
lean_inc(v_r_805_);
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_del_object(v___x_798_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_r_632_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_847_ = lean_ctor_get(v_r_632_, 4);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_r_632_, 3);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_r_632_, 2);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_r_632_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_r_632_, 0);
lean_dec(v_unused_851_);
v___x_810_ = v_r_632_;
v_isShared_811_ = v_isSharedCheck_846_;
goto v_resetjp_809_;
}
else
{
lean_dec(v_r_632_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_846_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___x_834_; lean_object* v___y_836_; 
v___x_812_ = lean_nat_add(v___x_638_, v_size_628_);
lean_dec(v_size_628_);
v___x_813_ = lean_nat_add(v___x_812_, v_size_788_);
lean_dec(v___x_812_);
v___x_834_ = lean_nat_add(v___x_638_, v_size_800_);
if (lean_obj_tag(v_l_804_) == 0)
{
lean_object* v_size_844_; 
v_size_844_ = lean_ctor_get(v_l_804_, 0);
lean_inc(v_size_844_);
v___y_836_ = v_size_844_;
goto v___jp_835_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___y_836_ = v___x_845_;
goto v___jp_835_;
}
v___jp_814_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_nat_add(v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
lean_inc_ref(v_tree_785_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_tree_785_);
lean_ctor_set(v___x_810_, 3, v_r_805_);
lean_ctor_set(v___x_810_, 2, v_v_787_);
lean_ctor_set(v___x_810_, 1, v_k_786_);
lean_ctor_set(v___x_810_, 0, v___x_818_);
v___x_820_ = v___x_810_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_tree_785_);
v___x_820_ = v_reuseFailAlloc_833_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_isSharedCheck_827_ = !lean_is_exclusive(v_tree_785_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; lean_object* v_unused_829_; lean_object* v_unused_830_; lean_object* v_unused_831_; lean_object* v_unused_832_; 
v_unused_828_ = lean_ctor_get(v_tree_785_, 4);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_tree_785_, 3);
lean_dec(v_unused_829_);
v_unused_830_ = lean_ctor_get(v_tree_785_, 2);
lean_dec(v_unused_830_);
v_unused_831_ = lean_ctor_get(v_tree_785_, 1);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_tree_785_, 0);
lean_dec(v_unused_832_);
v___x_822_ = v_tree_785_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_tree_785_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 4, v___x_820_);
lean_ctor_set(v___x_822_, 3, v___y_815_);
lean_ctor_set(v___x_822_, 2, v_v_803_);
lean_ctor_set(v___x_822_, 1, v_k_802_);
lean_ctor_set(v___x_822_, 0, v___x_813_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v___y_815_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v___x_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_nat_add(v___x_834_, v___y_836_);
lean_dec(v___y_836_);
lean_dec(v___x_834_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_l_804_);
lean_ctor_set(v___x_782_, 3, v_l_631_);
lean_ctor_set(v___x_782_, 2, v_v_630_);
lean_ctor_set(v___x_782_, 1, v_k_629_);
lean_ctor_set(v___x_782_, 0, v___x_837_);
v___x_839_ = v___x_782_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_l_804_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_nat_add(v___x_638_, v_size_788_);
if (lean_obj_tag(v_r_805_) == 0)
{
lean_object* v_size_841_; 
v_size_841_ = lean_ctor_get(v_r_805_, 0);
lean_inc(v_size_841_);
v___y_815_ = v___x_839_;
v___y_816_ = v___x_840_;
v___y_817_ = v_size_841_;
goto v___jp_814_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___y_815_ = v___x_839_;
v___y_816_ = v___x_840_;
v___y_817_ = v___x_842_;
goto v___jp_814_;
}
}
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_852_ = lean_nat_add(v___x_638_, v_size_628_);
lean_dec(v_size_628_);
v___x_853_ = lean_nat_add(v___x_852_, v_size_788_);
lean_dec(v___x_852_);
v___x_854_ = lean_nat_add(v___x_638_, v_size_788_);
v___x_855_ = lean_nat_add(v___x_854_, v_size_801_);
lean_dec(v___x_854_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_tree_785_);
lean_ctor_set(v___x_782_, 3, v_r_632_);
lean_ctor_set(v___x_782_, 2, v_v_787_);
lean_ctor_set(v___x_782_, 1, v_k_786_);
lean_ctor_set(v___x_782_, 0, v___x_855_);
v___x_857_ = v___x_782_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_tree_785_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 4, v___x_857_);
lean_ctor_set(v___x_798_, 0, v___x_853_);
v___x_859_ = v___x_798_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_631_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_891_; 
lean_inc_ref(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_inc(v_size_628_);
v_isSharedCheck_891_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; 
v_unused_892_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_l_455_, 2);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_l_455_, 1);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_896_);
v___x_869_ = v_l_455_;
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
else
{
lean_dec(v_l_455_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_r_632_) == 0)
{
lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_size_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_k_871_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_k_871_);
v_v_872_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_v_872_);
lean_dec_ref(v___x_784_);
v_size_873_ = lean_ctor_get(v_r_632_, 0);
v___x_874_ = lean_nat_add(v___x_638_, v_size_628_);
lean_dec(v_size_628_);
v___x_875_ = lean_nat_add(v___x_638_, v_size_873_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_tree_785_);
lean_ctor_set(v___x_782_, 3, v_r_632_);
lean_ctor_set(v___x_782_, 2, v_v_872_);
lean_ctor_set(v___x_782_, 1, v_k_871_);
lean_ctor_set(v___x_782_, 0, v___x_875_);
v___x_877_ = v___x_782_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_tree_785_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 4, v___x_877_);
lean_ctor_set(v___x_869_, 0, v___x_874_);
v___x_879_ = v___x_869_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v_size_628_);
v_k_882_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_k_882_);
v_v_883_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_v_883_);
lean_dec_ref(v___x_784_);
v___x_884_ = lean_unsigned_to_nat(3u);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_r_632_);
lean_ctor_set(v___x_782_, 3, v_r_632_);
lean_ctor_set(v___x_782_, 2, v_v_883_);
lean_ctor_set(v___x_782_, 1, v_k_882_);
lean_ctor_set(v___x_782_, 0, v___x_638_);
v___x_886_ = v___x_782_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_r_632_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 4, v___x_886_);
lean_ctor_set(v___x_869_, 0, v___x_884_);
v___x_888_ = v___x_869_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_631_);
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
}
}
else
{
if (lean_obj_tag(v_r_632_) == 0)
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_921_; 
lean_inc(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
v_isSharedCheck_921_ = !lean_is_exclusive(v_l_455_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; 
v_unused_922_ = lean_ctor_get(v_l_455_, 4);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_l_455_, 3);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_l_455_, 2);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_455_, 1);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_455_, 0);
lean_dec(v_unused_926_);
v___x_898_ = v_l_455_;
v_isShared_899_ = v_isSharedCheck_921_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_l_455_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_921_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_k_900_; lean_object* v_v_901_; lean_object* v_k_902_; lean_object* v_v_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_917_; 
v_k_900_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_k_900_);
v_v_901_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_v_901_);
lean_dec_ref(v___x_784_);
v_k_902_ = lean_ctor_get(v_r_632_, 1);
v_v_903_ = lean_ctor_get(v_r_632_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_r_632_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_918_ = lean_ctor_get(v_r_632_, 4);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_r_632_, 3);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_r_632_, 0);
lean_dec(v_unused_920_);
v___x_905_ = v_r_632_;
v_isShared_906_ = v_isSharedCheck_917_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_v_903_);
lean_inc(v_k_902_);
lean_dec(v_r_632_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_917_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_unsigned_to_nat(3u);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 4, v_l_631_);
lean_ctor_set(v___x_905_, 3, v_l_631_);
lean_ctor_set(v___x_905_, 2, v_v_630_);
lean_ctor_set(v___x_905_, 1, v_k_629_);
lean_ctor_set(v___x_905_, 0, v___x_638_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_l_631_);
v___x_909_ = v_reuseFailAlloc_916_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_l_631_);
lean_ctor_set(v___x_782_, 3, v_l_631_);
lean_ctor_set(v___x_782_, 2, v_v_901_);
lean_ctor_set(v___x_782_, 1, v_k_900_);
lean_ctor_set(v___x_782_, 0, v___x_638_);
v___x_911_ = v___x_782_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_l_631_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 4, v___x_911_);
lean_ctor_set(v___x_898_, 3, v___x_909_);
lean_ctor_set(v___x_898_, 2, v_v_903_);
lean_ctor_set(v___x_898_, 1, v_k_902_);
lean_ctor_set(v___x_898_, 0, v___x_907_);
v___x_913_ = v___x_898_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_902_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v___x_909_);
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
}
else
{
lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_k_927_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_k_927_);
v_v_928_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_v_928_);
lean_dec_ref(v___x_784_);
v___x_929_ = lean_unsigned_to_nat(2u);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_r_632_);
lean_ctor_set(v___x_782_, 3, v_l_455_);
lean_ctor_set(v___x_782_, 2, v_v_928_);
lean_ctor_set(v___x_782_, 1, v_k_927_);
lean_ctor_set(v___x_782_, 0, v___x_929_);
v___x_931_ = v___x_782_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_r_632_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
}
else
{
return v_l_455_;
}
}
else
{
return v_r_456_;
}
}
}
else
{
lean_object* v_impl_939_; lean_object* v___x_940_; 
v_impl_939_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_451_, v_l_455_);
v___x_940_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_939_) == 0)
{
if (lean_obj_tag(v_r_456_) == 0)
{
lean_object* v_size_941_; lean_object* v_size_942_; lean_object* v_k_943_; lean_object* v_v_944_; lean_object* v_l_945_; lean_object* v_r_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_size_941_ = lean_ctor_get(v_impl_939_, 0);
lean_inc(v_size_941_);
v_size_942_ = lean_ctor_get(v_r_456_, 0);
v_k_943_ = lean_ctor_get(v_r_456_, 1);
v_v_944_ = lean_ctor_get(v_r_456_, 2);
v_l_945_ = lean_ctor_get(v_r_456_, 3);
lean_inc(v_l_945_);
v_r_946_ = lean_ctor_get(v_r_456_, 4);
v___x_947_ = lean_unsigned_to_nat(3u);
v___x_948_ = lean_nat_mul(v___x_947_, v_size_941_);
v___x_949_ = lean_nat_dec_lt(v___x_948_, v_size_942_);
lean_dec(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_l_945_);
v___x_950_ = lean_nat_add(v___x_940_, v_size_941_);
lean_dec(v_size_941_);
v___x_951_ = lean_nat_add(v___x_950_, v_size_942_);
lean_dec(v___x_950_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 3, v_impl_939_);
lean_ctor_set(v___x_458_, 0, v___x_951_);
v___x_953_ = v___x_458_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_impl_939_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_r_456_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1018_; 
lean_inc(v_r_946_);
lean_inc(v_v_944_);
lean_inc(v_k_943_);
lean_inc(v_size_942_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1019_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_r_456_, 2);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_r_456_, 1);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_1023_);
v___x_956_ = v_r_456_;
v_isShared_957_ = v_isSharedCheck_1018_;
goto v_resetjp_955_;
}
else
{
lean_dec(v_r_456_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1018_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_size_958_; lean_object* v_k_959_; lean_object* v_v_960_; lean_object* v_l_961_; lean_object* v_r_962_; lean_object* v_size_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_size_958_ = lean_ctor_get(v_l_945_, 0);
v_k_959_ = lean_ctor_get(v_l_945_, 1);
v_v_960_ = lean_ctor_get(v_l_945_, 2);
v_l_961_ = lean_ctor_get(v_l_945_, 3);
v_r_962_ = lean_ctor_get(v_l_945_, 4);
v_size_963_ = lean_ctor_get(v_r_946_, 0);
v___x_964_ = lean_unsigned_to_nat(2u);
v___x_965_ = lean_nat_mul(v___x_964_, v_size_963_);
v___x_966_ = lean_nat_dec_lt(v_size_958_, v___x_965_);
lean_dec(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_994_; 
lean_inc(v_r_962_);
lean_inc(v_l_961_);
lean_inc(v_v_960_);
lean_inc(v_k_959_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_l_945_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_l_945_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_l_945_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_l_945_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_l_945_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_l_945_, 0);
lean_dec(v_unused_999_);
v___x_968_ = v_l_945_;
v_isShared_969_ = v_isSharedCheck_994_;
goto v_resetjp_967_;
}
else
{
lean_dec(v_l_945_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_994_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_984_; 
v___x_970_ = lean_nat_add(v___x_940_, v_size_941_);
lean_dec(v_size_941_);
v___x_971_ = lean_nat_add(v___x_970_, v_size_942_);
lean_dec(v_size_942_);
if (lean_obj_tag(v_l_961_) == 0)
{
lean_object* v_size_992_; 
v_size_992_ = lean_ctor_get(v_l_961_, 0);
lean_inc(v_size_992_);
v___y_984_ = v_size_992_;
goto v___jp_983_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___y_984_ = v___x_993_;
goto v___jp_983_;
}
v___jp_972_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_nat_add(v___y_973_, v___y_975_);
lean_dec(v___y_975_);
lean_dec(v___y_973_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 4, v_r_946_);
lean_ctor_set(v___x_968_, 3, v_r_962_);
lean_ctor_set(v___x_968_, 2, v_v_944_);
lean_ctor_set(v___x_968_, 1, v_k_943_);
lean_ctor_set(v___x_968_, 0, v___x_976_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_r_962_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_r_946_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 4, v___x_978_);
lean_ctor_set(v___x_956_, 3, v___y_974_);
lean_ctor_set(v___x_956_, 2, v_v_960_);
lean_ctor_set(v___x_956_, 1, v_k_959_);
lean_ctor_set(v___x_956_, 0, v___x_971_);
v___x_980_ = v___x_956_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_k_959_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_v_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v___y_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_nat_add(v___x_970_, v___y_984_);
lean_dec(v___y_984_);
lean_dec(v___x_970_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_l_961_);
lean_ctor_set(v___x_458_, 3, v_impl_939_);
lean_ctor_set(v___x_458_, 0, v___x_985_);
v___x_987_ = v___x_458_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_impl_939_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_l_961_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_nat_add(v___x_940_, v_size_963_);
if (lean_obj_tag(v_r_962_) == 0)
{
lean_object* v_size_989_; 
v_size_989_ = lean_ctor_get(v_r_962_, 0);
lean_inc(v_size_989_);
v___y_973_ = v___x_988_;
v___y_974_ = v___x_987_;
v___y_975_ = v_size_989_;
goto v___jp_972_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___y_973_ = v___x_988_;
v___y_974_ = v___x_987_;
v___y_975_ = v___x_990_;
goto v___jp_972_;
}
}
}
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_del_object(v___x_458_);
v___x_1000_ = lean_nat_add(v___x_940_, v_size_941_);
lean_dec(v_size_941_);
v___x_1001_ = lean_nat_add(v___x_1000_, v_size_942_);
lean_dec(v_size_942_);
v___x_1002_ = lean_nat_add(v___x_1000_, v_size_958_);
lean_dec(v___x_1000_);
lean_inc_ref(v_impl_939_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 4, v_l_945_);
lean_ctor_set(v___x_956_, 3, v_impl_939_);
lean_ctor_set(v___x_956_, 2, v_v_454_);
lean_ctor_set(v___x_956_, 1, v_k_453_);
lean_ctor_set(v___x_956_, 0, v___x_1002_);
v___x_1004_ = v___x_956_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_impl_939_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_l_945_);
v___x_1004_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v_impl_939_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; lean_object* v_unused_1013_; lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1012_ = lean_ctor_get(v_impl_939_, 4);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_impl_939_, 3);
lean_dec(v_unused_1013_);
v_unused_1014_ = lean_ctor_get(v_impl_939_, 2);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_impl_939_, 1);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_impl_939_, 0);
lean_dec(v_unused_1016_);
v___x_1006_ = v_impl_939_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_dec(v_impl_939_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v_r_946_);
lean_ctor_set(v___x_1006_, 3, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v_v_944_);
lean_ctor_set(v___x_1006_, 1, v_k_943_);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_r_946_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v_size_1024_ = lean_ctor_get(v_impl_939_, 0);
lean_inc(v_size_1024_);
v___x_1025_ = lean_nat_add(v___x_940_, v_size_1024_);
lean_dec(v_size_1024_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 3, v_impl_939_);
lean_ctor_set(v___x_458_, 0, v___x_1025_);
v___x_1027_ = v___x_458_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_impl_939_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_r_456_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
if (lean_obj_tag(v_r_456_) == 0)
{
lean_object* v_l_1029_; 
v_l_1029_ = lean_ctor_get(v_r_456_, 3);
lean_inc(v_l_1029_);
if (lean_obj_tag(v_l_1029_) == 0)
{
lean_object* v_r_1030_; 
v_r_1030_ = lean_ctor_get(v_r_456_, 4);
lean_inc(v_r_1030_);
if (lean_obj_tag(v_r_1030_) == 0)
{
lean_object* v_size_1031_; lean_object* v_k_1032_; lean_object* v_v_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_size_1031_ = lean_ctor_get(v_r_456_, 0);
v_k_1032_ = lean_ctor_get(v_r_456_, 1);
v_v_1033_ = lean_ctor_get(v_r_456_, 2);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; 
v_unused_1047_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_1048_);
v___x_1035_ = v_r_456_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_v_1033_);
lean_inc(v_k_1032_);
lean_inc(v_size_1031_);
lean_dec(v_r_456_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_size_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v_size_1037_ = lean_ctor_get(v_l_1029_, 0);
v___x_1038_ = lean_nat_add(v___x_940_, v_size_1031_);
lean_dec(v_size_1031_);
v___x_1039_ = lean_nat_add(v___x_940_, v_size_1037_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 4, v_l_1029_);
lean_ctor_set(v___x_1035_, 3, v_impl_939_);
lean_ctor_set(v___x_1035_, 2, v_v_454_);
lean_ctor_set(v___x_1035_, 1, v_k_453_);
lean_ctor_set(v___x_1035_, 0, v___x_1039_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_impl_939_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_l_1029_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_r_1030_);
lean_ctor_set(v___x_458_, 3, v___x_1041_);
lean_ctor_set(v___x_458_, 2, v_v_1033_);
lean_ctor_set(v___x_458_, 1, v_k_1032_);
lean_ctor_set(v___x_458_, 0, v___x_1038_);
v___x_1043_ = v___x_458_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_k_1032_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_v_1033_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_r_1030_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_k_1049_; lean_object* v_v_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1073_; 
v_k_1049_ = lean_ctor_get(v_r_456_, 1);
v_v_1050_ = lean_ctor_get(v_r_456_, 2);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1074_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_1076_);
v___x_1052_ = v_r_456_;
v_isShared_1053_ = v_isSharedCheck_1073_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_v_1050_);
lean_inc(v_k_1049_);
lean_dec(v_r_456_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1073_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1069_; 
v_k_1054_ = lean_ctor_get(v_l_1029_, 1);
v_v_1055_ = lean_ctor_get(v_l_1029_, 2);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_l_1029_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1070_ = lean_ctor_get(v_l_1029_, 4);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_l_1029_, 3);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_l_1029_, 0);
lean_dec(v_unused_1072_);
v___x_1057_ = v_l_1029_;
v_isShared_1058_ = v_isSharedCheck_1069_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_v_1055_);
lean_inc(v_k_1054_);
lean_dec(v_l_1029_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1069_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_unsigned_to_nat(3u);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 4, v_r_1030_);
lean_ctor_set(v___x_1057_, 3, v_r_1030_);
lean_ctor_set(v___x_1057_, 2, v_v_454_);
lean_ctor_set(v___x_1057_, 1, v_k_453_);
lean_ctor_set(v___x_1057_, 0, v___x_940_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_r_1030_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_r_1030_);
v___x_1061_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 3, v_r_1030_);
lean_ctor_set(v___x_1052_, 0, v___x_940_);
v___x_1063_ = v___x_1052_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_r_1030_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_r_1030_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_1063_);
lean_ctor_set(v___x_458_, 3, v___x_1061_);
lean_ctor_set(v___x_458_, 2, v_v_1055_);
lean_ctor_set(v___x_458_, 1, v_k_1054_);
lean_ctor_set(v___x_458_, 0, v___x_1059_);
v___x_1065_ = v___x_458_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1077_; 
v_r_1077_ = lean_ctor_get(v_r_456_, 4);
lean_inc(v_r_1077_);
if (lean_obj_tag(v_r_1077_) == 0)
{
lean_object* v_k_1078_; lean_object* v_v_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1090_; 
v_k_1078_ = lean_ctor_get(v_r_456_, 1);
v_v_1079_ = lean_ctor_get(v_r_456_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1091_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_456_, 0);
lean_dec(v_unused_1093_);
v___x_1081_ = v_r_456_;
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_v_1079_);
lean_inc(v_k_1078_);
lean_dec(v_r_456_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_unsigned_to_nat(3u);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 4, v_l_1029_);
lean_ctor_set(v___x_1081_, 2, v_v_454_);
lean_ctor_set(v___x_1081_, 1, v_k_453_);
lean_ctor_set(v___x_1081_, 0, v___x_940_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_1029_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_l_1029_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_r_1077_);
lean_ctor_set(v___x_458_, 3, v___x_1085_);
lean_ctor_set(v___x_458_, 2, v_v_1079_);
lean_ctor_set(v___x_458_, 1, v_k_1078_);
lean_ctor_set(v___x_458_, 0, v___x_1083_);
v___x_1087_ = v___x_458_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_1078_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_r_1077_);
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
else
{
lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1107_; 
v_size_1094_ = lean_ctor_get(v_r_456_, 0);
v_k_1095_ = lean_ctor_get(v_r_456_, 1);
v_v_1096_ = lean_ctor_get(v_r_456_, 2);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_r_456_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; 
v_unused_1108_ = lean_ctor_get(v_r_456_, 4);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_r_456_, 3);
lean_dec(v_unused_1109_);
v___x_1098_ = v_r_456_;
v_isShared_1099_ = v_isSharedCheck_1107_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
lean_inc(v_size_1094_);
lean_dec(v_r_456_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1107_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 3, v_r_1077_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_size_1094_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_r_1077_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_r_1077_);
v___x_1101_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_unsigned_to_nat(2u);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_1101_);
lean_ctor_set(v___x_458_, 3, v_r_1077_);
lean_ctor_set(v___x_458_, 0, v___x_1102_);
v___x_1104_ = v___x_458_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_r_1077_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v___x_1101_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_object* v___x_1111_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 3, v_r_456_);
lean_ctor_set(v___x_458_, 0, v___x_940_);
v___x_1111_ = v___x_458_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_r_456_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_456_);
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
}
else
{
return v_t_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object* v_k_1115_, lean_object* v_t_1116_){
_start:
{
uint64_t v_k_boxed_1117_; lean_object* v_res_1118_; 
v_k_boxed_1117_ = lean_unbox_uint64(v_k_1115_);
lean_dec_ref(v_k_1115_);
v_res_1118_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_1117_, v_t_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object* v_t_1119_, uint64_t v_k_1120_){
_start:
{
if (lean_obj_tag(v_t_1119_) == 0)
{
lean_object* v_k_1121_; lean_object* v_v_1122_; lean_object* v_l_1123_; lean_object* v_r_1124_; uint64_t v___x_1125_; uint8_t v___x_1126_; 
v_k_1121_ = lean_ctor_get(v_t_1119_, 1);
v_v_1122_ = lean_ctor_get(v_t_1119_, 2);
v_l_1123_ = lean_ctor_get(v_t_1119_, 3);
v_r_1124_ = lean_ctor_get(v_t_1119_, 4);
v___x_1125_ = lean_unbox_uint64(v_k_1121_);
v___x_1126_ = lean_uint64_dec_lt(v_k_1120_, v___x_1125_);
if (v___x_1126_ == 0)
{
uint64_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_unbox_uint64(v_k_1121_);
v___x_1128_ = lean_uint64_dec_eq(v_k_1120_, v___x_1127_);
if (v___x_1128_ == 0)
{
v_t_1119_ = v_r_1124_;
goto _start;
}
else
{
lean_object* v___x_1130_; 
lean_inc(v_v_1122_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_v_1122_);
return v___x_1130_;
}
}
else
{
v_t_1119_ = v_l_1123_;
goto _start;
}
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object* v_t_1133_, lean_object* v_k_1134_){
_start:
{
uint64_t v_k_boxed_1135_; lean_object* v_res_1136_; 
v_k_boxed_1135_ = lean_unbox_uint64(v_k_1134_);
lean_dec_ref(v_k_1134_);
v_res_1136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1133_, v_k_boxed_1135_);
lean_dec(v_t_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object* v_state_1137_, uint64_t v_id_1138_, lean_object* v_reason_1139_){
_start:
{
lean_object* v_tokens_1141_; lean_object* v___x_1142_; 
v_tokens_1141_ = lean_ctor_get(v_state_1137_, 0);
v___x_1142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1141_, v_id_1138_);
if (lean_obj_tag(v___x_1142_) == 1)
{
lean_object* v_val_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; size_t v_sz_1146_; size_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_tokens_1150_; uint64_t v_id_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_val_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_val_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v_fst_1144_ = lean_ctor_get(v_val_1143_, 0);
lean_inc(v_fst_1144_);
v_snd_1145_ = lean_ctor_get(v_val_1143_, 1);
lean_inc(v_snd_1145_);
lean_dec(v_val_1143_);
v_sz_1146_ = lean_array_size(v_snd_1145_);
v___x_1147_ = ((size_t)0ULL);
lean_inc(v_reason_1139_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1139_, v_snd_1145_, v_sz_1146_, v___x_1147_, v_state_1137_);
lean_dec(v_snd_1145_);
v___x_1149_ = l_Std_CancellationToken_cancel(v_fst_1144_, v_reason_1139_);
v_tokens_1150_ = lean_ctor_get(v___x_1148_, 0);
v_id_1151_ = lean_ctor_get_uint64(v___x_1148_, sizeof(void*)*1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v___x_1148_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_tokens_1150_);
lean_dec(v___x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_1138_, v_tokens_1150_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set_uint64(v_reuseFailAlloc_1158_, sizeof(void*)*1, v_id_1151_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_dec(v___x_1142_);
lean_dec(v_reason_1139_);
return v_state_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object* v_reason_1160_, lean_object* v_as_1161_, size_t v_sz_1162_, size_t v_i_1163_, lean_object* v_b_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_lt(v_i_1163_, v_sz_1162_);
if (v___x_1166_ == 0)
{
lean_dec(v_reason_1160_);
return v_b_1164_;
}
else
{
lean_object* v_a_1167_; uint64_t v___x_1168_; lean_object* v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; 
v_a_1167_ = lean_array_uget_borrowed(v_as_1161_, v_i_1163_);
v___x_1168_ = lean_unbox_uint64(v_a_1167_);
lean_inc(v_reason_1160_);
v___x_1169_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_b_1164_, v___x_1168_, v_reason_1160_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1163_, v___x_1170_);
v_i_1163_ = v___x_1171_;
v_b_1164_ = v___x_1169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object* v_reason_1173_, lean_object* v_as_1174_, lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1173_, v_as_1174_, v_sz_boxed_1179_, v_i_boxed_1180_, v_b_1177_);
lean_dec_ref(v_as_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object* v_state_1182_, lean_object* v_id_1183_, lean_object* v_reason_1184_, lean_object* v_a_1185_){
_start:
{
uint64_t v_id_boxed_1186_; lean_object* v_res_1187_; 
v_id_boxed_1186_ = lean_unbox_uint64(v_id_1183_);
lean_dec_ref(v_id_1183_);
v_res_1187_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_state_1182_, v_id_boxed_1186_, v_reason_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object* v_00_u03b4_1188_, lean_object* v_t_1189_, uint64_t v_k_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1189_, v_k_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object* v_00_u03b4_1192_, lean_object* v_t_1193_, lean_object* v_k_1194_){
_start:
{
uint64_t v_k_boxed_1195_; lean_object* v_res_1196_; 
v_k_boxed_1195_ = lean_unbox_uint64(v_k_1194_);
lean_dec_ref(v_k_1194_);
v_res_1196_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_1192_, v_t_1193_, v_k_boxed_1195_);
lean_dec(v_t_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object* v_00_u03b2_1197_, uint64_t v_k_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1198_, v_t_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object* v_00_u03b2_1202_, lean_object* v_k_1203_, lean_object* v_t_1204_, lean_object* v_h_1205_){
_start:
{
uint64_t v_k_boxed_1206_; lean_object* v_res_1207_; 
v_k_boxed_1206_ = lean_unbox_uint64(v_k_1203_);
lean_dec_ref(v_k_1203_);
v_res_1207_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_1202_, v_k_boxed_1206_, v_t_1204_, v_h_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(lean_object* v_xs_1208_, uint64_t v_v_1209_, lean_object* v_i_1210_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_array_get_size(v_xs_1208_);
v___x_1212_ = lean_nat_dec_lt(v_i_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v_i_1210_);
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; uint64_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_array_fget_borrowed(v_xs_1208_, v_i_1210_);
v___x_1215_ = lean_unbox_uint64(v___x_1214_);
v___x_1216_ = lean_uint64_dec_eq(v___x_1215_, v_v_1209_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_nat_add(v_i_1210_, v___x_1217_);
lean_dec(v_i_1210_);
v_i_1210_ = v___x_1218_;
goto _start;
}
else
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_i_1210_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_1221_, lean_object* v_v_1222_, lean_object* v_i_1223_){
_start:
{
uint64_t v_v_boxed_1224_; lean_object* v_res_1225_; 
v_v_boxed_1224_ = lean_unbox_uint64(v_v_1222_);
lean_dec_ref(v_v_1222_);
v_res_1225_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(v_xs_1221_, v_v_boxed_1224_, v_i_1223_);
lean_dec_ref(v_xs_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(lean_object* v_xs_1226_, uint64_t v_v_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0_spec__1(v_xs_1226_, v_v_1227_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0___boxed(lean_object* v_xs_1230_, lean_object* v_v_1231_){
_start:
{
uint64_t v_v_boxed_1232_; lean_object* v_res_1233_; 
v_v_boxed_1232_ = lean_unbox_uint64(v_v_1231_);
lean_dec_ref(v_v_1231_);
v_res_1233_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(v_xs_1230_, v_v_boxed_1232_);
lean_dec_ref(v_xs_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(lean_object* v_as_1234_, uint64_t v_a_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Std_CancellationContext_cancel_spec__0_spec__0(v_as_1234_, v_a_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
return v_as_1234_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1238_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = l_Array_eraseIdx___redArg(v_as_1234_, v_val_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00Std_CancellationContext_cancel_spec__0___boxed(lean_object* v_as_1239_, lean_object* v_a_1240_){
_start:
{
uint64_t v_a_boxed_1241_; lean_object* v_res_1242_; 
v_a_boxed_1241_ = lean_unbox_uint64(v_a_1240_);
lean_dec_ref(v_a_1240_);
v_res_1242_ = l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(v_as_1239_, v_a_boxed_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(uint64_t v___x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Array_erase___at___00Std_CancellationContext_cancel_spec__0(v_x_1244_, v___x_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1___boxed(lean_object* v___x_1246_, lean_object* v_x_1247_){
_start:
{
uint64_t v___x_845__boxed_1248_; lean_object* v_res_1249_; 
v___x_845__boxed_1248_ = lean_unbox_uint64(v___x_1246_);
lean_dec_ref(v___x_1246_);
v_res_1249_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1(v___x_845__boxed_1248_, v_x_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(uint64_t v___x_1250_, uint64_t v_k_1251_, lean_object* v_t_1252_){
_start:
{
if (lean_obj_tag(v_t_1252_) == 0)
{
lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_l_1256_; lean_object* v_r_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1281_; 
v_size_1253_ = lean_ctor_get(v_t_1252_, 0);
v_k_1254_ = lean_ctor_get(v_t_1252_, 1);
v_v_1255_ = lean_ctor_get(v_t_1252_, 2);
v_l_1256_ = lean_ctor_get(v_t_1252_, 3);
v_r_1257_ = lean_ctor_get(v_t_1252_, 4);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_t_1252_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1259_ = v_t_1252_;
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_r_1257_);
lean_inc(v_l_1256_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
lean_inc(v_size_1253_);
lean_dec(v_t_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
uint64_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_unbox_uint64(v_k_1254_);
v___x_1262_ = lean_uint64_dec_lt(v_k_1251_, v___x_1261_);
if (v___x_1262_ == 0)
{
uint64_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_unbox_uint64(v_k_1254_);
v___x_1264_ = lean_uint64_dec_eq(v_k_1251_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_1250_, v_k_1251_, v_r_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 4, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_l_1256_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
else
{
lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec(v_k_1254_);
v___f_1269_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
v___x_1270_ = lean_box_uint64(v___x_1250_);
v___f_1271_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1271_, 0, v___x_1270_);
v___x_1272_ = l_Prod_map___redArg(v___f_1269_, v___f_1271_, v_v_1255_);
v___x_1273_ = lean_box_uint64(v_k_1251_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 2, v___x_1272_);
lean_ctor_set(v___x_1259_, 1, v___x_1273_);
v___x_1275_ = v___x_1259_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_l_1256_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_r_1257_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_1250_, v_k_1251_, v_l_1256_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 3, v___x_1277_);
v___x_1279_ = v___x_1259_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_r_1257_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
return v_t_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1___boxed(lean_object* v___x_1282_, lean_object* v_k_1283_, lean_object* v_t_1284_){
_start:
{
uint64_t v___x_854__boxed_1285_; uint64_t v_k_boxed_1286_; lean_object* v_res_1287_; 
v___x_854__boxed_1285_ = lean_unbox_uint64(v___x_1282_);
lean_dec_ref(v___x_1282_);
v_k_boxed_1286_ = lean_unbox_uint64(v_k_1283_);
lean_dec_ref(v_k_1283_);
v_res_1287_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v___x_854__boxed_1285_, v_k_boxed_1286_, v_t_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t v_id_1288_, lean_object* v_reason_1289_, lean_object* v_parent_x3f_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___y_1296_; 
v___x_1293_ = lean_st_ref_get(v___y_1291_);
v___x_1294_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v___x_1293_, v_id_1288_, v_reason_1289_);
if (lean_obj_tag(v_parent_x3f_1290_) == 0)
{
v___y_1296_ = v___x_1294_;
goto v___jp_1295_;
}
else
{
lean_object* v_val_1299_; lean_object* v_tokens_1300_; uint64_t v_id_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1310_; 
v_val_1299_ = lean_ctor_get(v_parent_x3f_1290_, 0);
v_tokens_1300_ = lean_ctor_get(v___x_1294_, 0);
v_id_1301_ = lean_ctor_get_uint64(v___x_1294_, sizeof(void*)*1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1303_ = v___x_1294_;
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_tokens_1300_);
lean_dec(v___x_1294_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
uint64_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1305_ = lean_unbox_uint64(v_val_1299_);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_cancel_spec__1(v_id_1288_, v___x_1305_, v_tokens_1300_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
lean_ctor_set_uint64(v_reuseFailAlloc_1309_, sizeof(void*)*1, v_id_1301_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v___y_1296_ = v___x_1308_;
goto v___jp_1295_;
}
}
}
v___jp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_st_ref_swap(v___y_1291_, v___y_1296_);
lean_dec(v___x_1298_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object* v_id_1311_, lean_object* v_reason_1312_, lean_object* v_parent_x3f_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint64_t v_id_boxed_1316_; lean_object* v_res_1317_; 
v_id_boxed_1316_ = lean_unbox_uint64(v_id_1311_);
lean_dec_ref(v_id_1311_);
v_res_1317_ = l_Std_CancellationContext_cancel___lam__0(v_id_boxed_1316_, v_reason_1312_, v_parent_x3f_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec(v_parent_x3f_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object* v_x_1318_, lean_object* v_reason_1319_){
_start:
{
lean_object* v_state_1321_; lean_object* v_token_1322_; uint64_t v_id_1323_; lean_object* v_parent_x3f_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; uint8_t v___x_1327_; 
v_state_1321_ = lean_ctor_get(v_x_1318_, 0);
lean_inc_ref(v_state_1321_);
v_token_1322_ = lean_ctor_get(v_x_1318_, 1);
lean_inc_ref(v_token_1322_);
v_id_1323_ = lean_ctor_get_uint64(v_x_1318_, sizeof(void*)*3);
v_parent_x3f_1324_ = lean_ctor_get(v_x_1318_, 2);
lean_inc(v_parent_x3f_1324_);
lean_dec_ref(v_x_1318_);
v___x_1325_ = lean_box_uint64(v_id_1323_);
v___f_1326_ = lean_alloc_closure((void*)(l_Std_CancellationContext_cancel___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1326_, 0, v___x_1325_);
lean_closure_set(v___f_1326_, 1, v_reason_1319_);
lean_closure_set(v___f_1326_, 2, v_parent_x3f_1324_);
v___x_1327_ = l_Std_CancellationToken_isCancelled(v_token_1322_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1321_, v___f_1326_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v___f_1326_);
lean_dec_ref(v_state_1321_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object* v_x_1330_, lean_object* v_reason_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_CancellationContext_cancel(v_x_1330_, v_reason_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object* v_x_1334_){
_start:
{
lean_object* v_token_1336_; uint8_t v___x_1337_; 
v_token_1336_ = lean_ctor_get(v_x_1334_, 1);
lean_inc_ref(v_token_1336_);
lean_dec_ref(v_x_1334_);
v___x_1337_ = l_Std_CancellationToken_isCancelled(v_token_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object* v_x_1338_, lean_object* v_a_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Std_CancellationContext_isCancelled(v_x_1338_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object* v_x_1342_){
_start:
{
lean_object* v_token_1344_; lean_object* v___x_1345_; 
v_token_1344_ = lean_ctor_get(v_x_1342_, 1);
lean_inc_ref(v_token_1344_);
lean_dec_ref(v_x_1342_);
v___x_1345_ = l_Std_CancellationToken_getCancellationReason(v_token_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object* v_x_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_CancellationContext_getCancellationReason(v_x_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object* v_x_1349_){
_start:
{
lean_object* v_token_1351_; lean_object* v___x_1352_; 
v_token_1351_ = lean_ctor_get(v_x_1349_, 1);
lean_inc_ref(v_token_1351_);
lean_dec_ref(v_x_1349_);
v___x_1352_ = l_Std_CancellationToken_wait(v_token_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object* v_x_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_CancellationContext_done(v_x_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object* v_x_1356_){
_start:
{
lean_object* v_token_1357_; lean_object* v___x_1358_; 
v_token_1357_ = lean_ctor_get(v_x_1356_, 1);
lean_inc_ref(v_token_1357_);
lean_dec_ref(v_x_1356_);
v___x_1358_ = l_Std_CancellationToken_selector(v_token_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object* v_state_1359_, uint64_t v_id_1360_){
_start:
{
lean_object* v_tokens_1361_; lean_object* v___x_1362_; 
v_tokens_1361_ = lean_ctor_get(v_state_1359_, 0);
v___x_1362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1361_, v_id_1360_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
return v___x_1363_;
}
else
{
lean_object* v_val_1364_; lean_object* v_snd_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_val_1364_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v___x_1362_, 1);
v_snd_1365_ = lean_ctor_get(v_val_1364_, 1);
lean_inc(v_snd_1365_);
lean_dec(v_val_1364_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v_snd_1365_);
v___x_1368_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v_snd_1365_);
v___x_1369_ = lean_unsigned_to_nat(1u);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1371_ == 0)
{
if (v___x_1368_ == 0)
{
lean_dec(v_snd_1365_);
return v___x_1370_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1367_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1359_, v_snd_1365_, v___x_1372_, v___x_1373_, v___x_1366_);
lean_dec(v_snd_1365_);
v___x_1375_ = lean_nat_add(v___x_1370_, v___x_1374_);
lean_dec(v___x_1374_);
return v___x_1375_;
}
}
else
{
size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = lean_usize_of_nat(v___x_1367_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1359_, v_snd_1365_, v___x_1376_, v___x_1377_, v___x_1366_);
lean_dec(v_snd_1365_);
v___x_1379_ = lean_nat_add(v___x_1370_, v___x_1378_);
lean_dec(v___x_1378_);
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object* v_state_1380_, lean_object* v_as_1381_, size_t v_i_1382_, size_t v_stop_1383_, lean_object* v_b_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_eq(v_i_1382_, v_stop_1383_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; uint64_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; 
v___x_1386_ = lean_array_uget_borrowed(v_as_1381_, v_i_1382_);
v___x_1387_ = lean_unbox_uint64(v___x_1386_);
v___x_1388_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1380_, v___x_1387_);
v___x_1389_ = lean_nat_add(v_b_1384_, v___x_1388_);
lean_dec(v___x_1388_);
lean_dec(v_b_1384_);
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1382_, v___x_1390_);
v_i_1382_ = v___x_1391_;
v_b_1384_ = v___x_1389_;
goto _start;
}
else
{
return v_b_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object* v_state_1393_, lean_object* v_as_1394_, lean_object* v_i_1395_, lean_object* v_stop_1396_, lean_object* v_b_1397_){
_start:
{
size_t v_i_boxed_1398_; size_t v_stop_boxed_1399_; lean_object* v_res_1400_; 
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_stop_boxed_1399_ = lean_unbox_usize(v_stop_1396_);
lean_dec(v_stop_1396_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1393_, v_as_1394_, v_i_boxed_1398_, v_stop_boxed_1399_, v_b_1397_);
lean_dec_ref(v_as_1394_);
lean_dec_ref(v_state_1393_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object* v_state_1401_, lean_object* v_id_1402_){
_start:
{
uint64_t v_id_boxed_1403_; lean_object* v_res_1404_; 
v_id_boxed_1403_ = lean_unbox_uint64(v_id_1402_);
lean_dec_ref(v_id_1402_);
v_res_1404_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1401_, v_id_boxed_1403_);
lean_dec_ref(v_state_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t v_id_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_st_ref_get(v___y_1406_);
v___x_1409_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v___x_1408_, v_id_1405_);
lean_dec(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object* v_id_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint64_t v_id_boxed_1413_; lean_object* v_res_1414_; 
v_id_boxed_1413_ = lean_unbox_uint64(v_id_1410_);
lean_dec_ref(v_id_1410_);
v_res_1414_ = l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_1413_, v___y_1411_);
lean_dec(v___y_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object* v_x_1415_){
_start:
{
lean_object* v_state_1417_; uint64_t v_id_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
v_state_1417_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_state_1417_);
v_id_1418_ = lean_ctor_get_uint64(v_x_1415_, sizeof(void*)*3);
lean_dec_ref(v_x_1415_);
v___x_1419_ = lean_box_uint64(v_id_1418_);
v___f_1420_ = lean_alloc_closure((void*)(l_Std_CancellationContext_countAliveTokens___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1420_, 0, v___x_1419_);
v___x_1421_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1417_, v___f_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object* v_x_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_CancellationContext_countAliveTokens(v_x_1422_);
return v_res_1424_;
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
