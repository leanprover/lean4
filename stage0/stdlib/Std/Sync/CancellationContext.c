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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_304_; lean_object* v___x_305_; uint64_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint64_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
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
v___x_313_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_304_);
lean_ctor_set_uint64(v___x_313_, sizeof(void*)*2, v___x_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_CancellationContext_new();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object* v_00_u03b2_316_, uint64_t v_k_317_, lean_object* v_v_318_, lean_object* v_t_319_, lean_object* v_hl_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_317_, v_v_318_, v_t_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object* v_00_u03b2_322_, lean_object* v_k_323_, lean_object* v_v_324_, lean_object* v_t_325_, lean_object* v_hl_326_){
_start:
{
uint64_t v_k_boxed_327_; lean_object* v_res_328_; 
v_k_boxed_327_ = lean_unbox_uint64(v_k_323_);
lean_dec_ref(v_k_323_);
v_res_328_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(v_00_u03b2_322_, v_k_boxed_327_, v_v_324_, v_t_325_, v_hl_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object* v_mutex_329_, lean_object* v_k_330_){
_start:
{
lean_object* v_ref_332_; lean_object* v_mutex_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_ref_332_ = lean_ctor_get(v_mutex_329_, 0);
lean_inc(v_ref_332_);
v_mutex_333_ = lean_ctor_get(v_mutex_329_, 1);
lean_inc(v_mutex_333_);
lean_dec_ref(v_mutex_329_);
v___x_334_ = lean_io_basemutex_lock(v_mutex_333_);
v___x_335_ = lean_apply_2(v_k_330_, v_ref_332_, lean_box(0));
v___x_336_ = lean_io_basemutex_unlock(v_mutex_333_);
lean_dec(v_mutex_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object* v_mutex_337_, lean_object* v_k_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_337_, v_k_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_mutex_343_, lean_object* v_k_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_mutex_343_, v_k_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_mutex_349_, lean_object* v_k_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(v_00_u03b1_347_, v_00_u03b2_348_, v_mutex_349_, v_k_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object* v_x_353_){
_start:
{
lean_inc_ref(v_x_353_);
return v_x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t v___x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_box_uint64(v___x_356_);
v___x_359_ = lean_array_push(v_x_357_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object* v___x_360_, lean_object* v_x_361_){
_start:
{
uint64_t v___x_1350__boxed_362_; lean_object* v_res_363_; 
v___x_1350__boxed_362_ = lean_unbox_uint64(v___x_360_);
lean_dec_ref(v___x_360_);
v_res_363_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1350__boxed_362_, v_x_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t v___x_365_, uint64_t v_k_366_, lean_object* v_t_367_){
_start:
{
if (lean_obj_tag(v_t_367_) == 0)
{
lean_object* v_size_368_; lean_object* v_k_369_; lean_object* v_v_370_; lean_object* v_l_371_; lean_object* v_r_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_396_; 
v_size_368_ = lean_ctor_get(v_t_367_, 0);
v_k_369_ = lean_ctor_get(v_t_367_, 1);
v_v_370_ = lean_ctor_get(v_t_367_, 2);
v_l_371_ = lean_ctor_get(v_t_367_, 3);
v_r_372_ = lean_ctor_get(v_t_367_, 4);
v_isSharedCheck_396_ = !lean_is_exclusive(v_t_367_);
if (v_isSharedCheck_396_ == 0)
{
v___x_374_ = v_t_367_;
v_isShared_375_ = v_isSharedCheck_396_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_r_372_);
lean_inc(v_l_371_);
lean_inc(v_v_370_);
lean_inc(v_k_369_);
lean_inc(v_size_368_);
lean_dec(v_t_367_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_396_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint64_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_unbox_uint64(v_k_369_);
v___x_377_ = lean_uint64_dec_lt(v_k_366_, v___x_376_);
if (v___x_377_ == 0)
{
uint64_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_unbox_uint64(v_k_369_);
v___x_379_ = lean_uint64_dec_eq(v_k_366_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_365_, v_k_366_, v_r_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v___x_380_);
v___x_382_ = v___x_374_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_size_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_k_369_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_v_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_l_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec(v_k_369_);
v___f_384_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
v___x_385_ = lean_box_uint64(v___x_365_);
v___f_386_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(v___f_386_, 0, v___x_385_);
v___x_387_ = l_Prod_map___redArg(v___f_384_, v___f_386_, v_v_370_);
v___x_388_ = lean_box_uint64(v_k_366_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 2, v___x_387_);
lean_ctor_set(v___x_374_, 1, v___x_388_);
v___x_390_ = v___x_374_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_size_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_l_371_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_r_372_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_365_, v_k_366_, v_l_371_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 3, v___x_392_);
v___x_394_ = v___x_374_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_size_368_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_369_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_370_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_r_372_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
return v_t_367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object* v___x_397_, lean_object* v_k_398_, lean_object* v_t_399_){
_start:
{
uint64_t v___x_1362__boxed_400_; uint64_t v_k_boxed_401_; lean_object* v_res_402_; 
v___x_1362__boxed_400_ = lean_unbox_uint64(v___x_397_);
lean_dec_ref(v___x_397_);
v_k_boxed_401_ = lean_unbox_uint64(v_k_398_);
lean_dec_ref(v_k_398_);
v_res_402_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1362__boxed_400_, v_k_boxed_401_, v_t_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object* v_token_403_, uint64_t v_id_404_, lean_object* v_state_405_, lean_object* v_root_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Std_CancellationToken_isCancelled(v_token_403_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_tokens_412_; uint64_t v_id_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_428_; 
v___x_410_ = l_Std_CancellationToken_new();
v___x_411_ = lean_st_ref_get(v___y_407_);
v_tokens_412_ = lean_ctor_get(v___x_411_, 0);
v_id_413_ = lean_ctor_get_uint64(v___x_411_, sizeof(void*)*1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_428_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_428_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tokens_412_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_428_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; lean_object* v___x_424_; 
v___x_417_ = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(v___x_410_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_410_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_413_, v___x_418_, v_tokens_412_);
v___x_420_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_413_, v_id_404_, v___x_419_);
v___x_421_ = 1ULL;
v___x_422_ = lean_uint64_add(v_id_413_, v___x_421_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_420_);
v___x_424_ = v___x_415_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_420_);
v___x_424_ = v_reuseFailAlloc_427_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_ctor_set_uint64(v___x_424_, sizeof(void*)*1, v___x_422_);
v___x_425_ = lean_st_ref_set(v___y_407_, v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_426_, 0, v_state_405_);
lean_ctor_set(v___x_426_, 1, v___x_410_);
lean_ctor_set_uint64(v___x_426_, sizeof(void*)*2, v_id_413_);
return v___x_426_;
}
}
}
else
{
lean_dec_ref(v_state_405_);
lean_inc_ref(v_root_406_);
return v_root_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object* v_token_429_, lean_object* v_id_430_, lean_object* v_state_431_, lean_object* v_root_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint64_t v_id_boxed_435_; lean_object* v_res_436_; 
v_id_boxed_435_ = lean_unbox_uint64(v_id_430_);
lean_dec_ref(v_id_430_);
v_res_436_ = l_Std_CancellationContext_fork___lam__0(v_token_429_, v_id_boxed_435_, v_state_431_, v_root_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v_root_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object* v_root_437_){
_start:
{
lean_object* v_state_439_; lean_object* v_token_440_; uint64_t v_id_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
v_state_439_ = lean_ctor_get(v_root_437_, 0);
lean_inc_ref_n(v_state_439_, 2);
v_token_440_ = lean_ctor_get(v_root_437_, 1);
lean_inc_ref(v_token_440_);
v_id_441_ = lean_ctor_get_uint64(v_root_437_, sizeof(void*)*2);
v___x_442_ = lean_box_uint64(v_id_441_);
v___f_443_ = lean_alloc_closure((void*)(l_Std_CancellationContext_fork___lam__0___boxed), 6, 4);
lean_closure_set(v___f_443_, 0, v_token_440_);
lean_closure_set(v___f_443_, 1, v___x_442_);
lean_closure_set(v___f_443_, 2, v_state_439_);
lean_closure_set(v___f_443_, 3, v_root_437_);
v___x_444_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_439_, v___f_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object* v_root_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_CancellationContext_fork(v_root_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t v_k_448_, lean_object* v_t_449_){
_start:
{
if (lean_obj_tag(v_t_449_) == 0)
{
lean_object* v_k_450_; lean_object* v_v_451_; lean_object* v_l_452_; lean_object* v_r_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_1110_; 
v_k_450_ = lean_ctor_get(v_t_449_, 1);
v_v_451_ = lean_ctor_get(v_t_449_, 2);
v_l_452_ = lean_ctor_get(v_t_449_, 3);
v_r_453_ = lean_ctor_get(v_t_449_, 4);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_t_449_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v_t_449_, 0);
lean_dec(v_unused_1111_);
v___x_455_ = v_t_449_;
v_isShared_456_ = v_isSharedCheck_1110_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_r_453_);
lean_inc(v_l_452_);
lean_inc(v_v_451_);
lean_inc(v_k_450_);
lean_dec(v_t_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_1110_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint64_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unbox_uint64(v_k_450_);
v___x_458_ = lean_uint64_dec_lt(v_k_448_, v___x_457_);
if (v___x_458_ == 0)
{
uint64_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_unbox_uint64(v_k_450_);
v___x_460_ = lean_uint64_dec_eq(v_k_448_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v_impl_461_; lean_object* v___x_462_; 
v_impl_461_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_448_, v_r_453_);
v___x_462_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_461_) == 0)
{
if (lean_obj_tag(v_l_452_) == 0)
{
lean_object* v_size_463_; lean_object* v_size_464_; lean_object* v_k_465_; lean_object* v_v_466_; lean_object* v_l_467_; lean_object* v_r_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_size_463_ = lean_ctor_get(v_impl_461_, 0);
lean_inc(v_size_463_);
v_size_464_ = lean_ctor_get(v_l_452_, 0);
v_k_465_ = lean_ctor_get(v_l_452_, 1);
v_v_466_ = lean_ctor_get(v_l_452_, 2);
v_l_467_ = lean_ctor_get(v_l_452_, 3);
v_r_468_ = lean_ctor_get(v_l_452_, 4);
lean_inc(v_r_468_);
v___x_469_ = lean_unsigned_to_nat(3u);
v___x_470_ = lean_nat_mul(v___x_469_, v_size_463_);
v___x_471_ = lean_nat_dec_lt(v___x_470_, v_size_464_);
lean_dec(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec(v_r_468_);
v___x_472_ = lean_nat_add(v___x_462_, v_size_464_);
v___x_473_ = lean_nat_add(v___x_472_, v_size_463_);
lean_dec(v_size_463_);
lean_dec(v___x_472_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_impl_461_);
lean_ctor_set(v___x_455_, 0, v___x_473_);
v___x_475_ = v___x_455_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_impl_461_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_542_; 
lean_inc(v_l_467_);
lean_inc(v_v_466_);
lean_inc(v_k_465_);
lean_inc(v_size_464_);
v_isSharedCheck_542_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; lean_object* v_unused_544_; lean_object* v_unused_545_; lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_543_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_547_);
v___x_478_ = v_l_452_;
v_isShared_479_ = v_isSharedCheck_542_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_l_452_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_542_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_size_480_; lean_object* v_size_481_; lean_object* v_k_482_; lean_object* v_v_483_; lean_object* v_l_484_; lean_object* v_r_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_size_480_ = lean_ctor_get(v_l_467_, 0);
v_size_481_ = lean_ctor_get(v_r_468_, 0);
v_k_482_ = lean_ctor_get(v_r_468_, 1);
v_v_483_ = lean_ctor_get(v_r_468_, 2);
v_l_484_ = lean_ctor_get(v_r_468_, 3);
v_r_485_ = lean_ctor_get(v_r_468_, 4);
v___x_486_ = lean_unsigned_to_nat(2u);
v___x_487_ = lean_nat_mul(v___x_486_, v_size_480_);
v___x_488_ = lean_nat_dec_lt(v_size_481_, v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_517_; 
lean_inc(v_r_485_);
lean_inc(v_l_484_);
lean_inc(v_v_483_);
lean_inc(v_k_482_);
v_isSharedCheck_517_ = !lean_is_exclusive(v_r_468_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_518_ = lean_ctor_get(v_r_468_, 4);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_r_468_, 3);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_r_468_, 2);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_r_468_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_r_468_, 0);
lean_dec(v_unused_522_);
v___x_490_ = v_r_468_;
v_isShared_491_ = v_isSharedCheck_517_;
goto v_resetjp_489_;
}
else
{
lean_dec(v_r_468_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_517_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___x_505_; lean_object* v___y_507_; 
v___x_492_ = lean_nat_add(v___x_462_, v_size_464_);
lean_dec(v_size_464_);
v___x_493_ = lean_nat_add(v___x_492_, v_size_463_);
lean_dec(v___x_492_);
v___x_505_ = lean_nat_add(v___x_462_, v_size_480_);
if (lean_obj_tag(v_l_484_) == 0)
{
lean_object* v_size_515_; 
v_size_515_ = lean_ctor_get(v_l_484_, 0);
lean_inc(v_size_515_);
v___y_507_ = v_size_515_;
goto v___jp_506_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___y_507_ = v___x_516_;
goto v___jp_506_;
}
v___jp_494_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_nat_add(v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec(v___y_496_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 4, v_impl_461_);
lean_ctor_set(v___x_490_, 3, v_r_485_);
lean_ctor_set(v___x_490_, 2, v_v_451_);
lean_ctor_set(v___x_490_, 1, v_k_450_);
lean_ctor_set(v___x_490_, 0, v___x_498_);
v___x_500_ = v___x_490_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_r_485_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_impl_461_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 4, v___x_500_);
lean_ctor_set(v___x_478_, 3, v___y_495_);
lean_ctor_set(v___x_478_, 2, v_v_483_);
lean_ctor_set(v___x_478_, 1, v_k_482_);
lean_ctor_set(v___x_478_, 0, v___x_493_);
v___x_502_ = v___x_478_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v___y_495_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_nat_add(v___x_505_, v___y_507_);
lean_dec(v___y_507_);
lean_dec(v___x_505_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_484_);
lean_ctor_set(v___x_455_, 3, v_l_467_);
lean_ctor_set(v___x_455_, 2, v_v_466_);
lean_ctor_set(v___x_455_, 1, v_k_465_);
lean_ctor_set(v___x_455_, 0, v___x_508_);
v___x_510_ = v___x_455_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_465_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_466_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_l_467_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_l_484_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_nat_add(v___x_462_, v_size_463_);
lean_dec(v_size_463_);
if (lean_obj_tag(v_r_485_) == 0)
{
lean_object* v_size_512_; 
v_size_512_ = lean_ctor_get(v_r_485_, 0);
lean_inc(v_size_512_);
v___y_495_ = v___x_510_;
v___y_496_ = v___x_511_;
v___y_497_ = v_size_512_;
goto v___jp_494_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___y_495_ = v___x_510_;
v___y_496_ = v___x_511_;
v___y_497_ = v___x_513_;
goto v___jp_494_;
}
}
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
lean_del_object(v___x_455_);
v___x_523_ = lean_nat_add(v___x_462_, v_size_464_);
lean_dec(v_size_464_);
v___x_524_ = lean_nat_add(v___x_523_, v_size_463_);
lean_dec(v___x_523_);
v___x_525_ = lean_nat_add(v___x_462_, v_size_463_);
lean_dec(v_size_463_);
v___x_526_ = lean_nat_add(v___x_525_, v_size_481_);
lean_dec(v___x_525_);
lean_inc_ref(v_impl_461_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 4, v_impl_461_);
lean_ctor_set(v___x_478_, 3, v_r_468_);
lean_ctor_set(v___x_478_, 2, v_v_451_);
lean_ctor_set(v___x_478_, 1, v_k_450_);
lean_ctor_set(v___x_478_, 0, v___x_526_);
v___x_528_ = v___x_478_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_r_468_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_impl_461_);
v___x_528_ = v_reuseFailAlloc_541_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_isSharedCheck_535_ = !lean_is_exclusive(v_impl_461_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_536_ = lean_ctor_get(v_impl_461_, 4);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_impl_461_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_impl_461_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_461_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_impl_461_, 0);
lean_dec(v_unused_540_);
v___x_530_ = v_impl_461_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_dec(v_impl_461_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v___x_528_);
lean_ctor_set(v___x_530_, 3, v_l_467_);
lean_ctor_set(v___x_530_, 2, v_v_466_);
lean_ctor_set(v___x_530_, 1, v_k_465_);
lean_ctor_set(v___x_530_, 0, v___x_524_);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_465_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_466_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_l_467_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v___x_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v_size_548_ = lean_ctor_get(v_impl_461_, 0);
lean_inc(v_size_548_);
v___x_549_ = lean_nat_add(v___x_462_, v_size_548_);
lean_dec(v_size_548_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_impl_461_);
lean_ctor_set(v___x_455_, 0, v___x_549_);
v___x_551_ = v___x_455_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_impl_461_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
if (lean_obj_tag(v_l_452_) == 0)
{
lean_object* v_l_553_; 
v_l_553_ = lean_ctor_get(v_l_452_, 3);
if (lean_obj_tag(v_l_553_) == 0)
{
lean_object* v_r_554_; 
lean_inc_ref(v_l_553_);
v_r_554_ = lean_ctor_get(v_l_452_, 4);
lean_inc(v_r_554_);
if (lean_obj_tag(v_r_554_) == 0)
{
lean_object* v_size_555_; lean_object* v_k_556_; lean_object* v_v_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_size_555_ = lean_ctor_get(v_l_452_, 0);
v_k_556_ = lean_ctor_get(v_l_452_, 1);
v_v_557_ = lean_ctor_get(v_l_452_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; 
v_unused_571_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_572_);
v___x_559_ = v_l_452_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_v_557_);
lean_inc(v_k_556_);
lean_inc(v_size_555_);
lean_dec(v_l_452_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_size_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v_size_561_ = lean_ctor_get(v_r_554_, 0);
v___x_562_ = lean_nat_add(v___x_462_, v_size_555_);
lean_dec(v_size_555_);
v___x_563_ = lean_nat_add(v___x_462_, v_size_561_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 4, v_impl_461_);
lean_ctor_set(v___x_559_, 3, v_r_554_);
lean_ctor_set(v___x_559_, 2, v_v_451_);
lean_ctor_set(v___x_559_, 1, v_k_450_);
lean_ctor_set(v___x_559_, 0, v___x_563_);
v___x_565_ = v___x_559_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_r_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_impl_461_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_565_);
lean_ctor_set(v___x_455_, 3, v_l_553_);
lean_ctor_set(v___x_455_, 2, v_v_557_);
lean_ctor_set(v___x_455_, 1, v_k_556_);
lean_ctor_set(v___x_455_, 0, v___x_562_);
v___x_567_ = v___x_455_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_l_553_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_k_573_; lean_object* v_v_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_k_573_ = lean_ctor_get(v_l_452_, 1);
v_v_574_ = lean_ctor_get(v_l_452_, 2);
v_isSharedCheck_585_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_586_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_588_);
v___x_576_ = v_l_452_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_v_574_);
lean_inc(v_k_573_);
lean_dec(v_l_452_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(3u);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_r_554_);
lean_ctor_set(v___x_576_, 2, v_v_451_);
lean_ctor_set(v___x_576_, 1, v_k_450_);
lean_ctor_set(v___x_576_, 0, v___x_462_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_r_554_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_r_554_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_580_);
lean_ctor_set(v___x_455_, 3, v_l_553_);
lean_ctor_set(v___x_455_, 2, v_v_574_);
lean_ctor_set(v___x_455_, 1, v_k_573_);
lean_ctor_set(v___x_455_, 0, v___x_578_);
v___x_582_ = v___x_455_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_k_573_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_v_574_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_l_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
else
{
lean_object* v_r_589_; 
v_r_589_ = lean_ctor_get(v_l_452_, 4);
lean_inc(v_r_589_);
if (lean_obj_tag(v_r_589_) == 0)
{
lean_object* v_k_590_; lean_object* v_v_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
lean_inc(v_l_553_);
v_k_590_ = lean_ctor_get(v_l_452_, 1);
v_v_591_ = lean_ctor_get(v_l_452_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_615_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_617_);
v___x_593_ = v_l_452_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_v_591_);
lean_inc(v_k_590_);
lean_dec(v_l_452_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_k_595_; lean_object* v_v_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_610_; 
v_k_595_ = lean_ctor_get(v_r_589_, 1);
v_v_596_ = lean_ctor_get(v_r_589_, 2);
v_isSharedCheck_610_ = !lean_is_exclusive(v_r_589_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; lean_object* v_unused_613_; 
v_unused_611_ = lean_ctor_get(v_r_589_, 4);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_r_589_, 3);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_r_589_, 0);
lean_dec(v_unused_613_);
v___x_598_ = v_r_589_;
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_v_596_);
lean_inc(v_k_595_);
lean_dec(v_r_589_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(3u);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 4, v_l_553_);
lean_ctor_set(v___x_598_, 3, v_l_553_);
lean_ctor_set(v___x_598_, 2, v_v_591_);
lean_ctor_set(v___x_598_, 1, v_k_590_);
lean_ctor_set(v___x_598_, 0, v___x_462_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_590_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_591_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_l_553_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_l_553_);
v___x_602_ = v_reuseFailAlloc_609_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_l_553_);
lean_ctor_set(v___x_593_, 2, v_v_451_);
lean_ctor_set(v___x_593_, 1, v_k_450_);
lean_ctor_set(v___x_593_, 0, v___x_462_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_l_553_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_l_553_);
v___x_604_ = v_reuseFailAlloc_608_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_604_);
lean_ctor_set(v___x_455_, 3, v___x_602_);
lean_ctor_set(v___x_455_, 2, v_v_596_);
lean_ctor_set(v___x_455_, 1, v_k_595_);
lean_ctor_set(v___x_455_, 0, v___x_600_);
v___x_606_ = v___x_455_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_k_595_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_v_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_unsigned_to_nat(2u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_589_);
lean_ctor_set(v___x_455_, 0, v___x_618_);
v___x_620_ = v___x_455_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_r_589_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_623_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_452_);
lean_ctor_set(v___x_455_, 0, v___x_462_);
v___x_623_ = v___x_455_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_l_452_);
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
lean_del_object(v___x_455_);
lean_dec(v_v_451_);
lean_dec(v_k_450_);
if (lean_obj_tag(v_l_452_) == 0)
{
if (lean_obj_tag(v_r_453_) == 0)
{
lean_object* v_size_625_; lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v_l_628_; lean_object* v_r_629_; lean_object* v_size_630_; lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_size_625_ = lean_ctor_get(v_l_452_, 0);
v_k_626_ = lean_ctor_get(v_l_452_, 1);
v_v_627_ = lean_ctor_get(v_l_452_, 2);
v_l_628_ = lean_ctor_get(v_l_452_, 3);
v_r_629_ = lean_ctor_get(v_l_452_, 4);
lean_inc(v_r_629_);
v_size_630_ = lean_ctor_get(v_r_453_, 0);
v_k_631_ = lean_ctor_get(v_r_453_, 1);
v_v_632_ = lean_ctor_get(v_r_453_, 2);
v_l_633_ = lean_ctor_get(v_r_453_, 3);
lean_inc(v_l_633_);
v_r_634_ = lean_ctor_get(v_r_453_, 4);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_dec_lt(v_size_625_, v_size_630_);
if (v___x_636_ == 0)
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_773_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_777_);
v___x_638_ = v_l_452_;
v_isShared_639_ = v_isSharedCheck_772_;
goto v_resetjp_637_;
}
else
{
lean_dec(v_l_452_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_772_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v_tree_641_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_626_, v_v_627_, v_l_628_, v_r_629_);
v_tree_641_ = lean_ctor_get(v___x_640_, 2);
lean_inc(v_tree_641_);
if (lean_obj_tag(v_tree_641_) == 0)
{
lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v_size_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_k_642_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_k_642_);
v_v_643_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_v_643_);
lean_dec_ref(v___x_640_);
v_size_644_ = lean_ctor_get(v_tree_641_, 0);
v___x_645_ = lean_unsigned_to_nat(3u);
v___x_646_ = lean_nat_mul(v___x_645_, v_size_644_);
v___x_647_ = lean_nat_dec_lt(v___x_646_, v_size_630_);
lean_dec(v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_l_633_);
v___x_648_ = lean_nat_add(v___x_635_, v_size_644_);
v___x_649_ = lean_nat_add(v___x_648_, v_size_630_);
lean_dec(v___x_648_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_r_453_);
lean_ctor_set(v___x_638_, 3, v_tree_641_);
lean_ctor_set(v___x_638_, 2, v_v_643_);
lean_ctor_set(v___x_638_, 1, v_k_642_);
lean_ctor_set(v___x_638_, 0, v___x_649_);
v___x_651_ = v___x_638_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_tree_641_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_r_453_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
else
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_707_; 
lean_inc(v_r_634_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
lean_inc(v_size_630_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_708_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_r_453_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_r_453_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_712_);
v___x_654_ = v_r_453_;
v_isShared_655_ = v_isSharedCheck_707_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_r_453_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_707_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_size_656_; lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v_l_659_; lean_object* v_r_660_; lean_object* v_size_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_size_656_ = lean_ctor_get(v_l_633_, 0);
v_k_657_ = lean_ctor_get(v_l_633_, 1);
v_v_658_ = lean_ctor_get(v_l_633_, 2);
v_l_659_ = lean_ctor_get(v_l_633_, 3);
v_r_660_ = lean_ctor_get(v_l_633_, 4);
v_size_661_ = lean_ctor_get(v_r_634_, 0);
v___x_662_ = lean_unsigned_to_nat(2u);
v___x_663_ = lean_nat_mul(v___x_662_, v_size_661_);
v___x_664_ = lean_nat_dec_lt(v_size_656_, v___x_663_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_692_; 
lean_inc(v_r_660_);
lean_inc(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v_isSharedCheck_692_ = !lean_is_exclusive(v_l_633_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_693_ = lean_ctor_get(v_l_633_, 4);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_l_633_, 3);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_l_633_, 2);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_l_633_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_l_633_, 0);
lean_dec(v_unused_697_);
v___x_666_ = v_l_633_;
v_isShared_667_ = v_isSharedCheck_692_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_l_633_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_692_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_682_; 
v___x_668_ = lean_nat_add(v___x_635_, v_size_644_);
v___x_669_ = lean_nat_add(v___x_668_, v_size_630_);
lean_dec(v_size_630_);
if (lean_obj_tag(v_l_659_) == 0)
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_l_659_, 0);
lean_inc(v_size_690_);
v___y_682_ = v_size_690_;
goto v___jp_681_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_682_ = v___x_691_;
goto v___jp_681_;
}
v___jp_670_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_nat_add(v___y_671_, v___y_673_);
lean_dec(v___y_673_);
lean_dec(v___y_671_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 4, v_r_634_);
lean_ctor_set(v___x_666_, 3, v_r_660_);
lean_ctor_set(v___x_666_, 2, v_v_632_);
lean_ctor_set(v___x_666_, 1, v_k_631_);
lean_ctor_set(v___x_666_, 0, v___x_674_);
v___x_676_ = v___x_666_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_r_634_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v___x_676_);
lean_ctor_set(v___x_654_, 3, v___y_672_);
lean_ctor_set(v___x_654_, 2, v_v_658_);
lean_ctor_set(v___x_654_, 1, v_k_657_);
lean_ctor_set(v___x_654_, 0, v___x_669_);
v___x_678_ = v___x_654_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v___y_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_nat_add(v___x_668_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v___x_668_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_l_659_);
lean_ctor_set(v___x_638_, 3, v_tree_641_);
lean_ctor_set(v___x_638_, 2, v_v_643_);
lean_ctor_set(v___x_638_, 1, v_k_642_);
lean_ctor_set(v___x_638_, 0, v___x_683_);
v___x_685_ = v___x_638_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_tree_641_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_l_659_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = lean_nat_add(v___x_635_, v_size_661_);
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_size_687_; 
v_size_687_ = lean_ctor_get(v_r_660_, 0);
lean_inc(v_size_687_);
v___y_671_ = v___x_686_;
v___y_672_ = v___x_685_;
v___y_673_ = v_size_687_;
goto v___jp_670_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___y_671_ = v___x_686_;
v___y_672_ = v___x_685_;
v___y_673_ = v___x_688_;
goto v___jp_670_;
}
}
}
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_698_ = lean_nat_add(v___x_635_, v_size_644_);
v___x_699_ = lean_nat_add(v___x_698_, v_size_630_);
lean_dec(v_size_630_);
v___x_700_ = lean_nat_add(v___x_698_, v_size_656_);
lean_dec(v___x_698_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_l_633_);
lean_ctor_set(v___x_654_, 3, v_tree_641_);
lean_ctor_set(v___x_654_, 2, v_v_643_);
lean_ctor_set(v___x_654_, 1, v_k_642_);
lean_ctor_set(v___x_654_, 0, v___x_700_);
v___x_702_ = v___x_654_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_tree_641_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_l_633_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_r_634_);
lean_ctor_set(v___x_638_, 3, v___x_702_);
lean_ctor_set(v___x_638_, 2, v_v_632_);
lean_ctor_set(v___x_638_, 1, v_k_631_);
lean_ctor_set(v___x_638_, 0, v___x_699_);
v___x_704_ = v___x_638_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_r_634_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_766_; 
lean_inc(v_r_634_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
lean_inc(v_size_630_);
v_isSharedCheck_766_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_767_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_r_453_, 2);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_r_453_, 1);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_771_);
v___x_714_ = v_r_453_;
v_isShared_715_ = v_isSharedCheck_766_;
goto v_resetjp_713_;
}
else
{
lean_dec(v_r_453_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_766_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
if (lean_obj_tag(v_l_633_) == 0)
{
if (lean_obj_tag(v_r_634_) == 0)
{
lean_object* v_k_716_; lean_object* v_v_717_; lean_object* v_size_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_k_716_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_k_716_);
v_v_717_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_v_717_);
lean_dec_ref(v___x_640_);
v_size_718_ = lean_ctor_get(v_l_633_, 0);
v___x_719_ = lean_nat_add(v___x_635_, v_size_630_);
lean_dec(v_size_630_);
v___x_720_ = lean_nat_add(v___x_635_, v_size_718_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 4, v_l_633_);
lean_ctor_set(v___x_714_, 3, v_tree_641_);
lean_ctor_set(v___x_714_, 2, v_v_717_);
lean_ctor_set(v___x_714_, 1, v_k_716_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_722_ = v___x_714_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_716_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_717_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_tree_641_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_l_633_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_r_634_);
lean_ctor_set(v___x_638_, 3, v___x_722_);
lean_ctor_set(v___x_638_, 2, v_v_632_);
lean_ctor_set(v___x_638_, 1, v_k_631_);
lean_ctor_set(v___x_638_, 0, v___x_719_);
v___x_724_ = v___x_638_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_r_634_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_k_727_; lean_object* v_v_728_; lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_size_630_);
v_k_727_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_k_727_);
v_v_728_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_v_728_);
lean_dec_ref(v___x_640_);
v_k_729_ = lean_ctor_get(v_l_633_, 1);
v_v_730_ = lean_ctor_get(v_l_633_, 2);
v_isSharedCheck_744_ = !lean_is_exclusive(v_l_633_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_745_ = lean_ctor_get(v_l_633_, 4);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_l_633_, 3);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_l_633_, 0);
lean_dec(v_unused_747_);
v___x_732_ = v_l_633_;
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_v_730_);
lean_inc(v_k_729_);
lean_dec(v_l_633_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(3u);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 4, v_r_634_);
lean_ctor_set(v___x_732_, 3, v_r_634_);
lean_ctor_set(v___x_732_, 2, v_v_728_);
lean_ctor_set(v___x_732_, 1, v_k_727_);
lean_ctor_set(v___x_732_, 0, v___x_635_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_r_634_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_r_634_);
v___x_736_ = v_reuseFailAlloc_743_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 3, v_r_634_);
lean_ctor_set(v___x_714_, 0, v___x_635_);
v___x_738_ = v___x_714_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_r_634_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_r_634_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v___x_738_);
lean_ctor_set(v___x_638_, 3, v___x_736_);
lean_ctor_set(v___x_638_, 2, v_v_730_);
lean_ctor_set(v___x_638_, 1, v_k_729_);
lean_ctor_set(v___x_638_, 0, v___x_734_);
v___x_740_ = v___x_638_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_634_) == 0)
{
lean_object* v_k_748_; lean_object* v_v_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec(v_size_630_);
v_k_748_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_k_748_);
v_v_749_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_v_749_);
lean_dec_ref(v___x_640_);
v___x_750_ = lean_unsigned_to_nat(3u);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 4, v_l_633_);
lean_ctor_set(v___x_714_, 2, v_v_749_);
lean_ctor_set(v___x_714_, 1, v_k_748_);
lean_ctor_set(v___x_714_, 0, v___x_635_);
v___x_752_ = v___x_714_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_l_633_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_l_633_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_r_634_);
lean_ctor_set(v___x_638_, 3, v___x_752_);
lean_ctor_set(v___x_638_, 2, v_v_632_);
lean_ctor_set(v___x_638_, 1, v_k_631_);
lean_ctor_set(v___x_638_, 0, v___x_750_);
v___x_754_ = v___x_638_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_r_634_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v___x_760_; 
v_k_757_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_k_757_);
v_v_758_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_v_758_);
lean_dec_ref(v___x_640_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 3, v_r_634_);
v___x_760_ = v___x_714_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_size_630_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_r_634_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_r_634_);
v___x_760_ = v_reuseFailAlloc_765_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(2u);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v___x_760_);
lean_ctor_set(v___x_638_, 3, v_r_634_);
lean_ctor_set(v___x_638_, 2, v_v_758_);
lean_ctor_set(v___x_638_, 1, v_k_757_);
lean_ctor_set(v___x_638_, 0, v___x_761_);
v___x_763_ = v___x_638_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_r_634_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v___x_760_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
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
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_930_; 
lean_inc(v_r_634_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
v_isSharedCheck_930_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_931_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_r_453_, 2);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_r_453_, 1);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_935_);
v___x_779_ = v_r_453_;
v_isShared_780_ = v_isSharedCheck_930_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_r_453_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_930_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_tree_782_; 
v___x_781_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_631_, v_v_632_, v_l_633_, v_r_634_);
v_tree_782_ = lean_ctor_get(v___x_781_, 2);
lean_inc(v_tree_782_);
if (lean_obj_tag(v_tree_782_) == 0)
{
lean_object* v_k_783_; lean_object* v_v_784_; lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_k_783_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_k_783_);
v_v_784_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_v_784_);
lean_dec_ref(v___x_781_);
v_size_785_ = lean_ctor_get(v_tree_782_, 0);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_mul(v___x_786_, v_size_785_);
v___x_788_ = lean_nat_dec_lt(v___x_787_, v_size_625_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_r_629_);
v___x_789_ = lean_nat_add(v___x_635_, v_size_625_);
v___x_790_ = lean_nat_add(v___x_789_, v_size_785_);
lean_dec(v___x_789_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_tree_782_);
lean_ctor_set(v___x_779_, 3, v_l_452_);
lean_ctor_set(v___x_779_, 2, v_v_784_);
lean_ctor_set(v___x_779_, 1, v_k_783_);
lean_ctor_set(v___x_779_, 0, v___x_790_);
v___x_792_ = v___x_779_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_tree_782_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_859_; 
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_inc(v_size_625_);
v_isSharedCheck_859_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; lean_object* v_unused_864_; 
v_unused_860_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_864_);
v___x_795_ = v_l_452_;
v_isShared_796_ = v_isSharedCheck_859_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_l_452_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_859_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_size_797_; lean_object* v_size_798_; lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_l_801_; lean_object* v_r_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_size_797_ = lean_ctor_get(v_l_628_, 0);
v_size_798_ = lean_ctor_get(v_r_629_, 0);
v_k_799_ = lean_ctor_get(v_r_629_, 1);
v_v_800_ = lean_ctor_get(v_r_629_, 2);
v_l_801_ = lean_ctor_get(v_r_629_, 3);
v_r_802_ = lean_ctor_get(v_r_629_, 4);
v___x_803_ = lean_unsigned_to_nat(2u);
v___x_804_ = lean_nat_mul(v___x_803_, v_size_797_);
v___x_805_ = lean_nat_dec_lt(v_size_798_, v___x_804_);
lean_dec(v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_843_; 
lean_inc(v_r_802_);
lean_inc(v_l_801_);
lean_inc(v_v_800_);
lean_inc(v_k_799_);
lean_del_object(v___x_795_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_r_629_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; 
v_unused_844_ = lean_ctor_get(v_r_629_, 4);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_r_629_, 3);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_r_629_, 2);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_r_629_, 1);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_r_629_, 0);
lean_dec(v_unused_848_);
v___x_807_ = v_r_629_;
v_isShared_808_ = v_isSharedCheck_843_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_r_629_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_843_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___x_831_; lean_object* v___y_833_; 
v___x_809_ = lean_nat_add(v___x_635_, v_size_625_);
lean_dec(v_size_625_);
v___x_810_ = lean_nat_add(v___x_809_, v_size_785_);
lean_dec(v___x_809_);
v___x_831_ = lean_nat_add(v___x_635_, v_size_797_);
if (lean_obj_tag(v_l_801_) == 0)
{
lean_object* v_size_841_; 
v_size_841_ = lean_ctor_get(v_l_801_, 0);
lean_inc(v_size_841_);
v___y_833_ = v_size_841_;
goto v___jp_832_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___y_833_ = v___x_842_;
goto v___jp_832_;
}
v___jp_811_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_nat_add(v___y_812_, v___y_814_);
lean_dec(v___y_814_);
lean_dec(v___y_812_);
lean_inc_ref(v_tree_782_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_tree_782_);
lean_ctor_set(v___x_807_, 3, v_r_802_);
lean_ctor_set(v___x_807_, 2, v_v_784_);
lean_ctor_set(v___x_807_, 1, v_k_783_);
lean_ctor_set(v___x_807_, 0, v___x_815_);
v___x_817_ = v___x_807_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_r_802_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_tree_782_);
v___x_817_ = v_reuseFailAlloc_830_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v_tree_782_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_825_ = lean_ctor_get(v_tree_782_, 4);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_tree_782_, 3);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_tree_782_, 2);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_tree_782_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_tree_782_, 0);
lean_dec(v_unused_829_);
v___x_819_ = v_tree_782_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_tree_782_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v___x_817_);
lean_ctor_set(v___x_819_, 3, v___y_813_);
lean_ctor_set(v___x_819_, 2, v_v_800_);
lean_ctor_set(v___x_819_, 1, v_k_799_);
lean_ctor_set(v___x_819_, 0, v___x_810_);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v___y_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v___x_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_nat_add(v___x_831_, v___y_833_);
lean_dec(v___y_833_);
lean_dec(v___x_831_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_801_);
lean_ctor_set(v___x_779_, 3, v_l_628_);
lean_ctor_set(v___x_779_, 2, v_v_627_);
lean_ctor_set(v___x_779_, 1, v_k_626_);
lean_ctor_set(v___x_779_, 0, v___x_834_);
v___x_836_ = v___x_779_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_l_801_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_nat_add(v___x_635_, v_size_785_);
if (lean_obj_tag(v_r_802_) == 0)
{
lean_object* v_size_838_; 
v_size_838_ = lean_ctor_get(v_r_802_, 0);
lean_inc(v_size_838_);
v___y_812_ = v___x_837_;
v___y_813_ = v___x_836_;
v___y_814_ = v_size_838_;
goto v___jp_811_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(0u);
v___y_812_ = v___x_837_;
v___y_813_ = v___x_836_;
v___y_814_ = v___x_839_;
goto v___jp_811_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_849_ = lean_nat_add(v___x_635_, v_size_625_);
lean_dec(v_size_625_);
v___x_850_ = lean_nat_add(v___x_849_, v_size_785_);
lean_dec(v___x_849_);
v___x_851_ = lean_nat_add(v___x_635_, v_size_785_);
v___x_852_ = lean_nat_add(v___x_851_, v_size_798_);
lean_dec(v___x_851_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_tree_782_);
lean_ctor_set(v___x_779_, 3, v_r_629_);
lean_ctor_set(v___x_779_, 2, v_v_784_);
lean_ctor_set(v___x_779_, 1, v_k_783_);
lean_ctor_set(v___x_779_, 0, v___x_852_);
v___x_854_ = v___x_779_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_tree_782_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v___x_854_);
lean_ctor_set(v___x_795_, 0, v___x_850_);
v___x_856_ = v___x_795_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_628_) == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_888_; 
lean_inc_ref(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_inc(v_size_625_);
v_isSharedCheck_888_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_889_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_893_);
v___x_866_ = v_l_452_;
v_isShared_867_ = v_isSharedCheck_888_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_l_452_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_888_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v_k_868_; lean_object* v_v_869_; lean_object* v_size_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_k_868_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_k_868_);
v_v_869_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_v_869_);
lean_dec_ref(v___x_781_);
v_size_870_ = lean_ctor_get(v_r_629_, 0);
v___x_871_ = lean_nat_add(v___x_635_, v_size_625_);
lean_dec(v_size_625_);
v___x_872_ = lean_nat_add(v___x_635_, v_size_870_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_tree_782_);
lean_ctor_set(v___x_779_, 3, v_r_629_);
lean_ctor_set(v___x_779_, 2, v_v_869_);
lean_ctor_set(v___x_779_, 1, v_k_868_);
lean_ctor_set(v___x_779_, 0, v___x_872_);
v___x_874_ = v___x_779_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_868_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_tree_782_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_874_);
lean_ctor_set(v___x_866_, 0, v___x_871_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_k_879_; lean_object* v_v_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
lean_dec(v_size_625_);
v_k_879_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_k_879_);
v_v_880_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_v_880_);
lean_dec_ref(v___x_781_);
v___x_881_ = lean_unsigned_to_nat(3u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_r_629_);
lean_ctor_set(v___x_779_, 3, v_r_629_);
lean_ctor_set(v___x_779_, 2, v_v_880_);
lean_ctor_set(v___x_779_, 1, v_k_879_);
lean_ctor_set(v___x_779_, 0, v___x_635_);
v___x_883_ = v___x_779_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_r_629_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_883_);
lean_ctor_set(v___x_866_, 0, v___x_881_);
v___x_885_ = v___x_866_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_918_; 
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
v_isSharedCheck_918_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; lean_object* v_unused_920_; lean_object* v_unused_921_; lean_object* v_unused_922_; lean_object* v_unused_923_; 
v_unused_919_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_920_);
v_unused_921_ = lean_ctor_get(v_l_452_, 2);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_l_452_, 1);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_923_);
v___x_895_ = v_l_452_;
v_isShared_896_ = v_isSharedCheck_918_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_l_452_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_918_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_914_; 
v_k_897_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_k_897_);
v_v_898_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_v_898_);
lean_dec_ref(v___x_781_);
v_k_899_ = lean_ctor_get(v_r_629_, 1);
v_v_900_ = lean_ctor_get(v_r_629_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_r_629_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_915_ = lean_ctor_get(v_r_629_, 4);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_r_629_, 3);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_r_629_, 0);
lean_dec(v_unused_917_);
v___x_902_ = v_r_629_;
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_v_900_);
lean_inc(v_k_899_);
lean_dec(v_r_629_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_unsigned_to_nat(3u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_l_628_);
lean_ctor_set(v___x_902_, 3, v_l_628_);
lean_ctor_set(v___x_902_, 2, v_v_627_);
lean_ctor_set(v___x_902_, 1, v_k_626_);
lean_ctor_set(v___x_902_, 0, v___x_635_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_l_628_);
v___x_906_ = v_reuseFailAlloc_913_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_628_);
lean_ctor_set(v___x_779_, 3, v_l_628_);
lean_ctor_set(v___x_779_, 2, v_v_898_);
lean_ctor_set(v___x_779_, 1, v_k_897_);
lean_ctor_set(v___x_779_, 0, v___x_635_);
v___x_908_ = v___x_779_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_l_628_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v___x_908_);
lean_ctor_set(v___x_895_, 3, v___x_906_);
lean_ctor_set(v___x_895_, 2, v_v_900_);
lean_ctor_set(v___x_895_, 1, v_k_899_);
lean_ctor_set(v___x_895_, 0, v___x_904_);
v___x_910_ = v___x_895_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
else
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_k_924_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_k_924_);
v_v_925_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_v_925_);
lean_dec_ref(v___x_781_);
v___x_926_ = lean_unsigned_to_nat(2u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_r_629_);
lean_ctor_set(v___x_779_, 3, v_l_452_);
lean_ctor_set(v___x_779_, 2, v_v_925_);
lean_ctor_set(v___x_779_, 1, v_k_924_);
lean_ctor_set(v___x_779_, 0, v___x_926_);
v___x_928_ = v___x_779_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_924_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_v_925_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_r_629_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
else
{
return v_l_452_;
}
}
else
{
return v_r_453_;
}
}
}
else
{
lean_object* v_impl_936_; lean_object* v___x_937_; 
v_impl_936_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_448_, v_l_452_);
v___x_937_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_936_) == 0)
{
if (lean_obj_tag(v_r_453_) == 0)
{
lean_object* v_size_938_; lean_object* v_size_939_; lean_object* v_k_940_; lean_object* v_v_941_; lean_object* v_l_942_; lean_object* v_r_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_size_938_ = lean_ctor_get(v_impl_936_, 0);
lean_inc(v_size_938_);
v_size_939_ = lean_ctor_get(v_r_453_, 0);
v_k_940_ = lean_ctor_get(v_r_453_, 1);
v_v_941_ = lean_ctor_get(v_r_453_, 2);
v_l_942_ = lean_ctor_get(v_r_453_, 3);
lean_inc(v_l_942_);
v_r_943_ = lean_ctor_get(v_r_453_, 4);
v___x_944_ = lean_unsigned_to_nat(3u);
v___x_945_ = lean_nat_mul(v___x_944_, v_size_938_);
v___x_946_ = lean_nat_dec_lt(v___x_945_, v_size_939_);
lean_dec(v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_l_942_);
v___x_947_ = lean_nat_add(v___x_937_, v_size_938_);
lean_dec(v_size_938_);
v___x_948_ = lean_nat_add(v___x_947_, v_size_939_);
lean_dec(v___x_947_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 3, v_impl_936_);
lean_ctor_set(v___x_455_, 0, v___x_948_);
v___x_950_ = v___x_455_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_impl_936_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_r_453_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1015_; 
lean_inc(v_r_943_);
lean_inc(v_v_941_);
lean_inc(v_k_940_);
lean_inc(v_size_939_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; lean_object* v_unused_1020_; 
v_unused_1016_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_453_, 2);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_r_453_, 1);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_1020_);
v___x_953_ = v_r_453_;
v_isShared_954_ = v_isSharedCheck_1015_;
goto v_resetjp_952_;
}
else
{
lean_dec(v_r_453_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1015_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_size_955_; lean_object* v_k_956_; lean_object* v_v_957_; lean_object* v_l_958_; lean_object* v_r_959_; lean_object* v_size_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_size_955_ = lean_ctor_get(v_l_942_, 0);
v_k_956_ = lean_ctor_get(v_l_942_, 1);
v_v_957_ = lean_ctor_get(v_l_942_, 2);
v_l_958_ = lean_ctor_get(v_l_942_, 3);
v_r_959_ = lean_ctor_get(v_l_942_, 4);
v_size_960_ = lean_ctor_get(v_r_943_, 0);
v___x_961_ = lean_unsigned_to_nat(2u);
v___x_962_ = lean_nat_mul(v___x_961_, v_size_960_);
v___x_963_ = lean_nat_dec_lt(v_size_955_, v___x_962_);
lean_dec(v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_991_; 
lean_inc(v_r_959_);
lean_inc(v_l_958_);
lean_inc(v_v_957_);
lean_inc(v_k_956_);
v_isSharedCheck_991_ = !lean_is_exclusive(v_l_942_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_992_ = lean_ctor_get(v_l_942_, 4);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_l_942_, 3);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_l_942_, 2);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_l_942_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_l_942_, 0);
lean_dec(v_unused_996_);
v___x_965_ = v_l_942_;
v_isShared_966_ = v_isSharedCheck_991_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_l_942_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_991_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_981_; 
v___x_967_ = lean_nat_add(v___x_937_, v_size_938_);
lean_dec(v_size_938_);
v___x_968_ = lean_nat_add(v___x_967_, v_size_939_);
lean_dec(v_size_939_);
if (lean_obj_tag(v_l_958_) == 0)
{
lean_object* v_size_989_; 
v_size_989_ = lean_ctor_get(v_l_958_, 0);
lean_inc(v_size_989_);
v___y_981_ = v_size_989_;
goto v___jp_980_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___y_981_ = v___x_990_;
goto v___jp_980_;
}
v___jp_969_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_nat_add(v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec(v___y_971_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_r_943_);
lean_ctor_set(v___x_965_, 3, v_r_959_);
lean_ctor_set(v___x_965_, 2, v_v_941_);
lean_ctor_set(v___x_965_, 1, v_k_940_);
lean_ctor_set(v___x_965_, 0, v___x_973_);
v___x_975_ = v___x_965_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_940_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_941_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_r_959_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_r_943_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 4, v___x_975_);
lean_ctor_set(v___x_953_, 3, v___y_970_);
lean_ctor_set(v___x_953_, 2, v_v_957_);
lean_ctor_set(v___x_953_, 1, v_k_956_);
lean_ctor_set(v___x_953_, 0, v___x_968_);
v___x_977_ = v___x_953_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v___y_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_nat_add(v___x_967_, v___y_981_);
lean_dec(v___y_981_);
lean_dec(v___x_967_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_958_);
lean_ctor_set(v___x_455_, 3, v_impl_936_);
lean_ctor_set(v___x_455_, 0, v___x_982_);
v___x_984_ = v___x_455_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v_impl_936_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v_l_958_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = lean_nat_add(v___x_937_, v_size_960_);
if (lean_obj_tag(v_r_959_) == 0)
{
lean_object* v_size_986_; 
v_size_986_ = lean_ctor_get(v_r_959_, 0);
lean_inc(v_size_986_);
v___y_970_ = v___x_984_;
v___y_971_ = v___x_985_;
v___y_972_ = v_size_986_;
goto v___jp_969_;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___y_970_ = v___x_984_;
v___y_971_ = v___x_985_;
v___y_972_ = v___x_987_;
goto v___jp_969_;
}
}
}
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_del_object(v___x_455_);
v___x_997_ = lean_nat_add(v___x_937_, v_size_938_);
lean_dec(v_size_938_);
v___x_998_ = lean_nat_add(v___x_997_, v_size_939_);
lean_dec(v_size_939_);
v___x_999_ = lean_nat_add(v___x_997_, v_size_955_);
lean_dec(v___x_997_);
lean_inc_ref(v_impl_936_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 4, v_l_942_);
lean_ctor_set(v___x_953_, 3, v_impl_936_);
lean_ctor_set(v___x_953_, 2, v_v_451_);
lean_ctor_set(v___x_953_, 1, v_k_450_);
lean_ctor_set(v___x_953_, 0, v___x_999_);
v___x_1001_ = v___x_953_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_impl_936_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v_l_942_);
v___x_1001_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_isSharedCheck_1008_ = !lean_is_exclusive(v_impl_936_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1009_ = lean_ctor_get(v_impl_936_, 4);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_impl_936_, 3);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_impl_936_, 2);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_impl_936_, 1);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_impl_936_, 0);
lean_dec(v_unused_1013_);
v___x_1003_ = v_impl_936_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v_impl_936_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 4, v_r_943_);
lean_ctor_set(v___x_1003_, 3, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v_v_941_);
lean_ctor_set(v___x_1003_, 1, v_k_940_);
lean_ctor_set(v___x_1003_, 0, v___x_998_);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_940_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_941_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_r_943_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_size_1021_ = lean_ctor_get(v_impl_936_, 0);
lean_inc(v_size_1021_);
v___x_1022_ = lean_nat_add(v___x_937_, v_size_1021_);
lean_dec(v_size_1021_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 3, v_impl_936_);
lean_ctor_set(v___x_455_, 0, v___x_1022_);
v___x_1024_ = v___x_455_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_impl_936_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_r_453_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
if (lean_obj_tag(v_r_453_) == 0)
{
lean_object* v_l_1026_; 
v_l_1026_ = lean_ctor_get(v_r_453_, 3);
lean_inc(v_l_1026_);
if (lean_obj_tag(v_l_1026_) == 0)
{
lean_object* v_r_1027_; 
v_r_1027_ = lean_ctor_get(v_r_453_, 4);
lean_inc(v_r_1027_);
if (lean_obj_tag(v_r_1027_) == 0)
{
lean_object* v_size_1028_; lean_object* v_k_1029_; lean_object* v_v_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1043_; 
v_size_1028_ = lean_ctor_get(v_r_453_, 0);
v_k_1029_ = lean_ctor_get(v_r_453_, 1);
v_v_1030_ = lean_ctor_get(v_r_453_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1044_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_1045_);
v___x_1032_ = v_r_453_;
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_v_1030_);
lean_inc(v_k_1029_);
lean_inc(v_size_1028_);
lean_dec(v_r_453_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_size_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v_size_1034_ = lean_ctor_get(v_l_1026_, 0);
v___x_1035_ = lean_nat_add(v___x_937_, v_size_1028_);
lean_dec(v_size_1028_);
v___x_1036_ = lean_nat_add(v___x_937_, v_size_1034_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v_l_1026_);
lean_ctor_set(v___x_1032_, 3, v_impl_936_);
lean_ctor_set(v___x_1032_, 2, v_v_451_);
lean_ctor_set(v___x_1032_, 1, v_k_450_);
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_impl_936_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_l_1026_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_1027_);
lean_ctor_set(v___x_455_, 3, v___x_1038_);
lean_ctor_set(v___x_455_, 2, v_v_1030_);
lean_ctor_set(v___x_455_, 1, v_k_1029_);
lean_ctor_set(v___x_455_, 0, v___x_1035_);
v___x_1040_ = v___x_455_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_r_1027_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_k_1046_; lean_object* v_v_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1070_; 
v_k_1046_ = lean_ctor_get(v_r_453_, 1);
v_v_1047_ = lean_ctor_get(v_r_453_, 2);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1071_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_1073_);
v___x_1049_ = v_r_453_;
v_isShared_1050_ = v_isSharedCheck_1070_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_v_1047_);
lean_inc(v_k_1046_);
lean_dec(v_r_453_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1070_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_k_1051_; lean_object* v_v_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1066_; 
v_k_1051_ = lean_ctor_get(v_l_1026_, 1);
v_v_1052_ = lean_ctor_get(v_l_1026_, 2);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_l_1026_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1067_ = lean_ctor_get(v_l_1026_, 4);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_l_1026_, 3);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_l_1026_, 0);
lean_dec(v_unused_1069_);
v___x_1054_ = v_l_1026_;
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_v_1052_);
lean_inc(v_k_1051_);
lean_dec(v_l_1026_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_unsigned_to_nat(3u);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_r_1027_);
lean_ctor_set(v___x_1054_, 3, v_r_1027_);
lean_ctor_set(v___x_1054_, 2, v_v_451_);
lean_ctor_set(v___x_1054_, 1, v_k_450_);
lean_ctor_set(v___x_1054_, 0, v___x_937_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_r_1027_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_r_1027_);
v___x_1058_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 3, v_r_1027_);
lean_ctor_set(v___x_1049_, 0, v___x_937_);
v___x_1060_ = v___x_1049_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_r_1027_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_r_1027_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_1060_);
lean_ctor_set(v___x_455_, 3, v___x_1058_);
lean_ctor_set(v___x_455_, 2, v_v_1052_);
lean_ctor_set(v___x_455_, 1, v_k_1051_);
lean_ctor_set(v___x_455_, 0, v___x_1056_);
v___x_1062_ = v___x_455_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_k_1051_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_v_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1074_; 
v_r_1074_ = lean_ctor_get(v_r_453_, 4);
lean_inc(v_r_1074_);
if (lean_obj_tag(v_r_1074_) == 0)
{
lean_object* v_k_1075_; lean_object* v_v_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1087_; 
v_k_1075_ = lean_ctor_get(v_r_453_, 1);
v_v_1076_ = lean_ctor_get(v_r_453_, 2);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1088_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_r_453_, 0);
lean_dec(v_unused_1090_);
v___x_1078_ = v_r_453_;
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_v_1076_);
lean_inc(v_k_1075_);
lean_dec(v_r_453_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(3u);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_1026_);
lean_ctor_set(v___x_1078_, 2, v_v_451_);
lean_ctor_set(v___x_1078_, 1, v_k_450_);
lean_ctor_set(v___x_1078_, 0, v___x_937_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_l_1026_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_l_1026_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_r_1074_);
lean_ctor_set(v___x_455_, 3, v___x_1082_);
lean_ctor_set(v___x_455_, 2, v_v_1076_);
lean_ctor_set(v___x_455_, 1, v_k_1075_);
lean_ctor_set(v___x_455_, 0, v___x_1080_);
v___x_1084_ = v___x_455_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_1075_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_r_1074_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_size_1091_; lean_object* v_k_1092_; lean_object* v_v_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1104_; 
v_size_1091_ = lean_ctor_get(v_r_453_, 0);
v_k_1092_ = lean_ctor_get(v_r_453_, 1);
v_v_1093_ = lean_ctor_get(v_r_453_, 2);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_r_453_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; lean_object* v_unused_1106_; 
v_unused_1105_ = lean_ctor_get(v_r_453_, 4);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_r_453_, 3);
lean_dec(v_unused_1106_);
v___x_1095_ = v_r_453_;
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_v_1093_);
lean_inc(v_k_1092_);
lean_inc(v_size_1091_);
lean_dec(v_r_453_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 3, v_r_1074_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_size_1091_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_k_1092_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_v_1093_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_r_1074_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_r_1074_);
v___x_1098_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_unsigned_to_nat(2u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_1098_);
lean_ctor_set(v___x_455_, 3, v_r_1074_);
lean_ctor_set(v___x_455_, 0, v___x_1099_);
v___x_1101_ = v___x_455_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_r_1074_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v___x_1098_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
else
{
lean_object* v___x_1108_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 3, v_r_453_);
lean_ctor_set(v___x_455_, 0, v___x_937_);
v___x_1108_ = v___x_455_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_r_453_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_r_453_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
else
{
return v_t_449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object* v_k_1112_, lean_object* v_t_1113_){
_start:
{
uint64_t v_k_boxed_1114_; lean_object* v_res_1115_; 
v_k_boxed_1114_ = lean_unbox_uint64(v_k_1112_);
lean_dec_ref(v_k_1112_);
v_res_1115_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_1114_, v_t_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object* v_t_1116_, uint64_t v_k_1117_){
_start:
{
if (lean_obj_tag(v_t_1116_) == 0)
{
lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v_l_1120_; lean_object* v_r_1121_; uint64_t v___x_1122_; uint8_t v___x_1123_; 
v_k_1118_ = lean_ctor_get(v_t_1116_, 1);
v_v_1119_ = lean_ctor_get(v_t_1116_, 2);
v_l_1120_ = lean_ctor_get(v_t_1116_, 3);
v_r_1121_ = lean_ctor_get(v_t_1116_, 4);
v___x_1122_ = lean_unbox_uint64(v_k_1118_);
v___x_1123_ = lean_uint64_dec_lt(v_k_1117_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint64_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_unbox_uint64(v_k_1118_);
v___x_1125_ = lean_uint64_dec_eq(v_k_1117_, v___x_1124_);
if (v___x_1125_ == 0)
{
v_t_1116_ = v_r_1121_;
goto _start;
}
else
{
lean_object* v___x_1127_; 
lean_inc(v_v_1119_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_v_1119_);
return v___x_1127_;
}
}
else
{
v_t_1116_ = v_l_1120_;
goto _start;
}
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_box(0);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object* v_t_1130_, lean_object* v_k_1131_){
_start:
{
uint64_t v_k_boxed_1132_; lean_object* v_res_1133_; 
v_k_boxed_1132_ = lean_unbox_uint64(v_k_1131_);
lean_dec_ref(v_k_1131_);
v_res_1133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1130_, v_k_boxed_1132_);
lean_dec(v_t_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object* v_state_1134_, uint64_t v_id_1135_, lean_object* v_reason_1136_){
_start:
{
lean_object* v_tokens_1138_; lean_object* v___x_1139_; 
v_tokens_1138_ = lean_ctor_get(v_state_1134_, 0);
v___x_1139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1138_, v_id_1135_);
if (lean_obj_tag(v___x_1139_) == 1)
{
lean_object* v_val_1140_; lean_object* v_fst_1141_; lean_object* v_snd_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_tokens_1147_; uint64_t v_id_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_val_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_val_1140_);
lean_dec_ref(v___x_1139_);
v_fst_1141_ = lean_ctor_get(v_val_1140_, 0);
lean_inc(v_fst_1141_);
v_snd_1142_ = lean_ctor_get(v_val_1140_, 1);
lean_inc(v_snd_1142_);
lean_dec(v_val_1140_);
v_sz_1143_ = lean_array_size(v_snd_1142_);
v___x_1144_ = ((size_t)0ULL);
lean_inc(v_reason_1136_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1136_, v_snd_1142_, v_sz_1143_, v___x_1144_, v_state_1134_);
lean_dec(v_snd_1142_);
v___x_1146_ = l_Std_CancellationToken_cancel(v_fst_1141_, v_reason_1136_);
v_tokens_1147_ = lean_ctor_get(v___x_1145_, 0);
v_id_1148_ = lean_ctor_get_uint64(v___x_1145_, sizeof(void*)*1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___x_1145_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_tokens_1147_);
lean_dec(v___x_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_1135_, v_tokens_1147_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
lean_ctor_set_uint64(v_reuseFailAlloc_1155_, sizeof(void*)*1, v_id_1148_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_dec(v___x_1139_);
lean_dec(v_reason_1136_);
return v_state_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object* v_reason_1157_, lean_object* v_as_1158_, size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_b_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1163_ == 0)
{
lean_dec(v_reason_1157_);
return v_b_1161_;
}
else
{
lean_object* v_a_1164_; uint64_t v___x_1165_; lean_object* v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; 
v_a_1164_ = lean_array_uget_borrowed(v_as_1158_, v_i_1160_);
v___x_1165_ = lean_unbox_uint64(v_a_1164_);
lean_inc(v_reason_1157_);
v___x_1166_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_b_1161_, v___x_1165_, v_reason_1157_);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1160_, v___x_1167_);
v_i_1160_ = v___x_1168_;
v_b_1161_ = v___x_1166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object* v_reason_1170_, lean_object* v_as_1171_, lean_object* v_sz_1172_, lean_object* v_i_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_sz_boxed_1176_; size_t v_i_boxed_1177_; lean_object* v_res_1178_; 
v_sz_boxed_1176_ = lean_unbox_usize(v_sz_1172_);
lean_dec(v_sz_1172_);
v_i_boxed_1177_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_1170_, v_as_1171_, v_sz_boxed_1176_, v_i_boxed_1177_, v_b_1174_);
lean_dec_ref(v_as_1171_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object* v_state_1179_, lean_object* v_id_1180_, lean_object* v_reason_1181_, lean_object* v_a_1182_){
_start:
{
uint64_t v_id_boxed_1183_; lean_object* v_res_1184_; 
v_id_boxed_1183_ = lean_unbox_uint64(v_id_1180_);
lean_dec_ref(v_id_1180_);
v_res_1184_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_state_1179_, v_id_boxed_1183_, v_reason_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object* v_00_u03b4_1185_, lean_object* v_t_1186_, uint64_t v_k_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_1186_, v_k_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object* v_00_u03b4_1189_, lean_object* v_t_1190_, lean_object* v_k_1191_){
_start:
{
uint64_t v_k_boxed_1192_; lean_object* v_res_1193_; 
v_k_boxed_1192_ = lean_unbox_uint64(v_k_1191_);
lean_dec_ref(v_k_1191_);
v_res_1193_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_1189_, v_t_1190_, v_k_boxed_1192_);
lean_dec(v_t_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object* v_00_u03b2_1194_, uint64_t v_k_1195_, lean_object* v_t_1196_, lean_object* v_h_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1195_, v_t_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_k_1200_, lean_object* v_t_1201_, lean_object* v_h_1202_){
_start:
{
uint64_t v_k_boxed_1203_; lean_object* v_res_1204_; 
v_k_boxed_1203_ = lean_unbox_uint64(v_k_1200_);
lean_dec_ref(v_k_1200_);
v_res_1204_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_1199_, v_k_boxed_1203_, v_t_1201_, v_h_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t v_id_1205_, lean_object* v_reason_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_st_ref_get(v___y_1207_);
v___x_1210_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v___x_1209_, v_id_1205_, v_reason_1206_);
v___x_1211_ = lean_st_ref_set(v___y_1207_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object* v_id_1212_, lean_object* v_reason_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint64_t v_id_boxed_1216_; lean_object* v_res_1217_; 
v_id_boxed_1216_ = lean_unbox_uint64(v_id_1212_);
lean_dec_ref(v_id_1212_);
v_res_1217_ = l_Std_CancellationContext_cancel___lam__0(v_id_boxed_1216_, v_reason_1213_, v___y_1214_);
lean_dec(v___y_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object* v_x_1218_, lean_object* v_reason_1219_){
_start:
{
lean_object* v_state_1221_; lean_object* v_token_1222_; uint64_t v_id_1223_; uint8_t v___x_1224_; 
v_state_1221_ = lean_ctor_get(v_x_1218_, 0);
lean_inc_ref(v_state_1221_);
v_token_1222_ = lean_ctor_get(v_x_1218_, 1);
lean_inc_ref(v_token_1222_);
v_id_1223_ = lean_ctor_get_uint64(v_x_1218_, sizeof(void*)*2);
lean_dec_ref(v_x_1218_);
v___x_1224_ = l_Std_CancellationToken_isCancelled(v_token_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box_uint64(v_id_1223_);
v___f_1226_ = lean_alloc_closure((void*)(l_Std_CancellationContext_cancel___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1226_, 0, v___x_1225_);
lean_closure_set(v___f_1226_, 1, v_reason_1219_);
v___x_1227_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1221_, v___f_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec_ref(v_state_1221_);
lean_dec(v_reason_1219_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object* v_x_1229_, lean_object* v_reason_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_CancellationContext_cancel(v_x_1229_, v_reason_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object* v_x_1233_){
_start:
{
lean_object* v_token_1235_; uint8_t v___x_1236_; 
v_token_1235_ = lean_ctor_get(v_x_1233_, 1);
lean_inc_ref(v_token_1235_);
lean_dec_ref(v_x_1233_);
v___x_1236_ = l_Std_CancellationToken_isCancelled(v_token_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object* v_x_1237_, lean_object* v_a_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Std_CancellationContext_isCancelled(v_x_1237_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object* v_x_1241_){
_start:
{
lean_object* v_token_1243_; lean_object* v___x_1244_; 
v_token_1243_ = lean_ctor_get(v_x_1241_, 1);
lean_inc_ref(v_token_1243_);
lean_dec_ref(v_x_1241_);
v___x_1244_ = l_Std_CancellationToken_getCancellationReason(v_token_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object* v_x_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_CancellationContext_getCancellationReason(v_x_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object* v_x_1248_){
_start:
{
lean_object* v_token_1250_; lean_object* v___x_1251_; 
v_token_1250_ = lean_ctor_get(v_x_1248_, 1);
lean_inc_ref(v_token_1250_);
lean_dec_ref(v_x_1248_);
v___x_1251_ = l_Std_CancellationToken_wait(v_token_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object* v_x_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_CancellationContext_done(v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object* v_x_1255_){
_start:
{
lean_object* v_token_1256_; lean_object* v___x_1257_; 
v_token_1256_ = lean_ctor_get(v_x_1255_, 1);
lean_inc_ref(v_token_1256_);
lean_dec_ref(v_x_1255_);
v___x_1257_ = l_Std_CancellationToken_selector(v_token_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object* v_state_1258_, uint64_t v_id_1259_){
_start:
{
lean_object* v_tokens_1260_; lean_object* v___x_1261_; 
v_tokens_1260_ = lean_ctor_get(v_state_1258_, 0);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_1260_, v_id_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_unsigned_to_nat(0u);
return v___x_1262_;
}
else
{
lean_object* v_val_1263_; lean_object* v_snd_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_val_1263_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1263_);
lean_dec_ref(v___x_1261_);
v_snd_1264_ = lean_ctor_get(v_val_1263_, 1);
lean_inc(v_snd_1264_);
lean_dec(v_val_1263_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_array_get_size(v_snd_1264_);
v___x_1267_ = lean_nat_dec_lt(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v_snd_1264_);
v___x_1268_ = lean_unsigned_to_nat(1u);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_dec_le(v___x_1266_, v___x_1266_);
if (v___x_1270_ == 0)
{
if (v___x_1267_ == 0)
{
lean_dec(v_snd_1264_);
return v___x_1269_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1266_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1258_, v_snd_1264_, v___x_1271_, v___x_1272_, v___x_1265_);
lean_dec(v_snd_1264_);
v___x_1274_ = lean_nat_add(v___x_1269_, v___x_1273_);
lean_dec(v___x_1273_);
return v___x_1274_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1266_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1258_, v_snd_1264_, v___x_1275_, v___x_1276_, v___x_1265_);
lean_dec(v_snd_1264_);
v___x_1278_ = lean_nat_add(v___x_1269_, v___x_1277_);
lean_dec(v___x_1277_);
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object* v_state_1279_, lean_object* v_as_1280_, size_t v_i_1281_, size_t v_stop_1282_, lean_object* v_b_1283_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_eq(v_i_1281_, v_stop_1282_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint64_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; 
v___x_1285_ = lean_array_uget_borrowed(v_as_1280_, v_i_1281_);
v___x_1286_ = lean_unbox_uint64(v___x_1285_);
v___x_1287_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1279_, v___x_1286_);
v___x_1288_ = lean_nat_add(v_b_1283_, v___x_1287_);
lean_dec(v___x_1287_);
lean_dec(v_b_1283_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1281_, v___x_1289_);
v_i_1281_ = v___x_1290_;
v_b_1283_ = v___x_1288_;
goto _start;
}
else
{
return v_b_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object* v_state_1292_, lean_object* v_as_1293_, lean_object* v_i_1294_, lean_object* v_stop_1295_, lean_object* v_b_1296_){
_start:
{
size_t v_i_boxed_1297_; size_t v_stop_boxed_1298_; lean_object* v_res_1299_; 
v_i_boxed_1297_ = lean_unbox_usize(v_i_1294_);
lean_dec(v_i_1294_);
v_stop_boxed_1298_ = lean_unbox_usize(v_stop_1295_);
lean_dec(v_stop_1295_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_1292_, v_as_1293_, v_i_boxed_1297_, v_stop_boxed_1298_, v_b_1296_);
lean_dec_ref(v_as_1293_);
lean_dec_ref(v_state_1292_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object* v_state_1300_, lean_object* v_id_1301_){
_start:
{
uint64_t v_id_boxed_1302_; lean_object* v_res_1303_; 
v_id_boxed_1302_ = lean_unbox_uint64(v_id_1301_);
lean_dec_ref(v_id_1301_);
v_res_1303_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_1300_, v_id_boxed_1302_);
lean_dec_ref(v_state_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t v_id_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_st_ref_get(v___y_1305_);
v___x_1308_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v___x_1307_, v_id_1304_);
lean_dec(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object* v_id_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint64_t v_id_boxed_1312_; lean_object* v_res_1313_; 
v_id_boxed_1312_ = lean_unbox_uint64(v_id_1309_);
lean_dec_ref(v_id_1309_);
v_res_1313_ = l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_1312_, v___y_1310_);
lean_dec(v___y_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object* v_x_1314_){
_start:
{
lean_object* v_state_1316_; uint64_t v_id_1317_; lean_object* v___x_1318_; lean_object* v___f_1319_; lean_object* v___x_1320_; 
v_state_1316_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_state_1316_);
v_id_1317_ = lean_ctor_get_uint64(v_x_1314_, sizeof(void*)*2);
lean_dec_ref(v_x_1314_);
v___x_1318_ = lean_box_uint64(v_id_1317_);
v___f_1319_ = lean_alloc_closure((void*)(l_Std_CancellationContext_countAliveTokens___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1319_, 0, v___x_1318_);
v___x_1320_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(v_state_1316_, v___f_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object* v_x_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_CancellationContext_countAliveTokens(v_x_1321_);
return v_res_1323_;
}
}
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
