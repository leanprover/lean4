// Lean compiler output
// Module: Std.Sync.CancellationContext
// Imports: public import Std.Data public import Init.System.Promise public import Init.Data.Queue public import Std.Sync.Mutex public import Std.Sync.CancellationToken public import Std.Internal.Async.Select
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
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
static lean_object* l_Std_CancellationContext_new___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t, lean_object*);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_new();
LEAN_EXPORT lean_object* l_Std_CancellationContext_new();
lean_object* lean_io_basemutex_unlock(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object*, lean_object*, uint64_t);
lean_object* l_Std_CancellationToken_selector(lean_object*);
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_unbox_uint64(x_5);
x_11 = lean_uint64_dec_lt(x_1, x_10);
if (x_11 == 0)
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_unbox_uint64(x_5);
x_13 = lean_uint64_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_1, x_2, x_8);
x_15 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 4);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_mul(x_22, x_16);
x_24 = lean_nat_dec_lt(x_23, x_17);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_25 = lean_nat_add(x_15, x_16);
x_26 = lean_nat_add(x_25, x_17);
lean_dec(x_17);
lean_dec(x_25);
if (lean_is_scalar(x_9)) {
 x_27 = lean_alloc_ctor(0, 5, 0);
} else {
 x_27 = x_9;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_6);
lean_ctor_set(x_27, 3, x_7);
lean_ctor_set(x_27, 4, x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
x_31 = lean_ctor_get(x_20, 2);
x_32 = lean_ctor_get(x_20, 3);
x_33 = lean_ctor_get(x_20, 4);
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_mul(x_35, x_34);
x_37 = lean_nat_dec_lt(x_29, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_48; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
x_39 = lean_nat_add(x_15, x_16);
x_40 = lean_nat_add(x_39, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_32, 0);
lean_inc(x_55);
x_48 = x_55;
goto block_54;
}
else
{
lean_object* x_56; 
x_56 = lean_unsigned_to_nat(0u);
x_48 = x_56;
goto block_54;
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_18);
lean_ctor_set(x_45, 2, x_19);
lean_ctor_set(x_45, 3, x_33);
lean_ctor_set(x_45, 4, x_21);
if (lean_is_scalar(x_28)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_28;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_45);
return x_46;
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_nat_add(x_39, x_48);
lean_dec(x_48);
lean_dec(x_39);
if (lean_is_scalar(x_9)) {
 x_50 = lean_alloc_ctor(0, 5, 0);
} else {
 x_50 = x_9;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 2, x_6);
lean_ctor_set(x_50, 3, x_7);
lean_ctor_set(x_50, 4, x_32);
x_51 = lean_nat_add(x_15, x_34);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
x_41 = x_50;
x_42 = x_51;
x_43 = x_52;
goto block_47;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_41 = x_50;
x_42 = x_51;
x_43 = x_53;
goto block_47;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
x_57 = lean_nat_add(x_15, x_16);
x_58 = lean_nat_add(x_57, x_17);
lean_dec(x_17);
x_59 = lean_nat_add(x_57, x_29);
lean_dec(x_57);
lean_inc_ref(x_7);
if (lean_is_scalar(x_28)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_28;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
lean_ctor_set(x_60, 2, x_6);
lean_ctor_set(x_60, 3, x_7);
lean_ctor_set(x_60, 4, x_20);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_7, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_7, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_7, 0);
lean_dec(x_66);
lean_ctor_set(x_7, 4, x_21);
lean_ctor_set(x_7, 3, x_60);
lean_ctor_set(x_7, 2, x_19);
lean_ctor_set(x_7, 1, x_18);
lean_ctor_set(x_7, 0, x_58);
return x_7;
}
else
{
lean_object* x_67; 
lean_dec(x_7);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_18);
lean_ctor_set(x_67, 2, x_19);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_21);
return x_67;
}
}
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_14, 3);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_14);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_14, 4);
x_71 = lean_ctor_get(x_14, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_14, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_68, 1);
x_75 = lean_ctor_get(x_68, 2);
x_76 = lean_ctor_get(x_68, 4);
lean_dec(x_76);
x_77 = lean_ctor_get(x_68, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_68, 0);
lean_dec(x_78);
x_79 = lean_unsigned_to_nat(3u);
lean_inc_n(x_70, 2);
lean_ctor_set(x_68, 4, x_70);
lean_ctor_set(x_68, 3, x_70);
lean_ctor_set(x_68, 2, x_6);
lean_ctor_set(x_68, 1, x_5);
lean_ctor_set(x_68, 0, x_15);
lean_inc(x_70);
lean_ctor_set(x_14, 3, x_70);
lean_ctor_set(x_14, 0, x_15);
if (lean_is_scalar(x_9)) {
 x_80 = lean_alloc_ctor(0, 5, 0);
} else {
 x_80 = x_9;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_68);
lean_ctor_set(x_80, 4, x_14);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_68, 1);
x_82 = lean_ctor_get(x_68, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_83 = lean_unsigned_to_nat(3u);
lean_inc_n(x_70, 2);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_15);
lean_ctor_set(x_84, 1, x_5);
lean_ctor_set(x_84, 2, x_6);
lean_ctor_set(x_84, 3, x_70);
lean_ctor_set(x_84, 4, x_70);
lean_inc(x_70);
lean_ctor_set(x_14, 3, x_70);
lean_ctor_set(x_14, 0, x_15);
if (lean_is_scalar(x_9)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_9;
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_14);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_14, 4);
x_87 = lean_ctor_get(x_14, 1);
x_88 = lean_ctor_get(x_14, 2);
lean_inc(x_86);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_14);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_68, 2);
lean_inc(x_90);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_91 = x_68;
} else {
 lean_dec_ref(x_68);
 x_91 = lean_box(0);
}
x_92 = lean_unsigned_to_nat(3u);
lean_inc_n(x_86, 2);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_15);
lean_ctor_set(x_93, 1, x_5);
lean_ctor_set(x_93, 2, x_6);
lean_ctor_set(x_93, 3, x_86);
lean_ctor_set(x_93, 4, x_86);
lean_inc(x_86);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_15);
lean_ctor_set(x_94, 1, x_87);
lean_ctor_set(x_94, 2, x_88);
lean_ctor_set(x_94, 3, x_86);
lean_ctor_set(x_94, 4, x_86);
if (lean_is_scalar(x_9)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_9;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_93);
lean_ctor_set(x_95, 4, x_94);
return x_95;
}
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_14, 4);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_14);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_14, 1);
x_99 = lean_ctor_get(x_14, 2);
x_100 = lean_ctor_get(x_14, 4);
lean_dec(x_100);
x_101 = lean_ctor_get(x_14, 3);
lean_dec(x_101);
x_102 = lean_ctor_get(x_14, 0);
lean_dec(x_102);
x_103 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_14, 4, x_68);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_15);
if (lean_is_scalar(x_9)) {
 x_104 = lean_alloc_ctor(0, 5, 0);
} else {
 x_104 = x_9;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_14);
lean_ctor_set(x_104, 4, x_96);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_14, 1);
x_106 = lean_ctor_get(x_14, 2);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_14);
x_107 = lean_unsigned_to_nat(3u);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_15);
lean_ctor_set(x_108, 1, x_5);
lean_ctor_set(x_108, 2, x_6);
lean_ctor_set(x_108, 3, x_68);
lean_ctor_set(x_108, 4, x_68);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_109, 4, x_96);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_9;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 3, x_96);
lean_ctor_set(x_111, 4, x_14);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
x_112 = lean_box_uint64(x_1);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_7);
lean_ctor_set(x_113, 4, x_8);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_1, x_2, x_7);
x_115 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_8, 0);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 4);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_mul(x_122, x_116);
x_124 = lean_nat_dec_lt(x_123, x_117);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_125 = lean_nat_add(x_115, x_117);
lean_dec(x_117);
x_126 = lean_nat_add(x_125, x_116);
lean_dec(x_125);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
lean_ctor_set(x_127, 2, x_6);
lean_ctor_set(x_127, 3, x_114);
lean_ctor_set(x_127, 4, x_8);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_121, 0);
x_131 = lean_ctor_get(x_121, 1);
x_132 = lean_ctor_get(x_121, 2);
x_133 = lean_ctor_get(x_121, 3);
x_134 = lean_ctor_get(x_121, 4);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_mul(x_135, x_129);
x_137 = lean_nat_dec_lt(x_130, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_148; lean_object* x_149; 
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 x_138 = x_121;
} else {
 lean_dec_ref(x_121);
 x_138 = lean_box(0);
}
x_139 = lean_nat_add(x_115, x_117);
lean_dec(x_117);
x_140 = lean_nat_add(x_139, x_116);
lean_dec(x_139);
x_148 = lean_nat_add(x_115, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_133, 0);
lean_inc(x_156);
x_149 = x_156;
goto block_155;
}
else
{
lean_object* x_157; 
x_157 = lean_unsigned_to_nat(0u);
x_149 = x_157;
goto block_155;
}
block_147:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_143);
lean_dec(x_141);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_5);
lean_ctor_set(x_145, 2, x_6);
lean_ctor_set(x_145, 3, x_134);
lean_ctor_set(x_145, 4, x_8);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_131);
lean_ctor_set(x_146, 2, x_132);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_145);
return x_146;
}
block_155:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_nat_add(x_148, x_149);
lean_dec(x_149);
lean_dec(x_148);
if (lean_is_scalar(x_9)) {
 x_151 = lean_alloc_ctor(0, 5, 0);
} else {
 x_151 = x_9;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_118);
lean_ctor_set(x_151, 2, x_119);
lean_ctor_set(x_151, 3, x_120);
lean_ctor_set(x_151, 4, x_133);
x_152 = lean_nat_add(x_115, x_116);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
x_141 = x_152;
x_142 = x_151;
x_143 = x_153;
goto block_147;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_141 = x_152;
x_142 = x_151;
x_143 = x_154;
goto block_147;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_9);
x_158 = lean_nat_add(x_115, x_117);
lean_dec(x_117);
x_159 = lean_nat_add(x_158, x_116);
lean_dec(x_158);
x_160 = lean_nat_add(x_115, x_116);
x_161 = lean_nat_add(x_160, x_130);
lean_dec(x_160);
lean_inc_ref(x_8);
if (lean_is_scalar(x_128)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_128;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_5);
lean_ctor_set(x_162, 2, x_6);
lean_ctor_set(x_162, 3, x_121);
lean_ctor_set(x_162, 4, x_8);
x_163 = !lean_is_exclusive(x_8);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_8, 4);
lean_dec(x_164);
x_165 = lean_ctor_get(x_8, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_8, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_8, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_8, 0);
lean_dec(x_168);
lean_ctor_set(x_8, 4, x_162);
lean_ctor_set(x_8, 3, x_120);
lean_ctor_set(x_8, 2, x_119);
lean_ctor_set(x_8, 1, x_118);
lean_ctor_set(x_8, 0, x_159);
return x_8;
}
else
{
lean_object* x_169; 
lean_dec(x_8);
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_159);
lean_ctor_set(x_169, 1, x_118);
lean_ctor_set(x_169, 2, x_119);
lean_ctor_set(x_169, 3, x_120);
lean_ctor_set(x_169, 4, x_162);
return x_169;
}
}
}
}
else
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_114, 3);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_114);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_114, 4);
x_173 = lean_ctor_get(x_114, 1);
x_174 = lean_ctor_get(x_114, 2);
x_175 = lean_ctor_get(x_114, 3);
lean_dec(x_175);
x_176 = lean_ctor_get(x_114, 0);
lean_dec(x_176);
x_177 = lean_unsigned_to_nat(3u);
lean_inc(x_172);
lean_ctor_set(x_114, 3, x_172);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_9;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_173);
lean_ctor_set(x_178, 2, x_174);
lean_ctor_set(x_178, 3, x_170);
lean_ctor_set(x_178, 4, x_114);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_114, 4);
x_180 = lean_ctor_get(x_114, 1);
x_181 = lean_ctor_get(x_114, 2);
lean_inc(x_179);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_114);
x_182 = lean_unsigned_to_nat(3u);
lean_inc(x_179);
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_115);
lean_ctor_set(x_183, 1, x_5);
lean_ctor_set(x_183, 2, x_6);
lean_ctor_set(x_183, 3, x_179);
lean_ctor_set(x_183, 4, x_179);
if (lean_is_scalar(x_9)) {
 x_184 = lean_alloc_ctor(0, 5, 0);
} else {
 x_184 = x_9;
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_181);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_183);
return x_184;
}
}
else
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_114, 4);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_114);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_187 = lean_ctor_get(x_114, 1);
x_188 = lean_ctor_get(x_114, 2);
x_189 = lean_ctor_get(x_114, 4);
lean_dec(x_189);
x_190 = lean_ctor_get(x_114, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_114, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_185);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_185, 1);
x_194 = lean_ctor_get(x_185, 2);
x_195 = lean_ctor_get(x_185, 4);
lean_dec(x_195);
x_196 = lean_ctor_get(x_185, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_185, 0);
lean_dec(x_197);
x_198 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_185, 4, x_170);
lean_ctor_set(x_185, 3, x_170);
lean_ctor_set(x_185, 2, x_188);
lean_ctor_set(x_185, 1, x_187);
lean_ctor_set(x_185, 0, x_115);
lean_ctor_set(x_114, 4, x_170);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_199 = lean_alloc_ctor(0, 5, 0);
} else {
 x_199 = x_9;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_193);
lean_ctor_set(x_199, 2, x_194);
lean_ctor_set(x_199, 3, x_185);
lean_ctor_set(x_199, 4, x_114);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_185, 1);
x_201 = lean_ctor_get(x_185, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_185);
x_202 = lean_unsigned_to_nat(3u);
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_115);
lean_ctor_set(x_203, 1, x_187);
lean_ctor_set(x_203, 2, x_188);
lean_ctor_set(x_203, 3, x_170);
lean_ctor_set(x_203, 4, x_170);
lean_ctor_set(x_114, 4, x_170);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_9;
}
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_200);
lean_ctor_set(x_204, 2, x_201);
lean_ctor_set(x_204, 3, x_203);
lean_ctor_set(x_204, 4, x_114);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_205 = lean_ctor_get(x_114, 1);
x_206 = lean_ctor_get(x_114, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_ctor_get(x_185, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_185, 2);
lean_inc(x_208);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 x_209 = x_185;
} else {
 lean_dec_ref(x_185);
 x_209 = lean_box(0);
}
x_210 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_115);
lean_ctor_set(x_211, 1, x_205);
lean_ctor_set(x_211, 2, x_206);
lean_ctor_set(x_211, 3, x_170);
lean_ctor_set(x_211, 4, x_170);
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_115);
lean_ctor_set(x_212, 1, x_5);
lean_ctor_set(x_212, 2, x_6);
lean_ctor_set(x_212, 3, x_170);
lean_ctor_set(x_212, 4, x_170);
if (lean_is_scalar(x_9)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_9;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_207);
lean_ctor_set(x_213, 2, x_208);
lean_ctor_set(x_213, 3, x_211);
lean_ctor_set(x_213, 4, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_9;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_5);
lean_ctor_set(x_215, 2, x_6);
lean_ctor_set(x_215, 3, x_114);
lean_ctor_set(x_215, 4, x_185);
return x_215;
}
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_box_uint64(x_1);
x_218 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_2);
lean_ctor_set(x_218, 3, x_3);
lean_ctor_set(x_218, 4, x_3);
return x_218;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Std_CancellationContext_new___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new() {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Std_CancellationToken_new();
x_3 = lean_box(1);
x_4 = 0;
x_5 = l_Std_CancellationContext_new___closed__0;
lean_inc_ref(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_4, x_6, x_3);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
x_10 = l_Std_Mutex_new___redArg(x_9);
x_11 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set_uint64(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_CancellationContext_new();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_io_basemutex_lock(x_5);
x_7 = lean_apply_2(x_2, x_4, lean_box(0));
x_8 = lean_io_basemutex_unlock(x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box_uint64(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_unbox_uint64(x_5);
x_10 = lean_uint64_dec_lt(x_2, x_9);
if (x_10 == 0)
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_5);
x_12 = lean_uint64_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_8);
lean_ctor_set(x_3, 4, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
x_15 = lean_box_uint64(x_1);
x_16 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Prod_map___redArg(x_14, x_16, x_6);
x_18 = lean_box_uint64(x_2);
lean_ctor_set(x_3, 2, x_17);
lean_ctor_set(x_3, 1, x_18);
return x_3;
}
}
else
{
lean_object* x_19; 
x_19 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_7);
lean_ctor_set(x_3, 3, x_19);
return x_3;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 3);
x_24 = lean_ctor_get(x_3, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_25 = lean_unbox_uint64(x_21);
x_26 = lean_uint64_dec_lt(x_2, x_25);
if (x_26 == 0)
{
uint64_t x_27; uint8_t x_28; 
x_27 = lean_unbox_uint64(x_21);
x_28 = lean_uint64_dec_eq(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_24);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_31 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
x_32 = lean_box_uint64(x_1);
x_33 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l_Prod_map___redArg(x_31, x_33, x_22);
x_35 = lean_box_uint64(x_2);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_23);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_38, 2, x_22);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_24);
return x_38;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_CancellationToken_isCancelled(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Std_CancellationToken_new();
x_9 = lean_st_ref_get(x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
x_13 = l_Std_CancellationContext_new___closed__0;
lean_inc_ref(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_12, x_14, x_11);
x_16 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_12, x_2, x_15);
x_17 = 1;
x_18 = lean_uint64_add(x_12, x_17);
lean_ctor_set(x_9, 0, x_16);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_18);
x_19 = lean_st_ref_set(x_5, x_9);
x_20 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set_uint64(x_20, sizeof(void*)*2, x_12);
return x_20;
}
else
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Std_CancellationContext_new___closed__0;
lean_inc_ref(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_22, x_24, x_21);
x_26 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_22, x_2, x_25);
x_27 = 1;
x_28 = lean_uint64_add(x_22, x_27);
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_28);
x_30 = lean_st_ref_set(x_5, x_29);
x_31 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set_uint64(x_31, sizeof(void*)*2, x_22);
return x_31;
}
}
else
{
lean_dec_ref(x_3);
lean_inc_ref(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = l_Std_CancellationContext_fork___lam__0(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_6 = lean_box_uint64(x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Std_CancellationContext_fork___lam__0___boxed), 6, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_1);
x_8 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_CancellationContext_fork(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_unbox_uint64(x_3);
x_9 = lean_uint64_dec_lt(x_1, x_8);
if (x_9 == 0)
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_unbox_uint64(x_3);
x_11 = lean_uint64_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_1, x_6);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_23 = lean_nat_add(x_13, x_15);
x_24 = lean_nat_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
if (lean_is_scalar(x_7)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_7;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_5);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_26 = x_5;
} else {
 lean_dec_ref(x_5);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
x_30 = lean_ctor_get(x_19, 2);
x_31 = lean_ctor_get(x_19, 3);
x_32 = lean_ctor_get(x_19, 4);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_27);
x_35 = lean_nat_dec_lt(x_28, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; lean_object* x_47; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
x_37 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
x_38 = lean_nat_add(x_37, x_14);
lean_dec(x_37);
x_46 = lean_nat_add(x_13, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_31, 0);
lean_inc(x_54);
x_47 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_47 = x_55;
goto block_53;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
lean_ctor_set(x_43, 2, x_4);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_12);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_29);
lean_ctor_set(x_44, 2, x_30);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_add(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (lean_is_scalar(x_7)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_7;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_16);
lean_ctor_set(x_49, 2, x_17);
lean_ctor_set(x_49, 3, x_18);
lean_ctor_set(x_49, 4, x_31);
x_50 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
x_39 = x_49;
x_40 = x_50;
x_41 = x_51;
goto block_45;
}
else
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_39 = x_49;
x_40 = x_50;
x_41 = x_52;
goto block_45;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_7);
x_56 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
x_57 = lean_nat_add(x_56, x_14);
lean_dec(x_56);
x_58 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
x_59 = lean_nat_add(x_58, x_28);
lean_dec(x_58);
lean_inc_ref(x_12);
if (lean_is_scalar(x_26)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_26;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
lean_ctor_set(x_60, 2, x_4);
lean_ctor_set(x_60, 3, x_19);
lean_ctor_set(x_60, 4, x_12);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_12, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_12, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_12, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_12, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_12, 0);
lean_dec(x_66);
lean_ctor_set(x_12, 4, x_60);
lean_ctor_set(x_12, 3, x_18);
lean_ctor_set(x_12, 2, x_17);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_57);
return x_12;
}
else
{
lean_object* x_67; 
lean_dec(x_12);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_16);
lean_ctor_set(x_67, 2, x_17);
lean_ctor_set(x_67, 3, x_18);
lean_ctor_set(x_67, 4, x_60);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_12, 0);
lean_inc(x_68);
x_69 = lean_nat_add(x_13, x_68);
lean_dec(x_68);
if (lean_is_scalar(x_7)) {
 x_70 = lean_alloc_ctor(0, 5, 0);
} else {
 x_70 = x_7;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_4);
lean_ctor_set(x_70, 3, x_5);
lean_ctor_set(x_70, 4, x_12);
return x_70;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_5, 4);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
x_76 = lean_ctor_get(x_5, 2);
x_77 = lean_ctor_get(x_5, 4);
lean_dec(x_77);
x_78 = lean_ctor_get(x_5, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_nat_add(x_13, x_74);
lean_dec(x_74);
x_81 = lean_nat_add(x_13, x_79);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 3, x_72);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_81);
if (lean_is_scalar(x_7)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_7;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_82, 2, x_76);
lean_ctor_set(x_82, 3, x_71);
lean_ctor_set(x_82, 4, x_5);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
x_86 = lean_ctor_get(x_72, 0);
x_87 = lean_nat_add(x_13, x_83);
lean_dec(x_83);
x_88 = lean_nat_add(x_13, x_86);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_4);
lean_ctor_set(x_89, 3, x_72);
lean_ctor_set(x_89, 4, x_12);
if (lean_is_scalar(x_7)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_7;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set(x_90, 3, x_71);
lean_ctor_set(x_90, 4, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_5);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_5, 1);
x_93 = lean_ctor_get(x_5, 2);
x_94 = lean_ctor_get(x_5, 4);
lean_dec(x_94);
x_95 = lean_ctor_get(x_5, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_5, 0);
lean_dec(x_96);
x_97 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_5, 3, x_72);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_7;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
lean_ctor_set(x_98, 2, x_93);
lean_ctor_set(x_98, 3, x_71);
lean_ctor_set(x_98, 4, x_5);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_5);
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_13);
lean_ctor_set(x_102, 1, x_3);
lean_ctor_set(x_102, 2, x_4);
lean_ctor_set(x_102, 3, x_72);
lean_ctor_set(x_102, 4, x_72);
if (lean_is_scalar(x_7)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_7;
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_71);
lean_ctor_set(x_103, 4, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_5, 4);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
lean_inc(x_71);
x_105 = !lean_is_exclusive(x_5);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_5, 1);
x_107 = lean_ctor_get(x_5, 2);
x_108 = lean_ctor_get(x_5, 4);
lean_dec(x_108);
x_109 = lean_ctor_get(x_5, 3);
lean_dec(x_109);
x_110 = lean_ctor_get(x_5, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_104);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_104, 1);
x_113 = lean_ctor_get(x_104, 2);
x_114 = lean_ctor_get(x_104, 4);
lean_dec(x_114);
x_115 = lean_ctor_get(x_104, 3);
lean_dec(x_115);
x_116 = lean_ctor_get(x_104, 0);
lean_dec(x_116);
x_117 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_104, 4, x_71);
lean_ctor_set(x_104, 3, x_71);
lean_ctor_set(x_104, 2, x_107);
lean_ctor_set(x_104, 1, x_106);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_5, 4, x_71);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_7;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_104);
lean_ctor_set(x_118, 4, x_5);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_104, 1);
x_120 = lean_ctor_get(x_104, 2);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_104);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_13);
lean_ctor_set(x_122, 1, x_106);
lean_ctor_set(x_122, 2, x_107);
lean_ctor_set(x_122, 3, x_71);
lean_ctor_set(x_122, 4, x_71);
lean_ctor_set(x_5, 4, x_71);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_123 = lean_alloc_ctor(0, 5, 0);
} else {
 x_123 = x_7;
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set(x_123, 2, x_120);
lean_ctor_set(x_123, 3, x_122);
lean_ctor_set(x_123, 4, x_5);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_5, 1);
x_125 = lean_ctor_get(x_5, 2);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_5);
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 2);
lean_inc(x_127);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 x_128 = x_104;
} else {
 lean_dec_ref(x_104);
 x_128 = lean_box(0);
}
x_129 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_13);
lean_ctor_set(x_130, 1, x_124);
lean_ctor_set(x_130, 2, x_125);
lean_ctor_set(x_130, 3, x_71);
lean_ctor_set(x_130, 4, x_71);
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_13);
lean_ctor_set(x_131, 1, x_3);
lean_ctor_set(x_131, 2, x_4);
lean_ctor_set(x_131, 3, x_71);
lean_ctor_set(x_131, 4, x_71);
if (lean_is_scalar(x_7)) {
 x_132 = lean_alloc_ctor(0, 5, 0);
} else {
 x_132 = x_7;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_126);
lean_ctor_set(x_132, 2, x_127);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set(x_132, 4, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_7;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_3);
lean_ctor_set(x_134, 2, x_4);
lean_ctor_set(x_134, 3, x_5);
lean_ctor_set(x_134, 4, x_104);
return x_134;
}
}
}
else
{
lean_object* x_135; 
if (lean_is_scalar(x_7)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_7;
}
lean_ctor_set(x_135, 0, x_13);
lean_ctor_set(x_135, 1, x_3);
lean_ctor_set(x_135, 2, x_4);
lean_ctor_set(x_135, 3, x_5);
lean_ctor_set(x_135, 4, x_5);
return x_135;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_136 = lean_ctor_get(x_5, 0);
x_137 = lean_ctor_get(x_5, 1);
x_138 = lean_ctor_get(x_5, 2);
x_139 = lean_ctor_get(x_5, 3);
x_140 = lean_ctor_get(x_5, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_6, 0);
x_142 = lean_ctor_get(x_6, 1);
x_143 = lean_ctor_get(x_6, 2);
x_144 = lean_ctor_get(x_6, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_6, 4);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_dec_lt(x_136, x_141);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_148 = x_5;
} else {
 lean_dec_ref(x_5);
 x_148 = lean_box(0);
}
x_149 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_137, x_138, x_139, x_140);
x_150 = lean_ctor_get(x_149, 2);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec_ref(x_149);
x_153 = lean_ctor_get(x_150, 0);
x_154 = lean_unsigned_to_nat(3u);
x_155 = lean_nat_mul(x_154, x_153);
x_156 = lean_nat_dec_lt(x_155, x_141);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_144);
x_157 = lean_nat_add(x_146, x_153);
x_158 = lean_nat_add(x_157, x_141);
lean_dec(x_157);
if (lean_is_scalar(x_148)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_148;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_152);
lean_ctor_set(x_159, 3, x_150);
lean_ctor_set(x_159, 4, x_6);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_160 = x_6;
} else {
 lean_dec_ref(x_6);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_144, 0);
x_162 = lean_ctor_get(x_144, 1);
x_163 = lean_ctor_get(x_144, 2);
x_164 = lean_ctor_get(x_144, 3);
x_165 = lean_ctor_get(x_144, 4);
x_166 = lean_ctor_get(x_145, 0);
x_167 = lean_unsigned_to_nat(2u);
x_168 = lean_nat_mul(x_167, x_166);
x_169 = lean_nat_dec_lt(x_161, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_180; 
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 lean_ctor_release(x_144, 4);
 x_170 = x_144;
} else {
 lean_dec_ref(x_144);
 x_170 = lean_box(0);
}
x_171 = lean_nat_add(x_146, x_153);
x_172 = lean_nat_add(x_171, x_141);
lean_dec(x_141);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_164, 0);
lean_inc(x_187);
x_180 = x_187;
goto block_186;
}
else
{
lean_object* x_188; 
x_188 = lean_unsigned_to_nat(0u);
x_180 = x_188;
goto block_186;
}
block_179:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_nat_add(x_173, x_175);
lean_dec(x_175);
lean_dec(x_173);
if (lean_is_scalar(x_170)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_170;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_142);
lean_ctor_set(x_177, 2, x_143);
lean_ctor_set(x_177, 3, x_165);
lean_ctor_set(x_177, 4, x_145);
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_162);
lean_ctor_set(x_178, 2, x_163);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 4, x_177);
return x_178;
}
block_186:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_nat_add(x_171, x_180);
lean_dec(x_180);
lean_dec(x_171);
if (lean_is_scalar(x_148)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_148;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_151);
lean_ctor_set(x_182, 2, x_152);
lean_ctor_set(x_182, 3, x_150);
lean_ctor_set(x_182, 4, x_164);
x_183 = lean_nat_add(x_146, x_166);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_165, 0);
lean_inc(x_184);
x_173 = x_183;
x_174 = x_182;
x_175 = x_184;
goto block_179;
}
else
{
lean_object* x_185; 
x_185 = lean_unsigned_to_nat(0u);
x_173 = x_183;
x_174 = x_182;
x_175 = x_185;
goto block_179;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_nat_add(x_146, x_153);
x_190 = lean_nat_add(x_189, x_141);
lean_dec(x_141);
x_191 = lean_nat_add(x_189, x_161);
lean_dec(x_189);
if (lean_is_scalar(x_160)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_160;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_151);
lean_ctor_set(x_192, 2, x_152);
lean_ctor_set(x_192, 3, x_150);
lean_ctor_set(x_192, 4, x_144);
if (lean_is_scalar(x_148)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_148;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_142);
lean_ctor_set(x_193, 2, x_143);
lean_ctor_set(x_193, 3, x_192);
lean_ctor_set(x_193, 4, x_145);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_194 = !lean_is_exclusive(x_6);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_6, 4);
lean_dec(x_195);
x_196 = lean_ctor_get(x_6, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_6, 2);
lean_dec(x_197);
x_198 = lean_ctor_get(x_6, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_6, 0);
lean_dec(x_199);
if (lean_obj_tag(x_144) == 0)
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_149, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_149, 1);
lean_inc(x_201);
lean_dec_ref(x_149);
x_202 = lean_ctor_get(x_144, 0);
x_203 = lean_nat_add(x_146, x_141);
lean_dec(x_141);
x_204 = lean_nat_add(x_146, x_202);
lean_ctor_set(x_6, 4, x_144);
lean_ctor_set(x_6, 3, x_150);
lean_ctor_set(x_6, 2, x_201);
lean_ctor_set(x_6, 1, x_200);
lean_ctor_set(x_6, 0, x_204);
if (lean_is_scalar(x_148)) {
 x_205 = lean_alloc_ctor(0, 5, 0);
} else {
 x_205 = x_148;
}
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_142);
lean_ctor_set(x_205, 2, x_143);
lean_ctor_set(x_205, 3, x_6);
lean_ctor_set(x_205, 4, x_145);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_141);
x_206 = lean_ctor_get(x_149, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_149, 1);
lean_inc(x_207);
lean_dec_ref(x_149);
x_208 = !lean_is_exclusive(x_144);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_144, 1);
x_210 = lean_ctor_get(x_144, 2);
x_211 = lean_ctor_get(x_144, 4);
lean_dec(x_211);
x_212 = lean_ctor_get(x_144, 3);
lean_dec(x_212);
x_213 = lean_ctor_get(x_144, 0);
lean_dec(x_213);
x_214 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_144, 4, x_145);
lean_ctor_set(x_144, 3, x_145);
lean_ctor_set(x_144, 2, x_207);
lean_ctor_set(x_144, 1, x_206);
lean_ctor_set(x_144, 0, x_146);
lean_ctor_set(x_6, 3, x_145);
lean_ctor_set(x_6, 0, x_146);
if (lean_is_scalar(x_148)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_148;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
lean_ctor_set(x_215, 2, x_210);
lean_ctor_set(x_215, 3, x_144);
lean_ctor_set(x_215, 4, x_6);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_144, 1);
x_217 = lean_ctor_get(x_144, 2);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_144);
x_218 = lean_unsigned_to_nat(3u);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_146);
lean_ctor_set(x_219, 1, x_206);
lean_ctor_set(x_219, 2, x_207);
lean_ctor_set(x_219, 3, x_145);
lean_ctor_set(x_219, 4, x_145);
lean_ctor_set(x_6, 3, x_145);
lean_ctor_set(x_6, 0, x_146);
if (lean_is_scalar(x_148)) {
 x_220 = lean_alloc_ctor(0, 5, 0);
} else {
 x_220 = x_148;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_216);
lean_ctor_set(x_220, 2, x_217);
lean_ctor_set(x_220, 3, x_219);
lean_ctor_set(x_220, 4, x_6);
return x_220;
}
}
}
else
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_141);
x_221 = lean_ctor_get(x_149, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_149, 1);
lean_inc(x_222);
lean_dec_ref(x_149);
x_223 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_144);
lean_ctor_set(x_6, 2, x_222);
lean_ctor_set(x_6, 1, x_221);
lean_ctor_set(x_6, 0, x_146);
if (lean_is_scalar(x_148)) {
 x_224 = lean_alloc_ctor(0, 5, 0);
} else {
 x_224 = x_148;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_142);
lean_ctor_set(x_224, 2, x_143);
lean_ctor_set(x_224, 3, x_6);
lean_ctor_set(x_224, 4, x_145);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_149, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_149, 1);
lean_inc(x_226);
lean_dec_ref(x_149);
lean_ctor_set(x_6, 3, x_145);
x_227 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_148)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_148;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
lean_ctor_set(x_228, 2, x_226);
lean_ctor_set(x_228, 3, x_145);
lean_ctor_set(x_228, 4, x_6);
return x_228;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_144) == 0)
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_149, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_149, 1);
lean_inc(x_230);
lean_dec_ref(x_149);
x_231 = lean_ctor_get(x_144, 0);
x_232 = lean_nat_add(x_146, x_141);
lean_dec(x_141);
x_233 = lean_nat_add(x_146, x_231);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_229);
lean_ctor_set(x_234, 2, x_230);
lean_ctor_set(x_234, 3, x_150);
lean_ctor_set(x_234, 4, x_144);
if (lean_is_scalar(x_148)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_148;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_142);
lean_ctor_set(x_235, 2, x_143);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_145);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_141);
x_236 = lean_ctor_get(x_149, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_149, 1);
lean_inc(x_237);
lean_dec_ref(x_149);
x_238 = lean_ctor_get(x_144, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_144, 2);
lean_inc(x_239);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 lean_ctor_release(x_144, 4);
 x_240 = x_144;
} else {
 lean_dec_ref(x_144);
 x_240 = lean_box(0);
}
x_241 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 5, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_146);
lean_ctor_set(x_242, 1, x_236);
lean_ctor_set(x_242, 2, x_237);
lean_ctor_set(x_242, 3, x_145);
lean_ctor_set(x_242, 4, x_145);
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_146);
lean_ctor_set(x_243, 1, x_142);
lean_ctor_set(x_243, 2, x_143);
lean_ctor_set(x_243, 3, x_145);
lean_ctor_set(x_243, 4, x_145);
if (lean_is_scalar(x_148)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_148;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_238);
lean_ctor_set(x_244, 2, x_239);
lean_ctor_set(x_244, 3, x_242);
lean_ctor_set(x_244, 4, x_243);
return x_244;
}
}
else
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_141);
x_245 = lean_ctor_get(x_149, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_149, 1);
lean_inc(x_246);
lean_dec_ref(x_149);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_146);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_144);
lean_ctor_set(x_248, 4, x_144);
if (lean_is_scalar(x_148)) {
 x_249 = lean_alloc_ctor(0, 5, 0);
} else {
 x_249 = x_148;
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_142);
lean_ctor_set(x_249, 2, x_143);
lean_ctor_set(x_249, 3, x_248);
lean_ctor_set(x_249, 4, x_145);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_149, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_149, 1);
lean_inc(x_251);
lean_dec_ref(x_149);
x_252 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_252, 0, x_141);
lean_ctor_set(x_252, 1, x_142);
lean_ctor_set(x_252, 2, x_143);
lean_ctor_set(x_252, 3, x_145);
lean_ctor_set(x_252, 4, x_145);
x_253 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_148)) {
 x_254 = lean_alloc_ctor(0, 5, 0);
} else {
 x_254 = x_148;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
lean_ctor_set(x_254, 2, x_251);
lean_ctor_set(x_254, 3, x_145);
lean_ctor_set(x_254, 4, x_252);
return x_254;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_255 = x_6;
} else {
 lean_dec_ref(x_6);
 x_255 = lean_box(0);
}
x_256 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_142, x_143, x_144, x_145);
x_257 = lean_ctor_get(x_256, 2);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec_ref(x_256);
x_260 = lean_ctor_get(x_257, 0);
x_261 = lean_unsigned_to_nat(3u);
x_262 = lean_nat_mul(x_261, x_260);
x_263 = lean_nat_dec_lt(x_262, x_136);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_140);
x_264 = lean_nat_add(x_146, x_136);
x_265 = lean_nat_add(x_264, x_260);
lean_dec(x_264);
if (lean_is_scalar(x_255)) {
 x_266 = lean_alloc_ctor(0, 5, 0);
} else {
 x_266 = x_255;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_258);
lean_ctor_set(x_266, 2, x_259);
lean_ctor_set(x_266, 3, x_5);
lean_ctor_set(x_266, 4, x_257);
return x_266;
}
else
{
uint8_t x_267; 
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_267 = !lean_is_exclusive(x_5);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_268 = lean_ctor_get(x_5, 4);
lean_dec(x_268);
x_269 = lean_ctor_get(x_5, 3);
lean_dec(x_269);
x_270 = lean_ctor_get(x_5, 2);
lean_dec(x_270);
x_271 = lean_ctor_get(x_5, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_5, 0);
lean_dec(x_272);
x_273 = lean_ctor_get(x_139, 0);
x_274 = lean_ctor_get(x_140, 0);
x_275 = lean_ctor_get(x_140, 1);
x_276 = lean_ctor_get(x_140, 2);
x_277 = lean_ctor_get(x_140, 3);
x_278 = lean_ctor_get(x_140, 4);
x_279 = lean_unsigned_to_nat(2u);
x_280 = lean_nat_mul(x_279, x_273);
x_281 = lean_nat_dec_lt(x_274, x_280);
lean_dec(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_298; lean_object* x_299; 
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_free_object(x_5);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_282 = x_140;
} else {
 lean_dec_ref(x_140);
 x_282 = lean_box(0);
}
x_283 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_284 = lean_nat_add(x_283, x_260);
lean_dec(x_283);
x_298 = lean_nat_add(x_146, x_273);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_277, 0);
lean_inc(x_306);
x_299 = x_306;
goto block_305;
}
else
{
lean_object* x_307; 
x_307 = lean_unsigned_to_nat(0u);
x_299 = x_307;
goto block_305;
}
block_297:
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_nat_add(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
lean_inc_ref(x_257);
if (lean_is_scalar(x_282)) {
 x_289 = lean_alloc_ctor(0, 5, 0);
} else {
 x_289 = x_282;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_258);
lean_ctor_set(x_289, 2, x_259);
lean_ctor_set(x_289, 3, x_278);
lean_ctor_set(x_289, 4, x_257);
x_290 = !lean_is_exclusive(x_257);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_257, 4);
lean_dec(x_291);
x_292 = lean_ctor_get(x_257, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_257, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_257, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_257, 0);
lean_dec(x_295);
lean_ctor_set(x_257, 4, x_289);
lean_ctor_set(x_257, 3, x_285);
lean_ctor_set(x_257, 2, x_276);
lean_ctor_set(x_257, 1, x_275);
lean_ctor_set(x_257, 0, x_284);
return x_257;
}
else
{
lean_object* x_296; 
lean_dec(x_257);
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_284);
lean_ctor_set(x_296, 1, x_275);
lean_ctor_set(x_296, 2, x_276);
lean_ctor_set(x_296, 3, x_285);
lean_ctor_set(x_296, 4, x_289);
return x_296;
}
}
block_305:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_nat_add(x_298, x_299);
lean_dec(x_299);
lean_dec(x_298);
if (lean_is_scalar(x_255)) {
 x_301 = lean_alloc_ctor(0, 5, 0);
} else {
 x_301 = x_255;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_137);
lean_ctor_set(x_301, 2, x_138);
lean_ctor_set(x_301, 3, x_139);
lean_ctor_set(x_301, 4, x_277);
x_302 = lean_nat_add(x_146, x_260);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_278, 0);
lean_inc(x_303);
x_285 = x_301;
x_286 = x_302;
x_287 = x_303;
goto block_297;
}
else
{
lean_object* x_304; 
x_304 = lean_unsigned_to_nat(0u);
x_285 = x_301;
x_286 = x_302;
x_287 = x_304;
goto block_297;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_309 = lean_nat_add(x_308, x_260);
lean_dec(x_308);
x_310 = lean_nat_add(x_146, x_260);
x_311 = lean_nat_add(x_310, x_274);
lean_dec(x_310);
if (lean_is_scalar(x_255)) {
 x_312 = lean_alloc_ctor(0, 5, 0);
} else {
 x_312 = x_255;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_258);
lean_ctor_set(x_312, 2, x_259);
lean_ctor_set(x_312, 3, x_140);
lean_ctor_set(x_312, 4, x_257);
lean_ctor_set(x_5, 4, x_312);
lean_ctor_set(x_5, 0, x_309);
return x_5;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
lean_dec(x_5);
x_313 = lean_ctor_get(x_139, 0);
x_314 = lean_ctor_get(x_140, 0);
x_315 = lean_ctor_get(x_140, 1);
x_316 = lean_ctor_get(x_140, 2);
x_317 = lean_ctor_get(x_140, 3);
x_318 = lean_ctor_get(x_140, 4);
x_319 = lean_unsigned_to_nat(2u);
x_320 = lean_nat_mul(x_319, x_313);
x_321 = lean_nat_dec_lt(x_314, x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_333; lean_object* x_334; 
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_322 = x_140;
} else {
 lean_dec_ref(x_140);
 x_322 = lean_box(0);
}
x_323 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_324 = lean_nat_add(x_323, x_260);
lean_dec(x_323);
x_333 = lean_nat_add(x_146, x_313);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_317, 0);
lean_inc(x_341);
x_334 = x_341;
goto block_340;
}
else
{
lean_object* x_342; 
x_342 = lean_unsigned_to_nat(0u);
x_334 = x_342;
goto block_340;
}
block_332:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_328 = lean_nat_add(x_326, x_327);
lean_dec(x_327);
lean_dec(x_326);
lean_inc_ref(x_257);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(0, 5, 0);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_258);
lean_ctor_set(x_329, 2, x_259);
lean_ctor_set(x_329, 3, x_318);
lean_ctor_set(x_329, 4, x_257);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 x_330 = x_257;
} else {
 lean_dec_ref(x_257);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_315);
lean_ctor_set(x_331, 2, x_316);
lean_ctor_set(x_331, 3, x_325);
lean_ctor_set(x_331, 4, x_329);
return x_331;
}
block_340:
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_nat_add(x_333, x_334);
lean_dec(x_334);
lean_dec(x_333);
if (lean_is_scalar(x_255)) {
 x_336 = lean_alloc_ctor(0, 5, 0);
} else {
 x_336 = x_255;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_137);
lean_ctor_set(x_336, 2, x_138);
lean_ctor_set(x_336, 3, x_139);
lean_ctor_set(x_336, 4, x_317);
x_337 = lean_nat_add(x_146, x_260);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_318, 0);
lean_inc(x_338);
x_325 = x_336;
x_326 = x_337;
x_327 = x_338;
goto block_332;
}
else
{
lean_object* x_339; 
x_339 = lean_unsigned_to_nat(0u);
x_325 = x_336;
x_326 = x_337;
x_327 = x_339;
goto block_332;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_344 = lean_nat_add(x_343, x_260);
lean_dec(x_343);
x_345 = lean_nat_add(x_146, x_260);
x_346 = lean_nat_add(x_345, x_314);
lean_dec(x_345);
if (lean_is_scalar(x_255)) {
 x_347 = lean_alloc_ctor(0, 5, 0);
} else {
 x_347 = x_255;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_258);
lean_ctor_set(x_347, 2, x_259);
lean_ctor_set(x_347, 3, x_140);
lean_ctor_set(x_347, 4, x_257);
x_348 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_137);
lean_ctor_set(x_348, 2, x_138);
lean_ctor_set(x_348, 3, x_139);
lean_ctor_set(x_348, 4, x_347);
return x_348;
}
}
}
}
else
{
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_349; 
lean_inc_ref(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_349 = !lean_is_exclusive(x_5);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_350 = lean_ctor_get(x_5, 4);
lean_dec(x_350);
x_351 = lean_ctor_get(x_5, 3);
lean_dec(x_351);
x_352 = lean_ctor_get(x_5, 2);
lean_dec(x_352);
x_353 = lean_ctor_get(x_5, 1);
lean_dec(x_353);
x_354 = lean_ctor_get(x_5, 0);
lean_dec(x_354);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_355 = lean_ctor_get(x_256, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_256, 1);
lean_inc(x_356);
lean_dec_ref(x_256);
x_357 = lean_ctor_get(x_140, 0);
x_358 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_359 = lean_nat_add(x_146, x_357);
if (lean_is_scalar(x_255)) {
 x_360 = lean_alloc_ctor(0, 5, 0);
} else {
 x_360 = x_255;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_355);
lean_ctor_set(x_360, 2, x_356);
lean_ctor_set(x_360, 3, x_140);
lean_ctor_set(x_360, 4, x_257);
lean_ctor_set(x_5, 4, x_360);
lean_ctor_set(x_5, 0, x_358);
return x_5;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_136);
x_361 = lean_ctor_get(x_256, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_256, 1);
lean_inc(x_362);
lean_dec_ref(x_256);
x_363 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_255)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_255;
}
lean_ctor_set(x_364, 0, x_146);
lean_ctor_set(x_364, 1, x_361);
lean_ctor_set(x_364, 2, x_362);
lean_ctor_set(x_364, 3, x_140);
lean_ctor_set(x_364, 4, x_140);
lean_ctor_set(x_5, 4, x_364);
lean_ctor_set(x_5, 0, x_363);
return x_5;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_365 = lean_ctor_get(x_256, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_256, 1);
lean_inc(x_366);
lean_dec_ref(x_256);
x_367 = lean_ctor_get(x_140, 0);
x_368 = lean_nat_add(x_146, x_136);
lean_dec(x_136);
x_369 = lean_nat_add(x_146, x_367);
if (lean_is_scalar(x_255)) {
 x_370 = lean_alloc_ctor(0, 5, 0);
} else {
 x_370 = x_255;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_365);
lean_ctor_set(x_370, 2, x_366);
lean_ctor_set(x_370, 3, x_140);
lean_ctor_set(x_370, 4, x_257);
x_371 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_137);
lean_ctor_set(x_371, 2, x_138);
lean_ctor_set(x_371, 3, x_139);
lean_ctor_set(x_371, 4, x_370);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_136);
x_372 = lean_ctor_get(x_256, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_256, 1);
lean_inc(x_373);
lean_dec_ref(x_256);
x_374 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_255)) {
 x_375 = lean_alloc_ctor(0, 5, 0);
} else {
 x_375 = x_255;
}
lean_ctor_set(x_375, 0, x_146);
lean_ctor_set(x_375, 1, x_372);
lean_ctor_set(x_375, 2, x_373);
lean_ctor_set(x_375, 3, x_140);
lean_ctor_set(x_375, 4, x_140);
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_137);
lean_ctor_set(x_376, 2, x_138);
lean_ctor_set(x_376, 3, x_139);
lean_ctor_set(x_376, 4, x_375);
return x_376;
}
}
}
else
{
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_377; 
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
x_377 = !lean_is_exclusive(x_5);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_378 = lean_ctor_get(x_5, 4);
lean_dec(x_378);
x_379 = lean_ctor_get(x_5, 3);
lean_dec(x_379);
x_380 = lean_ctor_get(x_5, 2);
lean_dec(x_380);
x_381 = lean_ctor_get(x_5, 1);
lean_dec(x_381);
x_382 = lean_ctor_get(x_5, 0);
lean_dec(x_382);
x_383 = lean_ctor_get(x_256, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_256, 1);
lean_inc(x_384);
lean_dec_ref(x_256);
x_385 = !lean_is_exclusive(x_140);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_386 = lean_ctor_get(x_140, 1);
x_387 = lean_ctor_get(x_140, 2);
x_388 = lean_ctor_get(x_140, 4);
lean_dec(x_388);
x_389 = lean_ctor_get(x_140, 3);
lean_dec(x_389);
x_390 = lean_ctor_get(x_140, 0);
lean_dec(x_390);
x_391 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set(x_140, 3, x_139);
lean_ctor_set(x_140, 2, x_138);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set(x_140, 0, x_146);
if (lean_is_scalar(x_255)) {
 x_392 = lean_alloc_ctor(0, 5, 0);
} else {
 x_392 = x_255;
}
lean_ctor_set(x_392, 0, x_146);
lean_ctor_set(x_392, 1, x_383);
lean_ctor_set(x_392, 2, x_384);
lean_ctor_set(x_392, 3, x_139);
lean_ctor_set(x_392, 4, x_139);
lean_ctor_set(x_5, 4, x_392);
lean_ctor_set(x_5, 3, x_140);
lean_ctor_set(x_5, 2, x_387);
lean_ctor_set(x_5, 1, x_386);
lean_ctor_set(x_5, 0, x_391);
return x_5;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_393 = lean_ctor_get(x_140, 1);
x_394 = lean_ctor_get(x_140, 2);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_140);
x_395 = lean_unsigned_to_nat(3u);
x_396 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_396, 0, x_146);
lean_ctor_set(x_396, 1, x_137);
lean_ctor_set(x_396, 2, x_138);
lean_ctor_set(x_396, 3, x_139);
lean_ctor_set(x_396, 4, x_139);
if (lean_is_scalar(x_255)) {
 x_397 = lean_alloc_ctor(0, 5, 0);
} else {
 x_397 = x_255;
}
lean_ctor_set(x_397, 0, x_146);
lean_ctor_set(x_397, 1, x_383);
lean_ctor_set(x_397, 2, x_384);
lean_ctor_set(x_397, 3, x_139);
lean_ctor_set(x_397, 4, x_139);
lean_ctor_set(x_5, 4, x_397);
lean_ctor_set(x_5, 3, x_396);
lean_ctor_set(x_5, 2, x_394);
lean_ctor_set(x_5, 1, x_393);
lean_ctor_set(x_5, 0, x_395);
return x_5;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_5);
x_398 = lean_ctor_get(x_256, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_256, 1);
lean_inc(x_399);
lean_dec_ref(x_256);
x_400 = lean_ctor_get(x_140, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_140, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_402 = x_140;
} else {
 lean_dec_ref(x_140);
 x_402 = lean_box(0);
}
x_403 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(0, 5, 0);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_146);
lean_ctor_set(x_404, 1, x_137);
lean_ctor_set(x_404, 2, x_138);
lean_ctor_set(x_404, 3, x_139);
lean_ctor_set(x_404, 4, x_139);
if (lean_is_scalar(x_255)) {
 x_405 = lean_alloc_ctor(0, 5, 0);
} else {
 x_405 = x_255;
}
lean_ctor_set(x_405, 0, x_146);
lean_ctor_set(x_405, 1, x_398);
lean_ctor_set(x_405, 2, x_399);
lean_ctor_set(x_405, 3, x_139);
lean_ctor_set(x_405, 4, x_139);
x_406 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_400);
lean_ctor_set(x_406, 2, x_401);
lean_ctor_set(x_406, 3, x_404);
lean_ctor_set(x_406, 4, x_405);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_256, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_256, 1);
lean_inc(x_408);
lean_dec_ref(x_256);
x_409 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_255)) {
 x_410 = lean_alloc_ctor(0, 5, 0);
} else {
 x_410 = x_255;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_407);
lean_ctor_set(x_410, 2, x_408);
lean_ctor_set(x_410, 3, x_5);
lean_ctor_set(x_410, 4, x_140);
return x_410;
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; 
x_411 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_1, x_5);
x_412 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_411) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_6, 0);
x_415 = lean_ctor_get(x_6, 1);
x_416 = lean_ctor_get(x_6, 2);
x_417 = lean_ctor_get(x_6, 3);
lean_inc(x_417);
x_418 = lean_ctor_get(x_6, 4);
x_419 = lean_unsigned_to_nat(3u);
x_420 = lean_nat_mul(x_419, x_413);
x_421 = lean_nat_dec_lt(x_420, x_414);
lean_dec(x_420);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_417);
x_422 = lean_nat_add(x_412, x_413);
lean_dec(x_413);
x_423 = lean_nat_add(x_422, x_414);
lean_dec(x_422);
if (lean_is_scalar(x_7)) {
 x_424 = lean_alloc_ctor(0, 5, 0);
} else {
 x_424 = x_7;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_3);
lean_ctor_set(x_424, 2, x_4);
lean_ctor_set(x_424, 3, x_411);
lean_ctor_set(x_424, 4, x_6);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
lean_inc(x_418);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_425 = x_6;
} else {
 lean_dec_ref(x_6);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_417, 0);
x_427 = lean_ctor_get(x_417, 1);
x_428 = lean_ctor_get(x_417, 2);
x_429 = lean_ctor_get(x_417, 3);
x_430 = lean_ctor_get(x_417, 4);
x_431 = lean_ctor_get(x_418, 0);
x_432 = lean_unsigned_to_nat(2u);
x_433 = lean_nat_mul(x_432, x_431);
x_434 = lean_nat_dec_lt(x_426, x_433);
lean_dec(x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_445; 
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 x_435 = x_417;
} else {
 lean_dec_ref(x_417);
 x_435 = lean_box(0);
}
x_436 = lean_nat_add(x_412, x_413);
lean_dec(x_413);
x_437 = lean_nat_add(x_436, x_414);
lean_dec(x_414);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_429, 0);
lean_inc(x_452);
x_445 = x_452;
goto block_451;
}
else
{
lean_object* x_453; 
x_453 = lean_unsigned_to_nat(0u);
x_445 = x_453;
goto block_451;
}
block_444:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_nat_add(x_438, x_440);
lean_dec(x_440);
lean_dec(x_438);
if (lean_is_scalar(x_435)) {
 x_442 = lean_alloc_ctor(0, 5, 0);
} else {
 x_442 = x_435;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_415);
lean_ctor_set(x_442, 2, x_416);
lean_ctor_set(x_442, 3, x_430);
lean_ctor_set(x_442, 4, x_418);
if (lean_is_scalar(x_425)) {
 x_443 = lean_alloc_ctor(0, 5, 0);
} else {
 x_443 = x_425;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_427);
lean_ctor_set(x_443, 2, x_428);
lean_ctor_set(x_443, 3, x_439);
lean_ctor_set(x_443, 4, x_442);
return x_443;
}
block_451:
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_nat_add(x_436, x_445);
lean_dec(x_445);
lean_dec(x_436);
if (lean_is_scalar(x_7)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_7;
}
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_3);
lean_ctor_set(x_447, 2, x_4);
lean_ctor_set(x_447, 3, x_411);
lean_ctor_set(x_447, 4, x_429);
x_448 = lean_nat_add(x_412, x_431);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_430, 0);
lean_inc(x_449);
x_438 = x_448;
x_439 = x_447;
x_440 = x_449;
goto block_444;
}
else
{
lean_object* x_450; 
x_450 = lean_unsigned_to_nat(0u);
x_438 = x_448;
x_439 = x_447;
x_440 = x_450;
goto block_444;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
lean_dec(x_7);
x_454 = lean_nat_add(x_412, x_413);
lean_dec(x_413);
x_455 = lean_nat_add(x_454, x_414);
lean_dec(x_414);
x_456 = lean_nat_add(x_454, x_426);
lean_dec(x_454);
lean_inc_ref(x_411);
if (lean_is_scalar(x_425)) {
 x_457 = lean_alloc_ctor(0, 5, 0);
} else {
 x_457 = x_425;
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_3);
lean_ctor_set(x_457, 2, x_4);
lean_ctor_set(x_457, 3, x_411);
lean_ctor_set(x_457, 4, x_417);
x_458 = !lean_is_exclusive(x_411);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_459 = lean_ctor_get(x_411, 4);
lean_dec(x_459);
x_460 = lean_ctor_get(x_411, 3);
lean_dec(x_460);
x_461 = lean_ctor_get(x_411, 2);
lean_dec(x_461);
x_462 = lean_ctor_get(x_411, 1);
lean_dec(x_462);
x_463 = lean_ctor_get(x_411, 0);
lean_dec(x_463);
lean_ctor_set(x_411, 4, x_418);
lean_ctor_set(x_411, 3, x_457);
lean_ctor_set(x_411, 2, x_416);
lean_ctor_set(x_411, 1, x_415);
lean_ctor_set(x_411, 0, x_455);
return x_411;
}
else
{
lean_object* x_464; 
lean_dec(x_411);
x_464 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_464, 0, x_455);
lean_ctor_set(x_464, 1, x_415);
lean_ctor_set(x_464, 2, x_416);
lean_ctor_set(x_464, 3, x_457);
lean_ctor_set(x_464, 4, x_418);
return x_464;
}
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_411, 0);
lean_inc(x_465);
x_466 = lean_nat_add(x_412, x_465);
lean_dec(x_465);
if (lean_is_scalar(x_7)) {
 x_467 = lean_alloc_ctor(0, 5, 0);
} else {
 x_467 = x_7;
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_3);
lean_ctor_set(x_467, 2, x_4);
lean_ctor_set(x_467, 3, x_411);
lean_ctor_set(x_467, 4, x_6);
return x_467;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_6, 3);
lean_inc(x_468);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; 
x_469 = lean_ctor_get(x_6, 4);
lean_inc(x_469);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_6);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_471 = lean_ctor_get(x_6, 0);
x_472 = lean_ctor_get(x_6, 1);
x_473 = lean_ctor_get(x_6, 2);
x_474 = lean_ctor_get(x_6, 4);
lean_dec(x_474);
x_475 = lean_ctor_get(x_6, 3);
lean_dec(x_475);
x_476 = lean_ctor_get(x_468, 0);
x_477 = lean_nat_add(x_412, x_471);
lean_dec(x_471);
x_478 = lean_nat_add(x_412, x_476);
lean_ctor_set(x_6, 4, x_468);
lean_ctor_set(x_6, 3, x_411);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_478);
if (lean_is_scalar(x_7)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_7;
}
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_472);
lean_ctor_set(x_479, 2, x_473);
lean_ctor_set(x_479, 3, x_6);
lean_ctor_set(x_479, 4, x_469);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_480 = lean_ctor_get(x_6, 0);
x_481 = lean_ctor_get(x_6, 1);
x_482 = lean_ctor_get(x_6, 2);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_6);
x_483 = lean_ctor_get(x_468, 0);
x_484 = lean_nat_add(x_412, x_480);
lean_dec(x_480);
x_485 = lean_nat_add(x_412, x_483);
x_486 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_3);
lean_ctor_set(x_486, 2, x_4);
lean_ctor_set(x_486, 3, x_411);
lean_ctor_set(x_486, 4, x_468);
if (lean_is_scalar(x_7)) {
 x_487 = lean_alloc_ctor(0, 5, 0);
} else {
 x_487 = x_7;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_481);
lean_ctor_set(x_487, 2, x_482);
lean_ctor_set(x_487, 3, x_486);
lean_ctor_set(x_487, 4, x_469);
return x_487;
}
}
else
{
uint8_t x_488; 
x_488 = !lean_is_exclusive(x_6);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_489 = lean_ctor_get(x_6, 4);
lean_dec(x_489);
x_490 = lean_ctor_get(x_6, 3);
lean_dec(x_490);
x_491 = lean_ctor_get(x_6, 0);
lean_dec(x_491);
x_492 = !lean_is_exclusive(x_468);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_468, 1);
x_494 = lean_ctor_get(x_468, 2);
x_495 = lean_ctor_get(x_468, 4);
lean_dec(x_495);
x_496 = lean_ctor_get(x_468, 3);
lean_dec(x_496);
x_497 = lean_ctor_get(x_468, 0);
lean_dec(x_497);
x_498 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_468, 4, x_469);
lean_ctor_set(x_468, 3, x_469);
lean_ctor_set(x_468, 2, x_4);
lean_ctor_set(x_468, 1, x_3);
lean_ctor_set(x_468, 0, x_412);
lean_ctor_set(x_6, 3, x_469);
lean_ctor_set(x_6, 0, x_412);
if (lean_is_scalar(x_7)) {
 x_499 = lean_alloc_ctor(0, 5, 0);
} else {
 x_499 = x_7;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_493);
lean_ctor_set(x_499, 2, x_494);
lean_ctor_set(x_499, 3, x_468);
lean_ctor_set(x_499, 4, x_6);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_ctor_get(x_468, 1);
x_501 = lean_ctor_get(x_468, 2);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_468);
x_502 = lean_unsigned_to_nat(3u);
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_412);
lean_ctor_set(x_503, 1, x_3);
lean_ctor_set(x_503, 2, x_4);
lean_ctor_set(x_503, 3, x_469);
lean_ctor_set(x_503, 4, x_469);
lean_ctor_set(x_6, 3, x_469);
lean_ctor_set(x_6, 0, x_412);
if (lean_is_scalar(x_7)) {
 x_504 = lean_alloc_ctor(0, 5, 0);
} else {
 x_504 = x_7;
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_500);
lean_ctor_set(x_504, 2, x_501);
lean_ctor_set(x_504, 3, x_503);
lean_ctor_set(x_504, 4, x_6);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_505 = lean_ctor_get(x_6, 1);
x_506 = lean_ctor_get(x_6, 2);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_6);
x_507 = lean_ctor_get(x_468, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_468, 2);
lean_inc(x_508);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 lean_ctor_release(x_468, 3);
 lean_ctor_release(x_468, 4);
 x_509 = x_468;
} else {
 lean_dec_ref(x_468);
 x_509 = lean_box(0);
}
x_510 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_509)) {
 x_511 = lean_alloc_ctor(0, 5, 0);
} else {
 x_511 = x_509;
}
lean_ctor_set(x_511, 0, x_412);
lean_ctor_set(x_511, 1, x_3);
lean_ctor_set(x_511, 2, x_4);
lean_ctor_set(x_511, 3, x_469);
lean_ctor_set(x_511, 4, x_469);
x_512 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_512, 0, x_412);
lean_ctor_set(x_512, 1, x_505);
lean_ctor_set(x_512, 2, x_506);
lean_ctor_set(x_512, 3, x_469);
lean_ctor_set(x_512, 4, x_469);
if (lean_is_scalar(x_7)) {
 x_513 = lean_alloc_ctor(0, 5, 0);
} else {
 x_513 = x_7;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_507);
lean_ctor_set(x_513, 2, x_508);
lean_ctor_set(x_513, 3, x_511);
lean_ctor_set(x_513, 4, x_512);
return x_513;
}
}
}
else
{
lean_object* x_514; 
x_514 = lean_ctor_get(x_6, 4);
lean_inc(x_514);
if (lean_obj_tag(x_514) == 0)
{
uint8_t x_515; 
x_515 = !lean_is_exclusive(x_6);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_516 = lean_ctor_get(x_6, 1);
x_517 = lean_ctor_get(x_6, 2);
x_518 = lean_ctor_get(x_6, 4);
lean_dec(x_518);
x_519 = lean_ctor_get(x_6, 3);
lean_dec(x_519);
x_520 = lean_ctor_get(x_6, 0);
lean_dec(x_520);
x_521 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_468);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_412);
if (lean_is_scalar(x_7)) {
 x_522 = lean_alloc_ctor(0, 5, 0);
} else {
 x_522 = x_7;
}
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_516);
lean_ctor_set(x_522, 2, x_517);
lean_ctor_set(x_522, 3, x_6);
lean_ctor_set(x_522, 4, x_514);
return x_522;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_523 = lean_ctor_get(x_6, 1);
x_524 = lean_ctor_get(x_6, 2);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_6);
x_525 = lean_unsigned_to_nat(3u);
x_526 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_526, 0, x_412);
lean_ctor_set(x_526, 1, x_3);
lean_ctor_set(x_526, 2, x_4);
lean_ctor_set(x_526, 3, x_468);
lean_ctor_set(x_526, 4, x_468);
if (lean_is_scalar(x_7)) {
 x_527 = lean_alloc_ctor(0, 5, 0);
} else {
 x_527 = x_7;
}
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_523);
lean_ctor_set(x_527, 2, x_524);
lean_ctor_set(x_527, 3, x_526);
lean_ctor_set(x_527, 4, x_514);
return x_527;
}
}
else
{
uint8_t x_528; 
x_528 = !lean_is_exclusive(x_6);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_529 = lean_ctor_get(x_6, 4);
lean_dec(x_529);
x_530 = lean_ctor_get(x_6, 3);
lean_dec(x_530);
lean_ctor_set(x_6, 3, x_514);
x_531 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_532 = lean_alloc_ctor(0, 5, 0);
} else {
 x_532 = x_7;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_3);
lean_ctor_set(x_532, 2, x_4);
lean_ctor_set(x_532, 3, x_514);
lean_ctor_set(x_532, 4, x_6);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_533 = lean_ctor_get(x_6, 0);
x_534 = lean_ctor_get(x_6, 1);
x_535 = lean_ctor_get(x_6, 2);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_6);
x_536 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
lean_ctor_set(x_536, 2, x_535);
lean_ctor_set(x_536, 3, x_514);
lean_ctor_set(x_536, 4, x_514);
x_537 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_538 = lean_alloc_ctor(0, 5, 0);
} else {
 x_538 = x_7;
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_3);
lean_ctor_set(x_538, 2, x_4);
lean_ctor_set(x_538, 3, x_514);
lean_ctor_set(x_538, 4, x_536);
return x_538;
}
}
}
}
else
{
lean_object* x_539; 
if (lean_is_scalar(x_7)) {
 x_539 = lean_alloc_ctor(0, 5, 0);
} else {
 x_539 = x_7;
}
lean_ctor_set(x_539, 0, x_412);
lean_ctor_set(x_539, 1, x_3);
lean_ctor_set(x_539, 2, x_4);
lean_ctor_set(x_539, 3, x_6);
lean_ctor_set(x_539, 4, x_6);
return x_539;
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_unbox_uint64(x_3);
x_8 = lean_uint64_dec_lt(x_2, x_7);
if (x_8 == 0)
{
uint64_t x_9; uint8_t x_10; 
x_9 = lean_unbox_uint64(x_3);
x_10 = lean_uint64_dec_eq(x_2, x_9);
if (x_10 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_inc(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
else
{
x_1 = x_5;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(x_5, x_2);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_size(x_9);
x_11 = 0;
lean_inc(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(x_3, x_9, x_10, x_11, x_1);
lean_dec(x_9);
x_13 = l_Std_CancellationToken_cancel(x_8, x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_2, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
lean_inc(x_17);
lean_dec(x_12);
x_19 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_2, x_17);
x_20 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint64(x_20, sizeof(void*)*1, x_18);
return x_20;
}
}
else
{
lean_dec(x_6);
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(x_5, x_9, x_1);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(x_5, x_1, x_2);
x_7 = lean_st_ref_set(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = l_Std_CancellationContext_cancel___lam__0(x_5, x_2, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_7 = l_Std_CancellationToken_isCancelled(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box_uint64(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_CancellationContext_cancel___lam__0___boxed), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_CancellationContext_cancel(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationContext_isCancelled(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Std_CancellationToken_isCancelled(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_isCancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_CancellationContext_isCancelled(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Std_CancellationToken_getCancellationReason(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_CancellationContext_getCancellationReason(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Std_CancellationToken_wait(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_CancellationContext_done(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Std_CancellationToken_selector(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(x_1, x_7, x_14, x_15, x_8);
lean_dec(x_7);
x_17 = lean_nat_add(x_12, x_16);
lean_dec(x_16);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_9);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(x_1, x_7, x_18, x_19, x_8);
lean_dec(x_7);
x_21 = lean_nat_add(x_12, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(x_1, x_8);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_st_ref_get(x_2);
x_5 = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_CancellationContext_countAliveTokens___lam__0(x_4, x_2);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object* x_1) {
_start:
{
lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_5 = lean_box_uint64(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_CancellationContext_countAliveTokens___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_CancellationContext_countAliveTokens(x_1);
return x_3;
}
}
lean_object* initialize_Std_Data(uint8_t builtin);
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_CancellationContext_new___closed__0 = _init_l_Std_CancellationContext_new___closed__0();
lean_mark_persistent(l_Std_CancellationContext_new___closed__0);
l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
