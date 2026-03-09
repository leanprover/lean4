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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_CancellationContext_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_CancellationContext_new___closed__0 = (const lean_object*)&l_Std_CancellationContext_new___closed__0_value;
lean_object* l_Std_CancellationToken_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_new();
LEAN_EXPORT lean_object* l_Std_CancellationContext_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t, uint64_t, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_fork___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(uint64_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(lean_object*, uint64_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_getCancellationReason___boxed(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_done___boxed(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_doneSelector(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(lean_object*, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationContext_countAliveTokens___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_292; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_292 = !lean_is_exclusive(x_3);
if (x_292 == 0)
{
x_9 = x_3;
x_10 = x_292;
goto block_291;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_292;
goto block_291;
}
block_291:
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_5);
x_12 = lean_uint64_dec_lt(x_1, x_11);
if (x_12 == 0)
{
uint64_t x_13; uint8_t x_14; 
x_13 = lean_unbox_uint64(x_5);
x_14 = lean_uint64_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_1, x_2, x_8);
x_16 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_mul(x_23, x_17);
x_25 = lean_nat_dec_lt(x_24, x_18);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_nat_add(x_16, x_17);
x_27 = lean_nat_add(x_26, x_18);
lean_dec(x_18);
lean_dec(x_26);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_15);
lean_ctor_set(x_9, 0, x_27);
x_28 = x_9;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_6);
lean_ctor_set(x_30, 3, x_7);
lean_ctor_set(x_30, 4, x_15);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_94; 
x_94 = !lean_is_exclusive(x_15);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_15, 4);
lean_dec(x_95);
x_96 = lean_ctor_get(x_15, 3);
lean_dec(x_96);
x_97 = lean_ctor_get(x_15, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_15, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_15, 0);
lean_dec(x_99);
x_31 = x_15;
x_32 = x_94;
goto block_93;
}
else
{
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_mul(x_39, x_38);
x_41 = lean_nat_dec_lt(x_33, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; uint8_t x_69; 
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_21, 4);
lean_dec(x_70);
x_71 = lean_ctor_get(x_21, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_21, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_21, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_21, 0);
lean_dec(x_74);
x_42 = x_21;
x_43 = x_69;
goto block_68;
}
else
{
lean_dec(x_21);
x_42 = lean_box(0);
x_43 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_57; 
x_44 = lean_nat_add(x_16, x_17);
x_45 = lean_nat_add(x_44, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
x_57 = x_66;
goto block_65;
}
else
{
lean_object* x_67; 
x_67 = lean_unsigned_to_nat(0u);
x_57 = x_67;
goto block_65;
}
block_56:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_add(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
if (x_43 == 0)
{
lean_ctor_set(x_42, 4, x_22);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 2, x_20);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 0, x_49);
x_50 = x_42;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_55, 2, x_20);
lean_ctor_set(x_55, 3, x_37);
lean_ctor_set(x_55, 4, x_22);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 4, x_50);
lean_ctor_set(x_31, 3, x_47);
lean_ctor_set(x_31, 2, x_35);
lean_ctor_set(x_31, 1, x_34);
lean_ctor_set(x_31, 0, x_45);
x_51 = x_31;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_34);
lean_ctor_set(x_53, 2, x_35);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
block_65:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_add(x_44, x_57);
lean_dec(x_57);
lean_dec(x_44);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_36);
lean_ctor_set(x_9, 0, x_58);
x_59 = x_9;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_5);
lean_ctor_set(x_64, 2, x_6);
lean_ctor_set(x_64, 3, x_7);
lean_ctor_set(x_64, 4, x_36);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
x_60 = lean_nat_add(x_16, x_38);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_46 = x_60;
x_47 = x_59;
x_48 = x_61;
goto block_56;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_46 = x_60;
x_47 = x_59;
x_48 = x_62;
goto block_56;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_del_object(x_9);
x_75 = lean_nat_add(x_16, x_17);
x_76 = lean_nat_add(x_75, x_18);
lean_dec(x_18);
x_77 = lean_nat_add(x_75, x_33);
lean_dec(x_75);
lean_inc_ref(x_7);
if (x_32 == 0)
{
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set(x_31, 2, x_6);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 0, x_77);
x_78 = x_31;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_77);
lean_ctor_set(x_92, 1, x_5);
lean_ctor_set(x_92, 2, x_6);
lean_ctor_set(x_92, 3, x_7);
lean_ctor_set(x_92, 4, x_21);
x_78 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_85 = !lean_is_exclusive(x_7);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_7, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_7, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_7, 0);
lean_dec(x_90);
x_79 = x_7;
x_80 = x_85;
goto block_84;
}
else
{
lean_dec(x_7);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
lean_ctor_set(x_79, 4, x_22);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 2, x_20);
lean_ctor_set(x_79, 1, x_19);
lean_ctor_set(x_79, 0, x_76);
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_19);
lean_ctor_set(x_83, 2, x_20);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_22);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_15, 3);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_126; 
x_101 = lean_ctor_get(x_15, 4);
x_102 = lean_ctor_get(x_15, 1);
x_103 = lean_ctor_get(x_15, 2);
x_126 = !lean_is_exclusive(x_15);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_15, 3);
lean_dec(x_127);
x_128 = lean_ctor_get(x_15, 0);
lean_dec(x_128);
x_104 = x_15;
x_105 = x_126;
goto block_125;
}
else
{
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_15);
x_104 = lean_box(0);
x_105 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_121; 
x_106 = lean_ctor_get(x_100, 1);
x_107 = lean_ctor_get(x_100, 2);
x_121 = !lean_is_exclusive(x_100);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_100, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_100, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_100, 0);
lean_dec(x_124);
x_108 = x_100;
x_109 = x_121;
goto block_120;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_100);
x_108 = lean_box(0);
x_109 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(3u);
lean_inc_n(x_101, 2);
if (x_109 == 0)
{
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 3, x_101);
lean_ctor_set(x_108, 2, x_6);
lean_ctor_set(x_108, 1, x_5);
lean_ctor_set(x_108, 0, x_16);
x_111 = x_108;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_16);
lean_ctor_set(x_119, 1, x_5);
lean_ctor_set(x_119, 2, x_6);
lean_ctor_set(x_119, 3, x_101);
lean_ctor_set(x_119, 4, x_101);
x_111 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_112; 
lean_inc(x_101);
if (x_105 == 0)
{
lean_ctor_set(x_104, 3, x_101);
lean_ctor_set(x_104, 0, x_16);
x_112 = x_104;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_16);
lean_ctor_set(x_117, 1, x_102);
lean_ctor_set(x_117, 2, x_103);
lean_ctor_set(x_117, 3, x_101);
lean_ctor_set(x_117, 4, x_101);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_112);
lean_ctor_set(x_9, 3, x_111);
lean_ctor_set(x_9, 2, x_107);
lean_ctor_set(x_9, 1, x_106);
lean_ctor_set(x_9, 0, x_110);
x_113 = x_9;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_106);
lean_ctor_set(x_115, 2, x_107);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_15, 4);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_142; 
x_130 = lean_ctor_get(x_15, 1);
x_131 = lean_ctor_get(x_15, 2);
x_142 = !lean_is_exclusive(x_15);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_15, 4);
lean_dec(x_143);
x_144 = lean_ctor_get(x_15, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_15, 0);
lean_dec(x_145);
x_132 = x_15;
x_133 = x_142;
goto block_141;
}
else
{
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_15);
x_132 = lean_box(0);
x_133 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_unsigned_to_nat(3u);
if (x_133 == 0)
{
lean_ctor_set(x_132, 4, x_100);
lean_ctor_set(x_132, 2, x_6);
lean_ctor_set(x_132, 1, x_5);
lean_ctor_set(x_132, 0, x_16);
x_135 = x_132;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_16);
lean_ctor_set(x_140, 1, x_5);
lean_ctor_set(x_140, 2, x_6);
lean_ctor_set(x_140, 3, x_100);
lean_ctor_set(x_140, 4, x_100);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_129);
lean_ctor_set(x_9, 3, x_135);
lean_ctor_set(x_9, 2, x_131);
lean_ctor_set(x_9, 1, x_130);
lean_ctor_set(x_9, 0, x_134);
x_136 = x_9;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_130);
lean_ctor_set(x_138, 2, x_131);
lean_ctor_set(x_138, 3, x_135);
lean_ctor_set(x_138, 4, x_129);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_15);
lean_ctor_set(x_9, 3, x_129);
lean_ctor_set(x_9, 0, x_146);
x_147 = x_9;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_5);
lean_ctor_set(x_149, 2, x_6);
lean_ctor_set(x_149, 3, x_129);
lean_ctor_set(x_149, 4, x_15);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_5);
x_150 = lean_box_uint64(x_1);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_150);
x_151 = x_9;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_4);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_2);
lean_ctor_set(x_153, 3, x_7);
lean_ctor_set(x_153, 4, x_8);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_4);
x_154 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_1, x_2, x_7);
x_155 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_8, 0);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 4);
lean_inc(x_161);
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_nat_mul(x_162, x_156);
x_164 = lean_nat_dec_lt(x_163, x_157);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
x_165 = lean_nat_add(x_155, x_157);
lean_dec(x_157);
x_166 = lean_nat_add(x_165, x_156);
lean_dec(x_165);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_154);
lean_ctor_set(x_9, 0, x_166);
x_167 = x_9;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_5);
lean_ctor_set(x_169, 2, x_6);
lean_ctor_set(x_169, 3, x_154);
lean_ctor_set(x_169, 4, x_8);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
else
{
lean_object* x_170; uint8_t x_171; uint8_t x_235; 
x_235 = !lean_is_exclusive(x_154);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_154, 4);
lean_dec(x_236);
x_237 = lean_ctor_get(x_154, 3);
lean_dec(x_237);
x_238 = lean_ctor_get(x_154, 2);
lean_dec(x_238);
x_239 = lean_ctor_get(x_154, 1);
lean_dec(x_239);
x_240 = lean_ctor_get(x_154, 0);
lean_dec(x_240);
x_170 = x_154;
x_171 = x_235;
goto block_234;
}
else
{
lean_dec(x_154);
x_170 = lean_box(0);
x_171 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_172 = lean_ctor_get(x_160, 0);
x_173 = lean_ctor_get(x_161, 0);
x_174 = lean_ctor_get(x_161, 1);
x_175 = lean_ctor_get(x_161, 2);
x_176 = lean_ctor_get(x_161, 3);
x_177 = lean_ctor_get(x_161, 4);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_mul(x_178, x_172);
x_180 = lean_nat_dec_lt(x_173, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; uint8_t x_209; 
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
x_209 = !lean_is_exclusive(x_161);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_161, 4);
lean_dec(x_210);
x_211 = lean_ctor_get(x_161, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_161, 2);
lean_dec(x_212);
x_213 = lean_ctor_get(x_161, 1);
lean_dec(x_213);
x_214 = lean_ctor_get(x_161, 0);
lean_dec(x_214);
x_181 = x_161;
x_182 = x_209;
goto block_208;
}
else
{
lean_dec(x_161);
x_181 = lean_box(0);
x_182 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_196; lean_object* x_197; 
x_183 = lean_nat_add(x_155, x_157);
lean_dec(x_157);
x_184 = lean_nat_add(x_183, x_156);
lean_dec(x_183);
x_196 = lean_nat_add(x_155, x_172);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_176, 0);
lean_inc(x_206);
x_197 = x_206;
goto block_205;
}
else
{
lean_object* x_207; 
x_207 = lean_unsigned_to_nat(0u);
x_197 = x_207;
goto block_205;
}
block_195:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_nat_add(x_185, x_187);
lean_dec(x_187);
lean_dec(x_185);
if (x_182 == 0)
{
lean_ctor_set(x_181, 4, x_8);
lean_ctor_set(x_181, 3, x_177);
lean_ctor_set(x_181, 2, x_6);
lean_ctor_set(x_181, 1, x_5);
lean_ctor_set(x_181, 0, x_188);
x_189 = x_181;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_194, 1, x_5);
lean_ctor_set(x_194, 2, x_6);
lean_ctor_set(x_194, 3, x_177);
lean_ctor_set(x_194, 4, x_8);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_171 == 0)
{
lean_ctor_set(x_170, 4, x_189);
lean_ctor_set(x_170, 3, x_186);
lean_ctor_set(x_170, 2, x_175);
lean_ctor_set(x_170, 1, x_174);
lean_ctor_set(x_170, 0, x_184);
x_190 = x_170;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_184);
lean_ctor_set(x_192, 1, x_174);
lean_ctor_set(x_192, 2, x_175);
lean_ctor_set(x_192, 3, x_186);
lean_ctor_set(x_192, 4, x_189);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
block_205:
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_nat_add(x_196, x_197);
lean_dec(x_197);
lean_dec(x_196);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_176);
lean_ctor_set(x_9, 3, x_160);
lean_ctor_set(x_9, 2, x_159);
lean_ctor_set(x_9, 1, x_158);
lean_ctor_set(x_9, 0, x_198);
x_199 = x_9;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_158);
lean_ctor_set(x_204, 2, x_159);
lean_ctor_set(x_204, 3, x_160);
lean_ctor_set(x_204, 4, x_176);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
x_200 = lean_nat_add(x_155, x_156);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_177, 0);
lean_inc(x_201);
x_185 = x_200;
x_186 = x_199;
x_187 = x_201;
goto block_195;
}
else
{
lean_object* x_202; 
x_202 = lean_unsigned_to_nat(0u);
x_185 = x_200;
x_186 = x_199;
x_187 = x_202;
goto block_195;
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_del_object(x_9);
x_215 = lean_nat_add(x_155, x_157);
lean_dec(x_157);
x_216 = lean_nat_add(x_215, x_156);
lean_dec(x_215);
x_217 = lean_nat_add(x_155, x_156);
x_218 = lean_nat_add(x_217, x_173);
lean_dec(x_217);
lean_inc_ref(x_8);
if (x_171 == 0)
{
lean_ctor_set(x_170, 4, x_8);
lean_ctor_set(x_170, 3, x_161);
lean_ctor_set(x_170, 2, x_6);
lean_ctor_set(x_170, 1, x_5);
lean_ctor_set(x_170, 0, x_218);
x_219 = x_170;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_218);
lean_ctor_set(x_233, 1, x_5);
lean_ctor_set(x_233, 2, x_6);
lean_ctor_set(x_233, 3, x_161);
lean_ctor_set(x_233, 4, x_8);
x_219 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_220; uint8_t x_221; uint8_t x_226; 
x_226 = !lean_is_exclusive(x_8);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_8, 4);
lean_dec(x_227);
x_228 = lean_ctor_get(x_8, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_8, 2);
lean_dec(x_229);
x_230 = lean_ctor_get(x_8, 1);
lean_dec(x_230);
x_231 = lean_ctor_get(x_8, 0);
lean_dec(x_231);
x_220 = x_8;
x_221 = x_226;
goto block_225;
}
else
{
lean_dec(x_8);
x_220 = lean_box(0);
x_221 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_222; 
if (x_221 == 0)
{
lean_ctor_set(x_220, 4, x_219);
lean_ctor_set(x_220, 3, x_160);
lean_ctor_set(x_220, 2, x_159);
lean_ctor_set(x_220, 1, x_158);
lean_ctor_set(x_220, 0, x_216);
x_222 = x_220;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_224, 0, x_216);
lean_ctor_set(x_224, 1, x_158);
lean_ctor_set(x_224, 2, x_159);
lean_ctor_set(x_224, 3, x_160);
lean_ctor_set(x_224, 4, x_219);
x_222 = x_224;
goto block_223;
}
block_223:
{
return x_222;
}
}
}
}
}
}
}
else
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_154, 3);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_255; 
x_242 = lean_ctor_get(x_154, 4);
x_243 = lean_ctor_get(x_154, 1);
x_244 = lean_ctor_get(x_154, 2);
x_255 = !lean_is_exclusive(x_154);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_154, 3);
lean_dec(x_256);
x_257 = lean_ctor_get(x_154, 0);
lean_dec(x_257);
x_245 = x_154;
x_246 = x_255;
goto block_254;
}
else
{
lean_inc(x_242);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_154);
x_245 = lean_box(0);
x_246 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_unsigned_to_nat(3u);
lean_inc(x_242);
if (x_246 == 0)
{
lean_ctor_set(x_245, 3, x_242);
lean_ctor_set(x_245, 2, x_6);
lean_ctor_set(x_245, 1, x_5);
lean_ctor_set(x_245, 0, x_155);
x_248 = x_245;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_155);
lean_ctor_set(x_253, 1, x_5);
lean_ctor_set(x_253, 2, x_6);
lean_ctor_set(x_253, 3, x_242);
lean_ctor_set(x_253, 4, x_242);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_248);
lean_ctor_set(x_9, 3, x_241);
lean_ctor_set(x_9, 2, x_244);
lean_ctor_set(x_9, 1, x_243);
lean_ctor_set(x_9, 0, x_247);
x_249 = x_9;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_243);
lean_ctor_set(x_251, 2, x_244);
lean_ctor_set(x_251, 3, x_241);
lean_ctor_set(x_251, 4, x_248);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_154, 4);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_283; 
x_259 = lean_ctor_get(x_154, 1);
x_260 = lean_ctor_get(x_154, 2);
x_283 = !lean_is_exclusive(x_154);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_154, 4);
lean_dec(x_284);
x_285 = lean_ctor_get(x_154, 3);
lean_dec(x_285);
x_286 = lean_ctor_get(x_154, 0);
lean_dec(x_286);
x_261 = x_154;
x_262 = x_283;
goto block_282;
}
else
{
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_154);
x_261 = lean_box(0);
x_262 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_278; 
x_263 = lean_ctor_get(x_258, 1);
x_264 = lean_ctor_get(x_258, 2);
x_278 = !lean_is_exclusive(x_258);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_258, 4);
lean_dec(x_279);
x_280 = lean_ctor_get(x_258, 3);
lean_dec(x_280);
x_281 = lean_ctor_get(x_258, 0);
lean_dec(x_281);
x_265 = x_258;
x_266 = x_278;
goto block_277;
}
else
{
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_258);
x_265 = lean_box(0);
x_266 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_unsigned_to_nat(3u);
if (x_266 == 0)
{
lean_ctor_set(x_265, 4, x_241);
lean_ctor_set(x_265, 3, x_241);
lean_ctor_set(x_265, 2, x_260);
lean_ctor_set(x_265, 1, x_259);
lean_ctor_set(x_265, 0, x_155);
x_268 = x_265;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_155);
lean_ctor_set(x_276, 1, x_259);
lean_ctor_set(x_276, 2, x_260);
lean_ctor_set(x_276, 3, x_241);
lean_ctor_set(x_276, 4, x_241);
x_268 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_269; 
if (x_262 == 0)
{
lean_ctor_set(x_261, 4, x_241);
lean_ctor_set(x_261, 2, x_6);
lean_ctor_set(x_261, 1, x_5);
lean_ctor_set(x_261, 0, x_155);
x_269 = x_261;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_274, 0, x_155);
lean_ctor_set(x_274, 1, x_5);
lean_ctor_set(x_274, 2, x_6);
lean_ctor_set(x_274, 3, x_241);
lean_ctor_set(x_274, 4, x_241);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_269);
lean_ctor_set(x_9, 3, x_268);
lean_ctor_set(x_9, 2, x_264);
lean_ctor_set(x_9, 1, x_263);
lean_ctor_set(x_9, 0, x_267);
x_270 = x_9;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_263);
lean_ctor_set(x_272, 2, x_264);
lean_ctor_set(x_272, 3, x_268);
lean_ctor_set(x_272, 4, x_269);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_258);
lean_ctor_set(x_9, 3, x_154);
lean_ctor_set(x_9, 0, x_287);
x_288 = x_9;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_5);
lean_ctor_set(x_290, 2, x_6);
lean_ctor_set(x_290, 3, x_154);
lean_ctor_set(x_290, 4, x_258);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_unsigned_to_nat(1u);
x_294 = lean_box_uint64(x_1);
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set(x_295, 2, x_2);
lean_ctor_set(x_295, 3, x_3);
lean_ctor_set(x_295, 4, x_3);
return x_295;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationContext_new() {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Std_CancellationToken_new();
x_3 = lean_box(1);
x_4 = 0;
x_5 = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(uint64_t x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_32; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
x_9 = x_3;
x_10 = x_32;
goto block_31;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_32;
goto block_31;
}
block_31:
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_5);
x_12 = lean_uint64_dec_lt(x_2, x_11);
if (x_12 == 0)
{
uint64_t x_13; uint8_t x_14; 
x_13 = lean_unbox_uint64(x_5);
x_14 = lean_uint64_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_15);
x_16 = x_9;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_6);
lean_ctor_set(x_18, 3, x_7);
lean_ctor_set(x_18, 4, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_19 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0));
x_20 = lean_box_uint64(x_1);
x_21 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Prod_map___redArg(x_19, x_21, x_6);
x_23 = lean_box_uint64(x_2);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_22);
lean_ctor_set(x_9, 1, x_23);
x_24 = x_9;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_7);
lean_ctor_set(x_26, 4, x_8);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_1, x_2, x_7);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_27);
x_28 = x_9;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_6);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_8);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
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
lean_dec_ref(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_8 = l_Std_CancellationToken_new();
x_9 = lean_st_ref_get(x_5);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_12 = x_9;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; 
x_14 = ((lean_object*)(l_Std_CancellationContext_new___closed__0));
lean_inc_ref(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(x_11, x_15, x_10);
x_17 = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(x_11, x_2, x_16);
x_18 = 1;
x_19 = lean_uint64_add(x_11, x_18);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_17);
x_20 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_24, 0, x_17);
x_20 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
lean_ctor_set_uint64(x_20, sizeof(void*)*1, x_19);
x_21 = lean_st_ref_set(x_5, x_20);
x_22 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_11);
return x_22;
}
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
lean_dec_ref(x_2);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_663; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_663 = !lean_is_exclusive(x_2);
if (x_663 == 0)
{
lean_object* x_664; 
x_664 = lean_ctor_get(x_2, 0);
lean_dec(x_664);
x_7 = x_2;
x_8 = x_663;
goto block_662;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_663;
goto block_662;
}
block_662:
{
uint64_t x_9; uint8_t x_10; 
x_9 = lean_unbox_uint64(x_3);
x_10 = lean_uint64_dec_lt(x_1, x_9);
if (x_10 == 0)
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_3);
x_12 = lean_uint64_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_1, x_6);
x_14 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_5, 4);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_15);
x_23 = lean_nat_dec_lt(x_22, x_16);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_24 = lean_nat_add(x_14, x_16);
x_25 = lean_nat_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_13);
lean_ctor_set(x_7, 0, x_25);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set(x_28, 3, x_5);
lean_ctor_set(x_28, 4, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_94; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_94 = !lean_is_exclusive(x_5);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_5, 4);
lean_dec(x_95);
x_96 = lean_ctor_get(x_5, 3);
lean_dec(x_96);
x_97 = lean_ctor_get(x_5, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_5, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_5, 0);
lean_dec(x_99);
x_29 = x_5;
x_30 = x_94;
goto block_93;
}
else
{
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mul(x_37, x_31);
x_39 = lean_nat_dec_lt(x_32, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_68; 
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_68 = !lean_is_exclusive(x_20);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_20, 4);
lean_dec(x_69);
x_70 = lean_ctor_get(x_20, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_20, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_20, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_20, 0);
lean_dec(x_73);
x_40 = x_20;
x_41 = x_68;
goto block_67;
}
else
{
lean_dec(x_20);
x_40 = lean_box(0);
x_41 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_55; lean_object* x_56; 
x_42 = lean_nat_add(x_14, x_16);
lean_dec(x_16);
x_43 = lean_nat_add(x_42, x_15);
lean_dec(x_42);
x_55 = lean_nat_add(x_14, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_35, 0);
lean_inc(x_65);
x_56 = x_65;
goto block_64;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_56 = x_66;
goto block_64;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_13);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 0, x_47);
x_48 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set(x_53, 3, x_36);
lean_ctor_set(x_53, 4, x_13);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_48);
lean_ctor_set(x_29, 3, x_45);
lean_ctor_set(x_29, 2, x_34);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_43);
x_49 = x_29;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set(x_51, 2, x_34);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_64:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_nat_add(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_35);
lean_ctor_set(x_7, 3, x_19);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_57);
x_58 = x_7;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_17);
lean_ctor_set(x_63, 2, x_18);
lean_ctor_set(x_63, 3, x_19);
lean_ctor_set(x_63, 4, x_35);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
x_59 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_36, 0);
lean_inc(x_60);
x_44 = x_59;
x_45 = x_58;
x_46 = x_60;
goto block_54;
}
else
{
lean_object* x_61; 
x_61 = lean_unsigned_to_nat(0u);
x_44 = x_59;
x_45 = x_58;
x_46 = x_61;
goto block_54;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_del_object(x_7);
x_74 = lean_nat_add(x_14, x_16);
lean_dec(x_16);
x_75 = lean_nat_add(x_74, x_15);
lean_dec(x_74);
x_76 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
x_77 = lean_nat_add(x_76, x_32);
lean_dec(x_76);
lean_inc_ref(x_13);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_13);
lean_ctor_set(x_29, 3, x_20);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_77);
x_78 = x_29;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_77);
lean_ctor_set(x_92, 1, x_3);
lean_ctor_set(x_92, 2, x_4);
lean_ctor_set(x_92, 3, x_20);
lean_ctor_set(x_92, 4, x_13);
x_78 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_85 = !lean_is_exclusive(x_13);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_13, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_13, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_13, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_13, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_13, 0);
lean_dec(x_90);
x_79 = x_13;
x_80 = x_85;
goto block_84;
}
else
{
lean_dec(x_13);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 3, x_19);
lean_ctor_set(x_79, 2, x_18);
lean_ctor_set(x_79, 1, x_17);
lean_ctor_set(x_79, 0, x_75);
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_17);
lean_ctor_set(x_83, 2, x_18);
lean_ctor_set(x_83, 3, x_19);
lean_ctor_set(x_83, 4, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_13, 0);
lean_inc(x_100);
x_101 = lean_nat_add(x_14, x_100);
lean_dec(x_100);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_13);
lean_ctor_set(x_7, 0, x_101);
x_102 = x_7;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_3);
lean_ctor_set(x_104, 2, x_4);
lean_ctor_set(x_104, 3, x_5);
lean_ctor_set(x_104, 4, x_13);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_5, 4);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_122; 
x_107 = lean_ctor_get(x_5, 0);
x_108 = lean_ctor_get(x_5, 1);
x_109 = lean_ctor_get(x_5, 2);
x_122 = !lean_is_exclusive(x_5);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_5, 4);
lean_dec(x_123);
x_124 = lean_ctor_get(x_5, 3);
lean_dec(x_124);
x_110 = x_5;
x_111 = x_122;
goto block_121;
}
else
{
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_5);
x_110 = lean_box(0);
x_111 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_nat_add(x_14, x_107);
lean_dec(x_107);
x_114 = lean_nat_add(x_14, x_112);
if (x_111 == 0)
{
lean_ctor_set(x_110, 4, x_13);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 0, x_114);
x_115 = x_110;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_3);
lean_ctor_set(x_120, 2, x_4);
lean_ctor_set(x_120, 3, x_106);
lean_ctor_set(x_120, 4, x_13);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_115);
lean_ctor_set(x_7, 3, x_105);
lean_ctor_set(x_7, 2, x_109);
lean_ctor_set(x_7, 1, x_108);
lean_ctor_set(x_7, 0, x_113);
x_116 = x_7;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_105);
lean_ctor_set(x_118, 4, x_115);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_137; 
x_125 = lean_ctor_get(x_5, 1);
x_126 = lean_ctor_get(x_5, 2);
x_137 = !lean_is_exclusive(x_5);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_5, 4);
lean_dec(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_5, 0);
lean_dec(x_140);
x_127 = x_5;
x_128 = x_137;
goto block_136;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_5);
x_127 = lean_box(0);
x_128 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_unsigned_to_nat(3u);
if (x_128 == 0)
{
lean_ctor_set(x_127, 3, x_106);
lean_ctor_set(x_127, 2, x_4);
lean_ctor_set(x_127, 1, x_3);
lean_ctor_set(x_127, 0, x_14);
x_130 = x_127;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_14);
lean_ctor_set(x_135, 1, x_3);
lean_ctor_set(x_135, 2, x_4);
lean_ctor_set(x_135, 3, x_106);
lean_ctor_set(x_135, 4, x_106);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_130);
lean_ctor_set(x_7, 3, x_105);
lean_ctor_set(x_7, 2, x_126);
lean_ctor_set(x_7, 1, x_125);
lean_ctor_set(x_7, 0, x_129);
x_131 = x_7;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_105);
lean_ctor_set(x_133, 4, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_5, 4);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_166; 
lean_inc(x_105);
x_142 = lean_ctor_get(x_5, 1);
x_143 = lean_ctor_get(x_5, 2);
x_166 = !lean_is_exclusive(x_5);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_5, 4);
lean_dec(x_167);
x_168 = lean_ctor_get(x_5, 3);
lean_dec(x_168);
x_169 = lean_ctor_get(x_5, 0);
lean_dec(x_169);
x_144 = x_5;
x_145 = x_166;
goto block_165;
}
else
{
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_5);
x_144 = lean_box(0);
x_145 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_161; 
x_146 = lean_ctor_get(x_141, 1);
x_147 = lean_ctor_get(x_141, 2);
x_161 = !lean_is_exclusive(x_141);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_141, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_141, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_141, 0);
lean_dec(x_164);
x_148 = x_141;
x_149 = x_161;
goto block_160;
}
else
{
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_141);
x_148 = lean_box(0);
x_149 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_unsigned_to_nat(3u);
if (x_149 == 0)
{
lean_ctor_set(x_148, 4, x_105);
lean_ctor_set(x_148, 3, x_105);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 1, x_142);
lean_ctor_set(x_148, 0, x_14);
x_151 = x_148;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_14);
lean_ctor_set(x_159, 1, x_142);
lean_ctor_set(x_159, 2, x_143);
lean_ctor_set(x_159, 3, x_105);
lean_ctor_set(x_159, 4, x_105);
x_151 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_152; 
if (x_145 == 0)
{
lean_ctor_set(x_144, 4, x_105);
lean_ctor_set(x_144, 2, x_4);
lean_ctor_set(x_144, 1, x_3);
lean_ctor_set(x_144, 0, x_14);
x_152 = x_144;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_14);
lean_ctor_set(x_157, 1, x_3);
lean_ctor_set(x_157, 2, x_4);
lean_ctor_set(x_157, 3, x_105);
lean_ctor_set(x_157, 4, x_105);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_152);
lean_ctor_set(x_7, 3, x_151);
lean_ctor_set(x_7, 2, x_147);
lean_ctor_set(x_7, 1, x_146);
lean_ctor_set(x_7, 0, x_150);
x_153 = x_7;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_147);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set(x_155, 4, x_152);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_141);
lean_ctor_set(x_7, 0, x_170);
x_171 = x_7;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_3);
lean_ctor_set(x_173, 2, x_4);
lean_ctor_set(x_173, 3, x_5);
lean_ctor_set(x_173, 4, x_141);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
}
else
{
lean_object* x_174; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 0, x_14);
x_174 = x_7;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_14);
lean_ctor_set(x_176, 1, x_3);
lean_ctor_set(x_176, 2, x_4);
lean_ctor_set(x_176, 3, x_5);
lean_ctor_set(x_176, 4, x_5);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
else
{
lean_del_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_177 = lean_ctor_get(x_5, 0);
x_178 = lean_ctor_get(x_5, 1);
x_179 = lean_ctor_get(x_5, 2);
x_180 = lean_ctor_get(x_5, 3);
x_181 = lean_ctor_get(x_5, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_6, 0);
x_183 = lean_ctor_get(x_6, 1);
x_184 = lean_ctor_get(x_6, 2);
x_185 = lean_ctor_get(x_6, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_6, 4);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_dec_lt(x_177, x_182);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; uint8_t x_324; 
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
x_324 = !lean_is_exclusive(x_5);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_5, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_5, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_5, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_5, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_5, 0);
lean_dec(x_329);
x_189 = x_5;
x_190 = x_324;
goto block_323;
}
else
{
lean_dec(x_5);
x_189 = lean_box(0);
x_190 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_178, x_179, x_180, x_181);
x_192 = lean_ctor_get(x_191, 2);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec_ref(x_191);
x_195 = lean_ctor_get(x_192, 0);
x_196 = lean_unsigned_to_nat(3u);
x_197 = lean_nat_mul(x_196, x_195);
x_198 = lean_nat_dec_lt(x_197, x_182);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_185);
x_199 = lean_nat_add(x_187, x_195);
x_200 = lean_nat_add(x_199, x_182);
lean_dec(x_199);
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_6);
lean_ctor_set(x_189, 3, x_192);
lean_ctor_set(x_189, 2, x_194);
lean_ctor_set(x_189, 1, x_193);
lean_ctor_set(x_189, 0, x_200);
x_201 = x_189;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_193);
lean_ctor_set(x_203, 2, x_194);
lean_ctor_set(x_203, 3, x_192);
lean_ctor_set(x_203, 4, x_6);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
else
{
lean_object* x_204; uint8_t x_205; uint8_t x_258; 
lean_inc(x_186);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_258 = !lean_is_exclusive(x_6);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get(x_6, 4);
lean_dec(x_259);
x_260 = lean_ctor_get(x_6, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_6, 2);
lean_dec(x_261);
x_262 = lean_ctor_get(x_6, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_6, 0);
lean_dec(x_263);
x_204 = x_6;
x_205 = x_258;
goto block_257;
}
else
{
lean_dec(x_6);
x_204 = lean_box(0);
x_205 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_206 = lean_ctor_get(x_185, 0);
x_207 = lean_ctor_get(x_185, 1);
x_208 = lean_ctor_get(x_185, 2);
x_209 = lean_ctor_get(x_185, 3);
x_210 = lean_ctor_get(x_185, 4);
x_211 = lean_ctor_get(x_186, 0);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_nat_mul(x_212, x_211);
x_214 = lean_nat_dec_lt(x_206, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; uint8_t x_242; 
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_242 = !lean_is_exclusive(x_185);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_185, 4);
lean_dec(x_243);
x_244 = lean_ctor_get(x_185, 3);
lean_dec(x_244);
x_245 = lean_ctor_get(x_185, 2);
lean_dec(x_245);
x_246 = lean_ctor_get(x_185, 1);
lean_dec(x_246);
x_247 = lean_ctor_get(x_185, 0);
lean_dec(x_247);
x_215 = x_185;
x_216 = x_242;
goto block_241;
}
else
{
lean_dec(x_185);
x_215 = lean_box(0);
x_216 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_230; 
x_217 = lean_nat_add(x_187, x_195);
x_218 = lean_nat_add(x_217, x_182);
lean_dec(x_182);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
x_230 = x_239;
goto block_238;
}
else
{
lean_object* x_240; 
x_240 = lean_unsigned_to_nat(0u);
x_230 = x_240;
goto block_238;
}
block_229:
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_nat_add(x_219, x_221);
lean_dec(x_221);
lean_dec(x_219);
if (x_216 == 0)
{
lean_ctor_set(x_215, 4, x_186);
lean_ctor_set(x_215, 3, x_210);
lean_ctor_set(x_215, 2, x_184);
lean_ctor_set(x_215, 1, x_183);
lean_ctor_set(x_215, 0, x_222);
x_223 = x_215;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_222);
lean_ctor_set(x_228, 1, x_183);
lean_ctor_set(x_228, 2, x_184);
lean_ctor_set(x_228, 3, x_210);
lean_ctor_set(x_228, 4, x_186);
x_223 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_224; 
if (x_205 == 0)
{
lean_ctor_set(x_204, 4, x_223);
lean_ctor_set(x_204, 3, x_220);
lean_ctor_set(x_204, 2, x_208);
lean_ctor_set(x_204, 1, x_207);
lean_ctor_set(x_204, 0, x_218);
x_224 = x_204;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_207);
lean_ctor_set(x_226, 2, x_208);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set(x_226, 4, x_223);
x_224 = x_226;
goto block_225;
}
block_225:
{
return x_224;
}
}
}
block_238:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_nat_add(x_217, x_230);
lean_dec(x_230);
lean_dec(x_217);
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_209);
lean_ctor_set(x_189, 3, x_192);
lean_ctor_set(x_189, 2, x_194);
lean_ctor_set(x_189, 1, x_193);
lean_ctor_set(x_189, 0, x_231);
x_232 = x_189;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_231);
lean_ctor_set(x_237, 1, x_193);
lean_ctor_set(x_237, 2, x_194);
lean_ctor_set(x_237, 3, x_192);
lean_ctor_set(x_237, 4, x_209);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
x_233 = lean_nat_add(x_187, x_211);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_210, 0);
lean_inc(x_234);
x_219 = x_233;
x_220 = x_232;
x_221 = x_234;
goto block_229;
}
else
{
lean_object* x_235; 
x_235 = lean_unsigned_to_nat(0u);
x_219 = x_233;
x_220 = x_232;
x_221 = x_235;
goto block_229;
}
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_nat_add(x_187, x_195);
x_249 = lean_nat_add(x_248, x_182);
lean_dec(x_182);
x_250 = lean_nat_add(x_248, x_206);
lean_dec(x_248);
if (x_205 == 0)
{
lean_ctor_set(x_204, 4, x_185);
lean_ctor_set(x_204, 3, x_192);
lean_ctor_set(x_204, 2, x_194);
lean_ctor_set(x_204, 1, x_193);
lean_ctor_set(x_204, 0, x_250);
x_251 = x_204;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_256, 0, x_250);
lean_ctor_set(x_256, 1, x_193);
lean_ctor_set(x_256, 2, x_194);
lean_ctor_set(x_256, 3, x_192);
lean_ctor_set(x_256, 4, x_185);
x_251 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_252; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_186);
lean_ctor_set(x_189, 3, x_251);
lean_ctor_set(x_189, 2, x_184);
lean_ctor_set(x_189, 1, x_183);
lean_ctor_set(x_189, 0, x_249);
x_252 = x_189;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_249);
lean_ctor_set(x_254, 1, x_183);
lean_ctor_set(x_254, 2, x_184);
lean_ctor_set(x_254, 3, x_251);
lean_ctor_set(x_254, 4, x_186);
x_252 = x_254;
goto block_253;
}
block_253:
{
return x_252;
}
}
}
}
}
}
else
{
lean_object* x_264; uint8_t x_265; uint8_t x_317; 
lean_inc(x_186);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_317 = !lean_is_exclusive(x_6);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_6, 4);
lean_dec(x_318);
x_319 = lean_ctor_get(x_6, 3);
lean_dec(x_319);
x_320 = lean_ctor_get(x_6, 2);
lean_dec(x_320);
x_321 = lean_ctor_get(x_6, 1);
lean_dec(x_321);
x_322 = lean_ctor_get(x_6, 0);
lean_dec(x_322);
x_264 = x_6;
x_265 = x_317;
goto block_316;
}
else
{
lean_dec(x_6);
x_264 = lean_box(0);
x_265 = x_317;
goto block_316;
}
block_316:
{
if (lean_obj_tag(x_185) == 0)
{
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_191, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_191, 1);
lean_inc(x_267);
lean_dec_ref(x_191);
x_268 = lean_ctor_get(x_185, 0);
x_269 = lean_nat_add(x_187, x_182);
lean_dec(x_182);
x_270 = lean_nat_add(x_187, x_268);
if (x_265 == 0)
{
lean_ctor_set(x_264, 4, x_185);
lean_ctor_set(x_264, 3, x_192);
lean_ctor_set(x_264, 2, x_267);
lean_ctor_set(x_264, 1, x_266);
lean_ctor_set(x_264, 0, x_270);
x_271 = x_264;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_266);
lean_ctor_set(x_276, 2, x_267);
lean_ctor_set(x_276, 3, x_192);
lean_ctor_set(x_276, 4, x_185);
x_271 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_272; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_186);
lean_ctor_set(x_189, 3, x_271);
lean_ctor_set(x_189, 2, x_184);
lean_ctor_set(x_189, 1, x_183);
lean_ctor_set(x_189, 0, x_269);
x_272 = x_189;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_183);
lean_ctor_set(x_274, 2, x_184);
lean_ctor_set(x_274, 3, x_271);
lean_ctor_set(x_274, 4, x_186);
x_272 = x_274;
goto block_273;
}
block_273:
{
return x_272;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_294; 
lean_dec(x_182);
x_277 = lean_ctor_get(x_191, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_191, 1);
lean_inc(x_278);
lean_dec_ref(x_191);
x_279 = lean_ctor_get(x_185, 1);
x_280 = lean_ctor_get(x_185, 2);
x_294 = !lean_is_exclusive(x_185);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_185, 4);
lean_dec(x_295);
x_296 = lean_ctor_get(x_185, 3);
lean_dec(x_296);
x_297 = lean_ctor_get(x_185, 0);
lean_dec(x_297);
x_281 = x_185;
x_282 = x_294;
goto block_293;
}
else
{
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_185);
x_281 = lean_box(0);
x_282 = x_294;
goto block_293;
}
block_293:
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_unsigned_to_nat(3u);
if (x_282 == 0)
{
lean_ctor_set(x_281, 4, x_186);
lean_ctor_set(x_281, 3, x_186);
lean_ctor_set(x_281, 2, x_278);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set(x_281, 0, x_187);
x_284 = x_281;
goto block_291;
}
else
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_292, 0, x_187);
lean_ctor_set(x_292, 1, x_277);
lean_ctor_set(x_292, 2, x_278);
lean_ctor_set(x_292, 3, x_186);
lean_ctor_set(x_292, 4, x_186);
x_284 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_285; 
if (x_265 == 0)
{
lean_ctor_set(x_264, 3, x_186);
lean_ctor_set(x_264, 0, x_187);
x_285 = x_264;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_290, 0, x_187);
lean_ctor_set(x_290, 1, x_183);
lean_ctor_set(x_290, 2, x_184);
lean_ctor_set(x_290, 3, x_186);
lean_ctor_set(x_290, 4, x_186);
x_285 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_286; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_285);
lean_ctor_set(x_189, 3, x_284);
lean_ctor_set(x_189, 2, x_280);
lean_ctor_set(x_189, 1, x_279);
lean_ctor_set(x_189, 0, x_283);
x_286 = x_189;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_283);
lean_ctor_set(x_288, 1, x_279);
lean_ctor_set(x_288, 2, x_280);
lean_ctor_set(x_288, 3, x_284);
lean_ctor_set(x_288, 4, x_285);
x_286 = x_288;
goto block_287;
}
block_287:
{
return x_286;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_182);
x_298 = lean_ctor_get(x_191, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_191, 1);
lean_inc(x_299);
lean_dec_ref(x_191);
x_300 = lean_unsigned_to_nat(3u);
if (x_265 == 0)
{
lean_ctor_set(x_264, 4, x_185);
lean_ctor_set(x_264, 2, x_299);
lean_ctor_set(x_264, 1, x_298);
lean_ctor_set(x_264, 0, x_187);
x_301 = x_264;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_306, 0, x_187);
lean_ctor_set(x_306, 1, x_298);
lean_ctor_set(x_306, 2, x_299);
lean_ctor_set(x_306, 3, x_185);
lean_ctor_set(x_306, 4, x_185);
x_301 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_302; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_186);
lean_ctor_set(x_189, 3, x_301);
lean_ctor_set(x_189, 2, x_184);
lean_ctor_set(x_189, 1, x_183);
lean_ctor_set(x_189, 0, x_300);
x_302 = x_189;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_183);
lean_ctor_set(x_304, 2, x_184);
lean_ctor_set(x_304, 3, x_301);
lean_ctor_set(x_304, 4, x_186);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_191, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_191, 1);
lean_inc(x_308);
lean_dec_ref(x_191);
if (x_265 == 0)
{
lean_ctor_set(x_264, 3, x_186);
x_309 = x_264;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_182);
lean_ctor_set(x_315, 1, x_183);
lean_ctor_set(x_315, 2, x_184);
lean_ctor_set(x_315, 3, x_186);
lean_ctor_set(x_315, 4, x_186);
x_309 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_unsigned_to_nat(2u);
if (x_190 == 0)
{
lean_ctor_set(x_189, 4, x_309);
lean_ctor_set(x_189, 3, x_186);
lean_ctor_set(x_189, 2, x_308);
lean_ctor_set(x_189, 1, x_307);
lean_ctor_set(x_189, 0, x_310);
x_311 = x_189;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_307);
lean_ctor_set(x_313, 2, x_308);
lean_ctor_set(x_313, 3, x_186);
lean_ctor_set(x_313, 4, x_309);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
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
lean_object* x_330; uint8_t x_331; uint8_t x_482; 
lean_inc(x_186);
lean_inc(x_184);
lean_inc(x_183);
x_482 = !lean_is_exclusive(x_6);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_483 = lean_ctor_get(x_6, 4);
lean_dec(x_483);
x_484 = lean_ctor_get(x_6, 3);
lean_dec(x_484);
x_485 = lean_ctor_get(x_6, 2);
lean_dec(x_485);
x_486 = lean_ctor_get(x_6, 1);
lean_dec(x_486);
x_487 = lean_ctor_get(x_6, 0);
lean_dec(x_487);
x_330 = x_6;
x_331 = x_482;
goto block_481;
}
else
{
lean_dec(x_6);
x_330 = lean_box(0);
x_331 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_332; lean_object* x_333; 
x_332 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_183, x_184, x_185, x_186);
x_333 = lean_ctor_get(x_332, 2);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec_ref(x_332);
x_336 = lean_ctor_get(x_333, 0);
x_337 = lean_unsigned_to_nat(3u);
x_338 = lean_nat_mul(x_337, x_336);
x_339 = lean_nat_dec_lt(x_338, x_177);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_181);
x_340 = lean_nat_add(x_187, x_177);
x_341 = lean_nat_add(x_340, x_336);
lean_dec(x_340);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_333);
lean_ctor_set(x_330, 3, x_5);
lean_ctor_set(x_330, 2, x_335);
lean_ctor_set(x_330, 1, x_334);
lean_ctor_set(x_330, 0, x_341);
x_342 = x_330;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_334);
lean_ctor_set(x_344, 2, x_335);
lean_ctor_set(x_344, 3, x_5);
lean_ctor_set(x_344, 4, x_333);
x_342 = x_344;
goto block_343;
}
block_343:
{
return x_342;
}
}
else
{
lean_object* x_345; uint8_t x_346; uint8_t x_410; 
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
x_410 = !lean_is_exclusive(x_5);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_411 = lean_ctor_get(x_5, 4);
lean_dec(x_411);
x_412 = lean_ctor_get(x_5, 3);
lean_dec(x_412);
x_413 = lean_ctor_get(x_5, 2);
lean_dec(x_413);
x_414 = lean_ctor_get(x_5, 1);
lean_dec(x_414);
x_415 = lean_ctor_get(x_5, 0);
lean_dec(x_415);
x_345 = x_5;
x_346 = x_410;
goto block_409;
}
else
{
lean_dec(x_5);
x_345 = lean_box(0);
x_346 = x_410;
goto block_409;
}
block_409:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_347 = lean_ctor_get(x_180, 0);
x_348 = lean_ctor_get(x_181, 0);
x_349 = lean_ctor_get(x_181, 1);
x_350 = lean_ctor_get(x_181, 2);
x_351 = lean_ctor_get(x_181, 3);
x_352 = lean_ctor_get(x_181, 4);
x_353 = lean_unsigned_to_nat(2u);
x_354 = lean_nat_mul(x_353, x_347);
x_355 = lean_nat_dec_lt(x_348, x_354);
lean_dec(x_354);
if (x_355 == 0)
{
lean_object* x_356; uint8_t x_357; uint8_t x_393; 
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_del_object(x_345);
x_393 = !lean_is_exclusive(x_181);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_181, 4);
lean_dec(x_394);
x_395 = lean_ctor_get(x_181, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_181, 2);
lean_dec(x_396);
x_397 = lean_ctor_get(x_181, 1);
lean_dec(x_397);
x_398 = lean_ctor_get(x_181, 0);
lean_dec(x_398);
x_356 = x_181;
x_357 = x_393;
goto block_392;
}
else
{
lean_dec(x_181);
x_356 = lean_box(0);
x_357 = x_393;
goto block_392;
}
block_392:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_380; lean_object* x_381; 
x_358 = lean_nat_add(x_187, x_177);
lean_dec(x_177);
x_359 = lean_nat_add(x_358, x_336);
lean_dec(x_358);
x_380 = lean_nat_add(x_187, x_347);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_351, 0);
lean_inc(x_390);
x_381 = x_390;
goto block_389;
}
else
{
lean_object* x_391; 
x_391 = lean_unsigned_to_nat(0u);
x_381 = x_391;
goto block_389;
}
block_379:
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_nat_add(x_361, x_362);
lean_dec(x_362);
lean_dec(x_361);
lean_inc_ref(x_333);
if (x_357 == 0)
{
lean_ctor_set(x_356, 4, x_333);
lean_ctor_set(x_356, 3, x_352);
lean_ctor_set(x_356, 2, x_335);
lean_ctor_set(x_356, 1, x_334);
lean_ctor_set(x_356, 0, x_363);
x_364 = x_356;
goto block_377;
}
else
{
lean_object* x_378; 
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_363);
lean_ctor_set(x_378, 1, x_334);
lean_ctor_set(x_378, 2, x_335);
lean_ctor_set(x_378, 3, x_352);
lean_ctor_set(x_378, 4, x_333);
x_364 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_365; uint8_t x_366; uint8_t x_371; 
x_371 = !lean_is_exclusive(x_333);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = lean_ctor_get(x_333, 4);
lean_dec(x_372);
x_373 = lean_ctor_get(x_333, 3);
lean_dec(x_373);
x_374 = lean_ctor_get(x_333, 2);
lean_dec(x_374);
x_375 = lean_ctor_get(x_333, 1);
lean_dec(x_375);
x_376 = lean_ctor_get(x_333, 0);
lean_dec(x_376);
x_365 = x_333;
x_366 = x_371;
goto block_370;
}
else
{
lean_dec(x_333);
x_365 = lean_box(0);
x_366 = x_371;
goto block_370;
}
block_370:
{
lean_object* x_367; 
if (x_366 == 0)
{
lean_ctor_set(x_365, 4, x_364);
lean_ctor_set(x_365, 3, x_360);
lean_ctor_set(x_365, 2, x_350);
lean_ctor_set(x_365, 1, x_349);
lean_ctor_set(x_365, 0, x_359);
x_367 = x_365;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_369, 0, x_359);
lean_ctor_set(x_369, 1, x_349);
lean_ctor_set(x_369, 2, x_350);
lean_ctor_set(x_369, 3, x_360);
lean_ctor_set(x_369, 4, x_364);
x_367 = x_369;
goto block_368;
}
block_368:
{
return x_367;
}
}
}
}
block_389:
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_nat_add(x_380, x_381);
lean_dec(x_381);
lean_dec(x_380);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_351);
lean_ctor_set(x_330, 3, x_180);
lean_ctor_set(x_330, 2, x_179);
lean_ctor_set(x_330, 1, x_178);
lean_ctor_set(x_330, 0, x_382);
x_383 = x_330;
goto block_387;
}
else
{
lean_object* x_388; 
x_388 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_388, 0, x_382);
lean_ctor_set(x_388, 1, x_178);
lean_ctor_set(x_388, 2, x_179);
lean_ctor_set(x_388, 3, x_180);
lean_ctor_set(x_388, 4, x_351);
x_383 = x_388;
goto block_387;
}
block_387:
{
lean_object* x_384; 
x_384 = lean_nat_add(x_187, x_336);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_352, 0);
lean_inc(x_385);
x_360 = x_383;
x_361 = x_384;
x_362 = x_385;
goto block_379;
}
else
{
lean_object* x_386; 
x_386 = lean_unsigned_to_nat(0u);
x_360 = x_383;
x_361 = x_384;
x_362 = x_386;
goto block_379;
}
}
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = lean_nat_add(x_187, x_177);
lean_dec(x_177);
x_400 = lean_nat_add(x_399, x_336);
lean_dec(x_399);
x_401 = lean_nat_add(x_187, x_336);
x_402 = lean_nat_add(x_401, x_348);
lean_dec(x_401);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_333);
lean_ctor_set(x_330, 3, x_181);
lean_ctor_set(x_330, 2, x_335);
lean_ctor_set(x_330, 1, x_334);
lean_ctor_set(x_330, 0, x_402);
x_403 = x_330;
goto block_407;
}
else
{
lean_object* x_408; 
x_408 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_408, 0, x_402);
lean_ctor_set(x_408, 1, x_334);
lean_ctor_set(x_408, 2, x_335);
lean_ctor_set(x_408, 3, x_181);
lean_ctor_set(x_408, 4, x_333);
x_403 = x_408;
goto block_407;
}
block_407:
{
lean_object* x_404; 
if (x_346 == 0)
{
lean_ctor_set(x_345, 4, x_403);
lean_ctor_set(x_345, 0, x_400);
x_404 = x_345;
goto block_405;
}
else
{
lean_object* x_406; 
x_406 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_406, 0, x_400);
lean_ctor_set(x_406, 1, x_178);
lean_ctor_set(x_406, 2, x_179);
lean_ctor_set(x_406, 3, x_180);
lean_ctor_set(x_406, 4, x_403);
x_404 = x_406;
goto block_405;
}
block_405:
{
return x_404;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_416; uint8_t x_417; uint8_t x_439; 
lean_inc_ref(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
x_439 = !lean_is_exclusive(x_5);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_440 = lean_ctor_get(x_5, 4);
lean_dec(x_440);
x_441 = lean_ctor_get(x_5, 3);
lean_dec(x_441);
x_442 = lean_ctor_get(x_5, 2);
lean_dec(x_442);
x_443 = lean_ctor_get(x_5, 1);
lean_dec(x_443);
x_444 = lean_ctor_get(x_5, 0);
lean_dec(x_444);
x_416 = x_5;
x_417 = x_439;
goto block_438;
}
else
{
lean_dec(x_5);
x_416 = lean_box(0);
x_417 = x_439;
goto block_438;
}
block_438:
{
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_418 = lean_ctor_get(x_332, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_332, 1);
lean_inc(x_419);
lean_dec_ref(x_332);
x_420 = lean_ctor_get(x_181, 0);
x_421 = lean_nat_add(x_187, x_177);
lean_dec(x_177);
x_422 = lean_nat_add(x_187, x_420);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_333);
lean_ctor_set(x_330, 3, x_181);
lean_ctor_set(x_330, 2, x_419);
lean_ctor_set(x_330, 1, x_418);
lean_ctor_set(x_330, 0, x_422);
x_423 = x_330;
goto block_427;
}
else
{
lean_object* x_428; 
x_428 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_428, 0, x_422);
lean_ctor_set(x_428, 1, x_418);
lean_ctor_set(x_428, 2, x_419);
lean_ctor_set(x_428, 3, x_181);
lean_ctor_set(x_428, 4, x_333);
x_423 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_424; 
if (x_417 == 0)
{
lean_ctor_set(x_416, 4, x_423);
lean_ctor_set(x_416, 0, x_421);
x_424 = x_416;
goto block_425;
}
else
{
lean_object* x_426; 
x_426 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_178);
lean_ctor_set(x_426, 2, x_179);
lean_ctor_set(x_426, 3, x_180);
lean_ctor_set(x_426, 4, x_423);
x_424 = x_426;
goto block_425;
}
block_425:
{
return x_424;
}
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_177);
x_429 = lean_ctor_get(x_332, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_332, 1);
lean_inc(x_430);
lean_dec_ref(x_332);
x_431 = lean_unsigned_to_nat(3u);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_181);
lean_ctor_set(x_330, 3, x_181);
lean_ctor_set(x_330, 2, x_430);
lean_ctor_set(x_330, 1, x_429);
lean_ctor_set(x_330, 0, x_187);
x_432 = x_330;
goto block_436;
}
else
{
lean_object* x_437; 
x_437 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_437, 0, x_187);
lean_ctor_set(x_437, 1, x_429);
lean_ctor_set(x_437, 2, x_430);
lean_ctor_set(x_437, 3, x_181);
lean_ctor_set(x_437, 4, x_181);
x_432 = x_437;
goto block_436;
}
block_436:
{
lean_object* x_433; 
if (x_417 == 0)
{
lean_ctor_set(x_416, 4, x_432);
lean_ctor_set(x_416, 0, x_431);
x_433 = x_416;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_178);
lean_ctor_set(x_435, 2, x_179);
lean_ctor_set(x_435, 3, x_180);
lean_ctor_set(x_435, 4, x_432);
x_433 = x_435;
goto block_434;
}
block_434:
{
return x_433;
}
}
}
}
}
else
{
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_445; uint8_t x_446; uint8_t x_469; 
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
x_469 = !lean_is_exclusive(x_5);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_470 = lean_ctor_get(x_5, 4);
lean_dec(x_470);
x_471 = lean_ctor_get(x_5, 3);
lean_dec(x_471);
x_472 = lean_ctor_get(x_5, 2);
lean_dec(x_472);
x_473 = lean_ctor_get(x_5, 1);
lean_dec(x_473);
x_474 = lean_ctor_get(x_5, 0);
lean_dec(x_474);
x_445 = x_5;
x_446 = x_469;
goto block_468;
}
else
{
lean_dec(x_5);
x_445 = lean_box(0);
x_446 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; uint8_t x_464; 
x_447 = lean_ctor_get(x_332, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_332, 1);
lean_inc(x_448);
lean_dec_ref(x_332);
x_449 = lean_ctor_get(x_181, 1);
x_450 = lean_ctor_get(x_181, 2);
x_464 = !lean_is_exclusive(x_181);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_181, 4);
lean_dec(x_465);
x_466 = lean_ctor_get(x_181, 3);
lean_dec(x_466);
x_467 = lean_ctor_get(x_181, 0);
lean_dec(x_467);
x_451 = x_181;
x_452 = x_464;
goto block_463;
}
else
{
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_181);
x_451 = lean_box(0);
x_452 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_453; lean_object* x_454; 
x_453 = lean_unsigned_to_nat(3u);
if (x_452 == 0)
{
lean_ctor_set(x_451, 4, x_180);
lean_ctor_set(x_451, 3, x_180);
lean_ctor_set(x_451, 2, x_179);
lean_ctor_set(x_451, 1, x_178);
lean_ctor_set(x_451, 0, x_187);
x_454 = x_451;
goto block_461;
}
else
{
lean_object* x_462; 
x_462 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_462, 0, x_187);
lean_ctor_set(x_462, 1, x_178);
lean_ctor_set(x_462, 2, x_179);
lean_ctor_set(x_462, 3, x_180);
lean_ctor_set(x_462, 4, x_180);
x_454 = x_462;
goto block_461;
}
block_461:
{
lean_object* x_455; 
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_180);
lean_ctor_set(x_330, 3, x_180);
lean_ctor_set(x_330, 2, x_448);
lean_ctor_set(x_330, 1, x_447);
lean_ctor_set(x_330, 0, x_187);
x_455 = x_330;
goto block_459;
}
else
{
lean_object* x_460; 
x_460 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_460, 0, x_187);
lean_ctor_set(x_460, 1, x_447);
lean_ctor_set(x_460, 2, x_448);
lean_ctor_set(x_460, 3, x_180);
lean_ctor_set(x_460, 4, x_180);
x_455 = x_460;
goto block_459;
}
block_459:
{
lean_object* x_456; 
if (x_446 == 0)
{
lean_ctor_set(x_445, 4, x_455);
lean_ctor_set(x_445, 3, x_454);
lean_ctor_set(x_445, 2, x_450);
lean_ctor_set(x_445, 1, x_449);
lean_ctor_set(x_445, 0, x_453);
x_456 = x_445;
goto block_457;
}
else
{
lean_object* x_458; 
x_458 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_458, 0, x_453);
lean_ctor_set(x_458, 1, x_449);
lean_ctor_set(x_458, 2, x_450);
lean_ctor_set(x_458, 3, x_454);
lean_ctor_set(x_458, 4, x_455);
x_456 = x_458;
goto block_457;
}
block_457:
{
return x_456;
}
}
}
}
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_475 = lean_ctor_get(x_332, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_332, 1);
lean_inc(x_476);
lean_dec_ref(x_332);
x_477 = lean_unsigned_to_nat(2u);
if (x_331 == 0)
{
lean_ctor_set(x_330, 4, x_181);
lean_ctor_set(x_330, 3, x_5);
lean_ctor_set(x_330, 2, x_476);
lean_ctor_set(x_330, 1, x_475);
lean_ctor_set(x_330, 0, x_477);
x_478 = x_330;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_475);
lean_ctor_set(x_480, 2, x_476);
lean_ctor_set(x_480, 3, x_5);
lean_ctor_set(x_480, 4, x_181);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
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
lean_object* x_488; lean_object* x_489; 
x_488 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_1, x_5);
x_489 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_488) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
x_490 = lean_ctor_get(x_488, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_6, 0);
x_492 = lean_ctor_get(x_6, 1);
x_493 = lean_ctor_get(x_6, 2);
x_494 = lean_ctor_get(x_6, 3);
lean_inc(x_494);
x_495 = lean_ctor_get(x_6, 4);
x_496 = lean_unsigned_to_nat(3u);
x_497 = lean_nat_mul(x_496, x_490);
x_498 = lean_nat_dec_lt(x_497, x_491);
lean_dec(x_497);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_494);
x_499 = lean_nat_add(x_489, x_490);
lean_dec(x_490);
x_500 = lean_nat_add(x_499, x_491);
lean_dec(x_499);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_488);
lean_ctor_set(x_7, 0, x_500);
x_501 = x_7;
goto block_502;
}
else
{
lean_object* x_503; 
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_3);
lean_ctor_set(x_503, 2, x_4);
lean_ctor_set(x_503, 3, x_488);
lean_ctor_set(x_503, 4, x_6);
x_501 = x_503;
goto block_502;
}
block_502:
{
return x_501;
}
}
else
{
lean_object* x_504; uint8_t x_505; uint8_t x_567; 
lean_inc(x_495);
lean_inc(x_493);
lean_inc(x_492);
lean_inc(x_491);
x_567 = !lean_is_exclusive(x_6);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_6, 4);
lean_dec(x_568);
x_569 = lean_ctor_get(x_6, 3);
lean_dec(x_569);
x_570 = lean_ctor_get(x_6, 2);
lean_dec(x_570);
x_571 = lean_ctor_get(x_6, 1);
lean_dec(x_571);
x_572 = lean_ctor_get(x_6, 0);
lean_dec(x_572);
x_504 = x_6;
x_505 = x_567;
goto block_566;
}
else
{
lean_dec(x_6);
x_504 = lean_box(0);
x_505 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_506 = lean_ctor_get(x_494, 0);
x_507 = lean_ctor_get(x_494, 1);
x_508 = lean_ctor_get(x_494, 2);
x_509 = lean_ctor_get(x_494, 3);
x_510 = lean_ctor_get(x_494, 4);
x_511 = lean_ctor_get(x_495, 0);
x_512 = lean_unsigned_to_nat(2u);
x_513 = lean_nat_mul(x_512, x_511);
x_514 = lean_nat_dec_lt(x_506, x_513);
lean_dec(x_513);
if (x_514 == 0)
{
lean_object* x_515; uint8_t x_516; uint8_t x_542; 
lean_inc(x_510);
lean_inc(x_509);
lean_inc(x_508);
lean_inc(x_507);
x_542 = !lean_is_exclusive(x_494);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_543 = lean_ctor_get(x_494, 4);
lean_dec(x_543);
x_544 = lean_ctor_get(x_494, 3);
lean_dec(x_544);
x_545 = lean_ctor_get(x_494, 2);
lean_dec(x_545);
x_546 = lean_ctor_get(x_494, 1);
lean_dec(x_546);
x_547 = lean_ctor_get(x_494, 0);
lean_dec(x_547);
x_515 = x_494;
x_516 = x_542;
goto block_541;
}
else
{
lean_dec(x_494);
x_515 = lean_box(0);
x_516 = x_542;
goto block_541;
}
block_541:
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_530; 
x_517 = lean_nat_add(x_489, x_490);
lean_dec(x_490);
x_518 = lean_nat_add(x_517, x_491);
lean_dec(x_491);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_539; 
x_539 = lean_ctor_get(x_509, 0);
lean_inc(x_539);
x_530 = x_539;
goto block_538;
}
else
{
lean_object* x_540; 
x_540 = lean_unsigned_to_nat(0u);
x_530 = x_540;
goto block_538;
}
block_529:
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_nat_add(x_519, x_521);
lean_dec(x_521);
lean_dec(x_519);
if (x_516 == 0)
{
lean_ctor_set(x_515, 4, x_495);
lean_ctor_set(x_515, 3, x_510);
lean_ctor_set(x_515, 2, x_493);
lean_ctor_set(x_515, 1, x_492);
lean_ctor_set(x_515, 0, x_522);
x_523 = x_515;
goto block_527;
}
else
{
lean_object* x_528; 
x_528 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_528, 0, x_522);
lean_ctor_set(x_528, 1, x_492);
lean_ctor_set(x_528, 2, x_493);
lean_ctor_set(x_528, 3, x_510);
lean_ctor_set(x_528, 4, x_495);
x_523 = x_528;
goto block_527;
}
block_527:
{
lean_object* x_524; 
if (x_505 == 0)
{
lean_ctor_set(x_504, 4, x_523);
lean_ctor_set(x_504, 3, x_520);
lean_ctor_set(x_504, 2, x_508);
lean_ctor_set(x_504, 1, x_507);
lean_ctor_set(x_504, 0, x_518);
x_524 = x_504;
goto block_525;
}
else
{
lean_object* x_526; 
x_526 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_526, 0, x_518);
lean_ctor_set(x_526, 1, x_507);
lean_ctor_set(x_526, 2, x_508);
lean_ctor_set(x_526, 3, x_520);
lean_ctor_set(x_526, 4, x_523);
x_524 = x_526;
goto block_525;
}
block_525:
{
return x_524;
}
}
}
block_538:
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_nat_add(x_517, x_530);
lean_dec(x_530);
lean_dec(x_517);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_509);
lean_ctor_set(x_7, 3, x_488);
lean_ctor_set(x_7, 0, x_531);
x_532 = x_7;
goto block_536;
}
else
{
lean_object* x_537; 
x_537 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_537, 0, x_531);
lean_ctor_set(x_537, 1, x_3);
lean_ctor_set(x_537, 2, x_4);
lean_ctor_set(x_537, 3, x_488);
lean_ctor_set(x_537, 4, x_509);
x_532 = x_537;
goto block_536;
}
block_536:
{
lean_object* x_533; 
x_533 = lean_nat_add(x_489, x_511);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_534; 
x_534 = lean_ctor_get(x_510, 0);
lean_inc(x_534);
x_519 = x_533;
x_520 = x_532;
x_521 = x_534;
goto block_529;
}
else
{
lean_object* x_535; 
x_535 = lean_unsigned_to_nat(0u);
x_519 = x_533;
x_520 = x_532;
x_521 = x_535;
goto block_529;
}
}
}
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_del_object(x_7);
x_548 = lean_nat_add(x_489, x_490);
lean_dec(x_490);
x_549 = lean_nat_add(x_548, x_491);
lean_dec(x_491);
x_550 = lean_nat_add(x_548, x_506);
lean_dec(x_548);
lean_inc_ref(x_488);
if (x_505 == 0)
{
lean_ctor_set(x_504, 4, x_494);
lean_ctor_set(x_504, 3, x_488);
lean_ctor_set(x_504, 2, x_4);
lean_ctor_set(x_504, 1, x_3);
lean_ctor_set(x_504, 0, x_550);
x_551 = x_504;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_565, 0, x_550);
lean_ctor_set(x_565, 1, x_3);
lean_ctor_set(x_565, 2, x_4);
lean_ctor_set(x_565, 3, x_488);
lean_ctor_set(x_565, 4, x_494);
x_551 = x_565;
goto block_564;
}
block_564:
{
lean_object* x_552; uint8_t x_553; uint8_t x_558; 
x_558 = !lean_is_exclusive(x_488);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_559 = lean_ctor_get(x_488, 4);
lean_dec(x_559);
x_560 = lean_ctor_get(x_488, 3);
lean_dec(x_560);
x_561 = lean_ctor_get(x_488, 2);
lean_dec(x_561);
x_562 = lean_ctor_get(x_488, 1);
lean_dec(x_562);
x_563 = lean_ctor_get(x_488, 0);
lean_dec(x_563);
x_552 = x_488;
x_553 = x_558;
goto block_557;
}
else
{
lean_dec(x_488);
x_552 = lean_box(0);
x_553 = x_558;
goto block_557;
}
block_557:
{
lean_object* x_554; 
if (x_553 == 0)
{
lean_ctor_set(x_552, 4, x_495);
lean_ctor_set(x_552, 3, x_551);
lean_ctor_set(x_552, 2, x_493);
lean_ctor_set(x_552, 1, x_492);
lean_ctor_set(x_552, 0, x_549);
x_554 = x_552;
goto block_555;
}
else
{
lean_object* x_556; 
x_556 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_556, 0, x_549);
lean_ctor_set(x_556, 1, x_492);
lean_ctor_set(x_556, 2, x_493);
lean_ctor_set(x_556, 3, x_551);
lean_ctor_set(x_556, 4, x_495);
x_554 = x_556;
goto block_555;
}
block_555:
{
return x_554;
}
}
}
}
}
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_488, 0);
lean_inc(x_573);
x_574 = lean_nat_add(x_489, x_573);
lean_dec(x_573);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_488);
lean_ctor_set(x_7, 0, x_574);
x_575 = x_7;
goto block_576;
}
else
{
lean_object* x_577; 
x_577 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_3);
lean_ctor_set(x_577, 2, x_4);
lean_ctor_set(x_577, 3, x_488);
lean_ctor_set(x_577, 4, x_6);
x_575 = x_577;
goto block_576;
}
block_576:
{
return x_575;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_578; 
x_578 = lean_ctor_get(x_6, 3);
lean_inc(x_578);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; 
x_579 = lean_ctor_get(x_6, 4);
lean_inc(x_579);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; uint8_t x_595; 
x_580 = lean_ctor_get(x_6, 0);
x_581 = lean_ctor_get(x_6, 1);
x_582 = lean_ctor_get(x_6, 2);
x_595 = !lean_is_exclusive(x_6);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_ctor_get(x_6, 4);
lean_dec(x_596);
x_597 = lean_ctor_get(x_6, 3);
lean_dec(x_597);
x_583 = x_6;
x_584 = x_595;
goto block_594;
}
else
{
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_6);
x_583 = lean_box(0);
x_584 = x_595;
goto block_594;
}
block_594:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_585 = lean_ctor_get(x_578, 0);
x_586 = lean_nat_add(x_489, x_580);
lean_dec(x_580);
x_587 = lean_nat_add(x_489, x_585);
if (x_584 == 0)
{
lean_ctor_set(x_583, 4, x_578);
lean_ctor_set(x_583, 3, x_488);
lean_ctor_set(x_583, 2, x_4);
lean_ctor_set(x_583, 1, x_3);
lean_ctor_set(x_583, 0, x_587);
x_588 = x_583;
goto block_592;
}
else
{
lean_object* x_593; 
x_593 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_593, 0, x_587);
lean_ctor_set(x_593, 1, x_3);
lean_ctor_set(x_593, 2, x_4);
lean_ctor_set(x_593, 3, x_488);
lean_ctor_set(x_593, 4, x_578);
x_588 = x_593;
goto block_592;
}
block_592:
{
lean_object* x_589; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_579);
lean_ctor_set(x_7, 3, x_588);
lean_ctor_set(x_7, 2, x_582);
lean_ctor_set(x_7, 1, x_581);
lean_ctor_set(x_7, 0, x_586);
x_589 = x_7;
goto block_590;
}
else
{
lean_object* x_591; 
x_591 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_591, 0, x_586);
lean_ctor_set(x_591, 1, x_581);
lean_ctor_set(x_591, 2, x_582);
lean_ctor_set(x_591, 3, x_588);
lean_ctor_set(x_591, 4, x_579);
x_589 = x_591;
goto block_590;
}
block_590:
{
return x_589;
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; uint8_t x_622; 
x_598 = lean_ctor_get(x_6, 1);
x_599 = lean_ctor_get(x_6, 2);
x_622 = !lean_is_exclusive(x_6);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_6, 4);
lean_dec(x_623);
x_624 = lean_ctor_get(x_6, 3);
lean_dec(x_624);
x_625 = lean_ctor_get(x_6, 0);
lean_dec(x_625);
x_600 = x_6;
x_601 = x_622;
goto block_621;
}
else
{
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_6);
x_600 = lean_box(0);
x_601 = x_622;
goto block_621;
}
block_621:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; uint8_t x_617; 
x_602 = lean_ctor_get(x_578, 1);
x_603 = lean_ctor_get(x_578, 2);
x_617 = !lean_is_exclusive(x_578);
if (x_617 == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_578, 4);
lean_dec(x_618);
x_619 = lean_ctor_get(x_578, 3);
lean_dec(x_619);
x_620 = lean_ctor_get(x_578, 0);
lean_dec(x_620);
x_604 = x_578;
x_605 = x_617;
goto block_616;
}
else
{
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_578);
x_604 = lean_box(0);
x_605 = x_617;
goto block_616;
}
block_616:
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_unsigned_to_nat(3u);
if (x_605 == 0)
{
lean_ctor_set(x_604, 4, x_579);
lean_ctor_set(x_604, 3, x_579);
lean_ctor_set(x_604, 2, x_4);
lean_ctor_set(x_604, 1, x_3);
lean_ctor_set(x_604, 0, x_489);
x_607 = x_604;
goto block_614;
}
else
{
lean_object* x_615; 
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_489);
lean_ctor_set(x_615, 1, x_3);
lean_ctor_set(x_615, 2, x_4);
lean_ctor_set(x_615, 3, x_579);
lean_ctor_set(x_615, 4, x_579);
x_607 = x_615;
goto block_614;
}
block_614:
{
lean_object* x_608; 
if (x_601 == 0)
{
lean_ctor_set(x_600, 3, x_579);
lean_ctor_set(x_600, 0, x_489);
x_608 = x_600;
goto block_612;
}
else
{
lean_object* x_613; 
x_613 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_613, 0, x_489);
lean_ctor_set(x_613, 1, x_598);
lean_ctor_set(x_613, 2, x_599);
lean_ctor_set(x_613, 3, x_579);
lean_ctor_set(x_613, 4, x_579);
x_608 = x_613;
goto block_612;
}
block_612:
{
lean_object* x_609; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_608);
lean_ctor_set(x_7, 3, x_607);
lean_ctor_set(x_7, 2, x_603);
lean_ctor_set(x_7, 1, x_602);
lean_ctor_set(x_7, 0, x_606);
x_609 = x_7;
goto block_610;
}
else
{
lean_object* x_611; 
x_611 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_611, 0, x_606);
lean_ctor_set(x_611, 1, x_602);
lean_ctor_set(x_611, 2, x_603);
lean_ctor_set(x_611, 3, x_607);
lean_ctor_set(x_611, 4, x_608);
x_609 = x_611;
goto block_610;
}
block_610:
{
return x_609;
}
}
}
}
}
}
}
else
{
lean_object* x_626; 
x_626 = lean_ctor_get(x_6, 4);
lean_inc(x_626);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; uint8_t x_639; 
x_627 = lean_ctor_get(x_6, 1);
x_628 = lean_ctor_get(x_6, 2);
x_639 = !lean_is_exclusive(x_6);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_6, 4);
lean_dec(x_640);
x_641 = lean_ctor_get(x_6, 3);
lean_dec(x_641);
x_642 = lean_ctor_get(x_6, 0);
lean_dec(x_642);
x_629 = x_6;
x_630 = x_639;
goto block_638;
}
else
{
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_6);
x_629 = lean_box(0);
x_630 = x_639;
goto block_638;
}
block_638:
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_unsigned_to_nat(3u);
if (x_630 == 0)
{
lean_ctor_set(x_629, 4, x_578);
lean_ctor_set(x_629, 2, x_4);
lean_ctor_set(x_629, 1, x_3);
lean_ctor_set(x_629, 0, x_489);
x_632 = x_629;
goto block_636;
}
else
{
lean_object* x_637; 
x_637 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_637, 0, x_489);
lean_ctor_set(x_637, 1, x_3);
lean_ctor_set(x_637, 2, x_4);
lean_ctor_set(x_637, 3, x_578);
lean_ctor_set(x_637, 4, x_578);
x_632 = x_637;
goto block_636;
}
block_636:
{
lean_object* x_633; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_626);
lean_ctor_set(x_7, 3, x_632);
lean_ctor_set(x_7, 2, x_628);
lean_ctor_set(x_7, 1, x_627);
lean_ctor_set(x_7, 0, x_631);
x_633 = x_7;
goto block_634;
}
else
{
lean_object* x_635; 
x_635 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_635, 0, x_631);
lean_ctor_set(x_635, 1, x_627);
lean_ctor_set(x_635, 2, x_628);
lean_ctor_set(x_635, 3, x_632);
lean_ctor_set(x_635, 4, x_626);
x_633 = x_635;
goto block_634;
}
block_634:
{
return x_633;
}
}
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; uint8_t x_656; 
x_643 = lean_ctor_get(x_6, 0);
x_644 = lean_ctor_get(x_6, 1);
x_645 = lean_ctor_get(x_6, 2);
x_656 = !lean_is_exclusive(x_6);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_ctor_get(x_6, 4);
lean_dec(x_657);
x_658 = lean_ctor_get(x_6, 3);
lean_dec(x_658);
x_646 = x_6;
x_647 = x_656;
goto block_655;
}
else
{
lean_inc(x_645);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_6);
x_646 = lean_box(0);
x_647 = x_656;
goto block_655;
}
block_655:
{
lean_object* x_648; 
if (x_647 == 0)
{
lean_ctor_set(x_646, 3, x_626);
x_648 = x_646;
goto block_653;
}
else
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_654, 0, x_643);
lean_ctor_set(x_654, 1, x_644);
lean_ctor_set(x_654, 2, x_645);
lean_ctor_set(x_654, 3, x_626);
lean_ctor_set(x_654, 4, x_626);
x_648 = x_654;
goto block_653;
}
block_653:
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_648);
lean_ctor_set(x_7, 3, x_626);
lean_ctor_set(x_7, 0, x_649);
x_650 = x_7;
goto block_651;
}
else
{
lean_object* x_652; 
x_652 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_3);
lean_ctor_set(x_652, 2, x_4);
lean_ctor_set(x_652, 3, x_626);
lean_ctor_set(x_652, 4, x_648);
x_650 = x_652;
goto block_651;
}
block_651:
{
return x_650;
}
}
}
}
}
}
else
{
lean_object* x_659; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 0, x_489);
x_659 = x_7;
goto block_660;
}
else
{
lean_object* x_661; 
x_661 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_661, 0, x_489);
lean_ctor_set(x_661, 1, x_3);
lean_ctor_set(x_661, 2, x_4);
lean_ctor_set(x_661, 3, x_6);
lean_ctor_set(x_661, 4, x_6);
x_659 = x_661;
goto block_660;
}
block_660:
{
return x_659;
}
}
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
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
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
x_16 = x_12;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(x_2, x_14);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set_uint64(x_21, sizeof(void*)*1, x_15);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
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
x_8 = lean_array_uget_borrowed(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
x_7 = lean_array_uget_borrowed(x_2, x_3);
x_8 = lean_unbox_uint64(x_7);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync_CancellationToken(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin)
;
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
res = initialize_Std_Sync_CancellationToken(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationContext(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_CancellationContext(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_CancellationContext(builtin);
}
#ifdef __cplusplus
}
#endif
