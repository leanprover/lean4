// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Lean.Meta.Tactic.Clear
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__6;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_setKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__3;
lean_object* l_Lean_LocalDecl_index(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1;
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__2;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_MVarId_revert___closed__2;
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__5;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = l_Lean_Expr_fvarId_x21(x_14);
lean_inc(x_7);
lean_inc(x_18);
x_19 = l_Lean_FVarId_getDecl(x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_isAuxDecl(x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_18);
x_23 = lean_array_push(x_17, x_14);
lean_ctor_set(x_6, 1, x_23);
x_24 = 1;
x_25 = lean_usize_add(x_5, x_24);
x_5 = x_25;
x_11 = x_21;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_MVarId_clear(x_16, x_18, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_6, 0, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_11 = x_29;
goto _start;
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = l_Lean_Expr_fvarId_x21(x_14);
lean_inc(x_7);
lean_inc(x_43);
x_44 = l_Lean_FVarId_getDecl(x_43, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_LocalDecl_isAuxDecl(x_45);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_43);
x_48 = lean_array_push(x_42, x_14);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_5, x_50);
x_5 = x_51;
x_6 = x_49;
x_11 = x_46;
goto _start;
}
else
{
lean_object* x_53; 
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_53 = l_Lean_MVarId_clear(x_41, x_43, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_42);
x_57 = 1;
x_58 = lean_usize_add(x_5, x_57);
x_5 = x_58;
x_6 = x_56;
x_11 = x_55;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_64 = lean_ctor_get(x_44, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_66 = x_44;
} else {
 lean_dec_ref(x_44);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to revert ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", it is an auxiliary declaration created to represent recursive definitions", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_7);
lean_inc(x_14);
x_15 = l_Lean_FVarId_getDecl(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_isAuxDecl(x_16);
lean_dec(x_16);
if (x_18 == 0)
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_14);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_21 = lean_box(0);
x_5 = x_20;
x_6 = x_21;
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = l_Lean_Expr_fvar___override(x_14);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_28, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_14 = 2;
lean_inc(x_13);
x_15 = l_Lean_MVarId_setKind(x_13, x_14, x_4, x_5, x_6, x_7, x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_13);
x_17 = l_Lean_MVarId_setTag(x_13, x_1, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_array_size(x_11);
x_21 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(x_20, x_2, x_11);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_21);
lean_ctor_set(x_17, 0, x_3);
return x_17;
}
else
{
lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_array_size(x_11);
x_24 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(x_23, x_2, x_11);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = l_Lean_Expr_getAppFn(x_26);
lean_dec(x_26);
x_29 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
x_30 = 2;
lean_inc(x_29);
x_31 = l_Lean_MVarId_setKind(x_29, x_30, x_4, x_5, x_6, x_7, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_29);
x_33 = l_Lean_MVarId_setTag(x_29, x_1, x_4, x_5, x_6, x_7, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_array_size(x_27);
x_37 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(x_36, x_2, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_revert___lambda__2___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MVarId_revert___lambda__2___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create binder due to failure when reverting variable dependencies", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_revert___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_10, x_11, x_1);
lean_inc(x_5);
x_13 = l_Lean_Meta_collectForwardDeps(x_12, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_size(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1(x_14, x_16, x_14, x_19, x_11, x_18, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_23);
x_25 = l_Lean_MVarId_getTag(x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_40; lean_object* x_53; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
lean_inc(x_23);
x_29 = l_Lean_MVarId_setKind(x_23, x_28, x_5, x_6, x_7, x_8, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
x_82 = lean_st_ref_get(x_8, x_30);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_6, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_8, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 2);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_get(x_8, x_92);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = l_Lean_Environment_mainModule(x_85);
lean_dec(x_85);
lean_ctor_set(x_94, 1, x_81);
lean_ctor_set(x_94, 0, x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_100);
lean_inc(x_23);
x_102 = l_Lean_MetavarContext_revert(x_24, x_23, x_2, x_94, x_101);
lean_dec(x_94);
lean_dec(x_24);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 2);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_st_ref_take(x_6, x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_105);
x_113 = lean_st_ref_set(x_6, x_109, x_110);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_take(x_8, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_116, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_dec(x_120);
lean_ctor_set(x_116, 2, x_107);
lean_ctor_set(x_116, 1, x_106);
x_121 = lean_st_ref_set(x_8, x_116, x_117);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
lean_ctor_set(x_121, 0, x_104);
x_53 = x_121;
goto block_80;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_104);
lean_ctor_set(x_125, 1, x_124);
x_53 = x_125;
goto block_80;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_ctor_get(x_116, 0);
x_127 = lean_ctor_get(x_116, 3);
x_128 = lean_ctor_get(x_116, 4);
x_129 = lean_ctor_get(x_116, 5);
x_130 = lean_ctor_get(x_116, 6);
x_131 = lean_ctor_get(x_116, 7);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_116);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_106);
lean_ctor_set(x_132, 2, x_107);
lean_ctor_set(x_132, 3, x_127);
lean_ctor_set(x_132, 4, x_128);
lean_ctor_set(x_132, 5, x_129);
lean_ctor_set(x_132, 6, x_130);
lean_ctor_set(x_132, 7, x_131);
x_133 = lean_st_ref_set(x_8, x_132, x_117);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_104);
lean_ctor_set(x_136, 1, x_134);
x_53 = x_136;
goto block_80;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_137 = lean_ctor_get(x_109, 1);
x_138 = lean_ctor_get(x_109, 2);
x_139 = lean_ctor_get(x_109, 3);
x_140 = lean_ctor_get(x_109, 4);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_109);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_105);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set(x_141, 2, x_138);
lean_ctor_set(x_141, 3, x_139);
lean_ctor_set(x_141, 4, x_140);
x_142 = lean_st_ref_set(x_6, x_141, x_110);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_st_ref_take(x_8, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 5);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 6);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 7);
lean_inc(x_152);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 lean_ctor_release(x_145, 5);
 lean_ctor_release(x_145, 6);
 lean_ctor_release(x_145, 7);
 x_153 = x_145;
} else {
 lean_dec_ref(x_145);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 8, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_106);
lean_ctor_set(x_154, 2, x_107);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set(x_154, 4, x_149);
lean_ctor_set(x_154, 5, x_150);
lean_ctor_set(x_154, 6, x_151);
lean_ctor_set(x_154, 7, x_152);
x_155 = lean_st_ref_set(x_8, x_154, x_146);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_104);
lean_ctor_set(x_158, 1, x_156);
x_53 = x_158;
goto block_80;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_159 = lean_ctor_get(x_102, 1);
lean_inc(x_159);
lean_dec(x_102);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 2);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_st_ref_take(x_6, x_97);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = !lean_is_exclusive(x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_167 = lean_ctor_get(x_164, 0);
lean_dec(x_167);
lean_ctor_set(x_164, 0, x_160);
x_168 = lean_st_ref_set(x_6, x_164, x_165);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_st_ref_take(x_8, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_171, 2);
lean_dec(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_dec(x_175);
lean_ctor_set(x_171, 2, x_162);
lean_ctor_set(x_171, 1, x_161);
x_176 = lean_st_ref_set(x_8, x_171, x_172);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_MVarId_revert___lambda__2___closed__6;
x_179 = l_Lean_throwError___at_Lean_MVarId_revert___spec__3(x_178, x_5, x_6, x_7, x_8, x_177);
x_53 = x_179;
goto block_80;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_180 = lean_ctor_get(x_171, 0);
x_181 = lean_ctor_get(x_171, 3);
x_182 = lean_ctor_get(x_171, 4);
x_183 = lean_ctor_get(x_171, 5);
x_184 = lean_ctor_get(x_171, 6);
x_185 = lean_ctor_get(x_171, 7);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_171);
x_186 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_186, 0, x_180);
lean_ctor_set(x_186, 1, x_161);
lean_ctor_set(x_186, 2, x_162);
lean_ctor_set(x_186, 3, x_181);
lean_ctor_set(x_186, 4, x_182);
lean_ctor_set(x_186, 5, x_183);
lean_ctor_set(x_186, 6, x_184);
lean_ctor_set(x_186, 7, x_185);
x_187 = lean_st_ref_set(x_8, x_186, x_172);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = l_Lean_MVarId_revert___lambda__2___closed__6;
x_190 = l_Lean_throwError___at_Lean_MVarId_revert___spec__3(x_189, x_5, x_6, x_7, x_8, x_188);
x_53 = x_190;
goto block_80;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_191 = lean_ctor_get(x_164, 1);
x_192 = lean_ctor_get(x_164, 2);
x_193 = lean_ctor_get(x_164, 3);
x_194 = lean_ctor_get(x_164, 4);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_164);
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_160);
lean_ctor_set(x_195, 1, x_191);
lean_ctor_set(x_195, 2, x_192);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
x_196 = lean_st_ref_set(x_6, x_195, x_165);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_st_ref_take(x_8, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 5);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 6);
lean_inc(x_205);
x_206 = lean_ctor_get(x_199, 7);
lean_inc(x_206);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 lean_ctor_release(x_199, 6);
 lean_ctor_release(x_199, 7);
 x_207 = x_199;
} else {
 lean_dec_ref(x_199);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 8, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_201);
lean_ctor_set(x_208, 1, x_161);
lean_ctor_set(x_208, 2, x_162);
lean_ctor_set(x_208, 3, x_202);
lean_ctor_set(x_208, 4, x_203);
lean_ctor_set(x_208, 5, x_204);
lean_ctor_set(x_208, 6, x_205);
lean_ctor_set(x_208, 7, x_206);
x_209 = lean_st_ref_set(x_8, x_208, x_200);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = l_Lean_MVarId_revert___lambda__2___closed__6;
x_212 = l_Lean_throwError___at_Lean_MVarId_revert___spec__3(x_211, x_5, x_6, x_7, x_8, x_210);
x_53 = x_212;
goto block_80;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_94, 0);
x_214 = lean_ctor_get(x_94, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_94);
x_215 = l_Lean_Environment_mainModule(x_85);
lean_dec(x_85);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_81);
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
lean_dec(x_213);
x_218 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_219 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_219, 0, x_89);
lean_ctor_set(x_219, 1, x_217);
lean_ctor_set(x_219, 2, x_93);
lean_ctor_set(x_219, 3, x_218);
lean_inc(x_23);
x_220 = l_Lean_MetavarContext_revert(x_24, x_23, x_2, x_216, x_219);
lean_dec(x_216);
lean_dec(x_24);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 2);
lean_inc(x_225);
lean_dec(x_221);
x_226 = lean_st_ref_take(x_6, x_214);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 4);
lean_inc(x_232);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 lean_ctor_release(x_227, 4);
 x_233 = x_227;
} else {
 lean_dec_ref(x_227);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 5, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_223);
lean_ctor_set(x_234, 1, x_229);
lean_ctor_set(x_234, 2, x_230);
lean_ctor_set(x_234, 3, x_231);
lean_ctor_set(x_234, 4, x_232);
x_235 = lean_st_ref_set(x_6, x_234, x_228);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_st_ref_take(x_8, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 4);
lean_inc(x_242);
x_243 = lean_ctor_get(x_238, 5);
lean_inc(x_243);
x_244 = lean_ctor_get(x_238, 6);
lean_inc(x_244);
x_245 = lean_ctor_get(x_238, 7);
lean_inc(x_245);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 lean_ctor_release(x_238, 5);
 lean_ctor_release(x_238, 6);
 lean_ctor_release(x_238, 7);
 x_246 = x_238;
} else {
 lean_dec_ref(x_238);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 8, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_224);
lean_ctor_set(x_247, 2, x_225);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set(x_247, 4, x_242);
lean_ctor_set(x_247, 5, x_243);
lean_ctor_set(x_247, 6, x_244);
lean_ctor_set(x_247, 7, x_245);
x_248 = lean_st_ref_set(x_8, x_247, x_239);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_222);
lean_ctor_set(x_251, 1, x_249);
x_53 = x_251;
goto block_80;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_252 = lean_ctor_get(x_220, 1);
lean_inc(x_252);
lean_dec(x_220);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 2);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_st_ref_take(x_6, x_214);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 2);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 4);
lean_inc(x_262);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 x_263 = x_257;
} else {
 lean_dec_ref(x_257);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 5, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_253);
lean_ctor_set(x_264, 1, x_259);
lean_ctor_set(x_264, 2, x_260);
lean_ctor_set(x_264, 3, x_261);
lean_ctor_set(x_264, 4, x_262);
x_265 = lean_st_ref_set(x_6, x_264, x_258);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_st_ref_take(x_8, x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 5);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 6);
lean_inc(x_274);
x_275 = lean_ctor_get(x_268, 7);
lean_inc(x_275);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 lean_ctor_release(x_268, 4);
 lean_ctor_release(x_268, 5);
 lean_ctor_release(x_268, 6);
 lean_ctor_release(x_268, 7);
 x_276 = x_268;
} else {
 lean_dec_ref(x_268);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 8, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_270);
lean_ctor_set(x_277, 1, x_254);
lean_ctor_set(x_277, 2, x_255);
lean_ctor_set(x_277, 3, x_271);
lean_ctor_set(x_277, 4, x_272);
lean_ctor_set(x_277, 5, x_273);
lean_ctor_set(x_277, 6, x_274);
lean_ctor_set(x_277, 7, x_275);
x_278 = lean_st_ref_set(x_8, x_277, x_269);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_MVarId_revert___lambda__2___closed__6;
x_281 = l_Lean_throwError___at_Lean_MVarId_revert___spec__3(x_280, x_5, x_6, x_7, x_8, x_279);
x_53 = x_281;
goto block_80;
}
}
block_39:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_MVarId_revert___lambda__1(x_26, x_11, x_32, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_52:
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_43);
x_31 = x_40;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_31 = x_47;
goto block_39;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
x_31 = x_40;
goto block_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_31 = x_51;
goto block_39;
}
}
}
block_80:
{
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_53, 1);
x_56 = 2;
x_57 = l_Lean_MVarId_setKind(x_23, x_56, x_5, x_6, x_7, x_8, x_55);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_53, 1, x_59);
lean_ctor_set(x_57, 0, x_53);
x_40 = x_57;
goto block_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_53, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_61);
x_40 = x_62;
goto block_52;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_53, 0);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_53);
x_65 = 2;
x_66 = l_Lean_MVarId_setKind(x_23, x_65, x_5, x_6, x_7, x_8, x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_67);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_40 = x_71;
goto block_52;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = 2;
x_75 = l_Lean_MVarId_setKind(x_23, x_74, x_5, x_6, x_7, x_8, x_73);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_72);
x_40 = x_75;
goto block_52;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
x_40 = x_79;
goto block_52;
}
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_282 = !lean_is_exclusive(x_25);
if (x_282 == 0)
{
return x_25;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_25, 0);
x_284 = lean_ctor_get(x_25, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_25);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_286 = !lean_is_exclusive(x_20);
if (x_286 == 0)
{
return x_20;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_20, 0);
x_288 = lean_ctor_get(x_20, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_20);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = !lean_is_exclusive(x_13);
if (x_290 == 0)
{
return x_13;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_13, 0);
x_292 = lean_ctor_get(x_13, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_13);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (x_5 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_array_size(x_3);
x_15 = 0;
x_16 = lean_box(0);
lean_inc(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4(x_3, x_13, x_3, x_14, x_15, x_16, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_MVarId_revert___lambda__2(x_3, x_4, x_1, x_16, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = l_Lean_MVarId_revert___lambda__2(x_3, x_4, x_1, x_25, x_6, x_7, x_8, x_9, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("revert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_revert___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_MVarId_revert___closed__2;
x_12 = lean_box(x_3);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lambda__3___boxed), 10, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
x_15 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_revert___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_MVarId_revert___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_MVarId_revert___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_MVarId_revert___lambda__3(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_MVarId_revert(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4(x_6, x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_array_push(x_4, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_usize_shift_right(x_2, x_3);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = l_Lean_LocalDecl_index(x_9);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_16 = l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1(x_11, x_15, x_14);
lean_dec(x_14);
lean_dec(x_11);
x_17 = 1;
x_18 = l_Lean_MVarId_revert(x_2, x_16, x_17, x_17, x_3, x_4, x_5, x_6, x_10);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAfter___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_MVarId_revertAfter___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at_Lean_MVarId_revertAfter___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldlM___at_Lean_MVarId_revertAfter___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_revert___spec__4___closed__4);
l_Lean_MVarId_revert___lambda__2___closed__1 = _init_l_Lean_MVarId_revert___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__1);
l_Lean_MVarId_revert___lambda__2___closed__2 = _init_l_Lean_MVarId_revert___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__2);
l_Lean_MVarId_revert___lambda__2___closed__3 = _init_l_Lean_MVarId_revert___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__3);
l_Lean_MVarId_revert___lambda__2___closed__4 = _init_l_Lean_MVarId_revert___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__4);
l_Lean_MVarId_revert___lambda__2___closed__5 = _init_l_Lean_MVarId_revert___lambda__2___closed__5();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__5);
l_Lean_MVarId_revert___lambda__2___closed__6 = _init_l_Lean_MVarId_revert___lambda__2___closed__6();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__6);
l_Lean_MVarId_revert___closed__1 = _init_l_Lean_MVarId_revert___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___closed__1);
l_Lean_MVarId_revert___closed__2 = _init_l_Lean_MVarId_revert___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___closed__2);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_MVarId_revertAfter___spec__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
