// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Init Lean.Meta.Tactic.Clear
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__1;
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__2;
static lean_object* l_Lean_MVarId_revert___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__3;
lean_object* l_Lean_MVarId_setKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4;
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to revert ", 17);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", it is an auxiliary declaration created to represent recursive definitions", 75);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalDecl(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_isAuxDecl(x_14);
lean_dec(x_14);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_12);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = l_Lean_Expr_fvar___override(x_12);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_26, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_16 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_5);
lean_inc(x_16);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_isAuxDecl(x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec(x_16);
x_21 = lean_array_push(x_15, x_12);
lean_ctor_set(x_4, 1, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_9 = x_19;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_MVarId_clear(x_14, x_16, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_4, 0, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
x_9 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
lean_inc(x_12);
x_41 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_5);
lean_inc(x_41);
x_42 = l_Lean_Meta_getLocalDecl(x_41, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_LocalDecl_isAuxDecl(x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_41);
x_46 = lean_array_push(x_40, x_12);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_3, x_48);
x_3 = x_49;
x_4 = x_47;
x_9 = x_44;
goto _start;
}
else
{
lean_object* x_51; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_51 = l_Lean_MVarId_clear(x_39, x_41, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_40);
x_55 = 1;
x_56 = lean_usize_add(x_3, x_55);
x_3 = x_56;
x_4 = x_54;
x_9 = x_53;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = lean_ctor_get(x_42, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_64 = x_42;
} else {
 lean_dec_ref(x_42);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_13);
x_14 = l_Lean_MVarId_setTag(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_array_get_size(x_11);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_18, x_2, x_11);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_19);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_array_get_size(x_11);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_22, x_2, x_11);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = l_Lean_Expr_getAppFn(x_25);
lean_dec(x_25);
x_28 = l_Lean_Expr_mvarId_x21(x_27);
lean_inc(x_28);
x_29 = l_Lean_MVarId_setTag(x_28, x_1, x_4, x_5, x_6, x_7, x_8);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_array_get_size(x_26);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_33, x_2, x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to create binder due to failure when reverting variable dependencies", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_revert___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_3);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_5);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(x_3, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_13, x_14, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_collectForwardDeps(x_18, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_get_size(x_20);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(x_20, x_25, x_14, x_23, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_29);
x_31 = l_Lean_MVarId_getTag(x_29, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_47; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
lean_inc(x_29);
x_35 = l_Lean_MVarId_setKind(x_29, x_34, x_5, x_6, x_7, x_8, x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
x_69 = lean_st_ref_get(x_8, x_36);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_get(x_8, x_71);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_get(x_6, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_8, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 2);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_8, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_environment_main_module(x_72);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_68);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = l_Lean_MVarId_revert___lambda__2___closed__2;
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_82);
lean_ctor_set(x_90, 3, x_89);
lean_inc(x_29);
x_91 = l_Lean_MetavarContext_revert(x_30, x_29, x_4, x_87, x_90);
lean_dec(x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_120 = lean_ctor_get(x_93, 0);
lean_inc(x_120);
x_121 = lean_st_ref_get(x_8, x_85);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_take(x_6, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_120, sizeof(void*)*8);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_ctor_get(x_120, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_120, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_120, 5);
lean_inc(x_133);
x_134 = lean_ctor_get(x_120, 6);
lean_inc(x_134);
x_135 = lean_ctor_get(x_120, 7);
lean_inc(x_135);
lean_dec(x_120);
x_136 = !lean_is_exclusive(x_124);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_124, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_126);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_139 = lean_ctor_get(x_126, 7);
lean_dec(x_139);
x_140 = lean_ctor_get(x_126, 6);
lean_dec(x_140);
x_141 = lean_ctor_get(x_126, 5);
lean_dec(x_141);
x_142 = lean_ctor_get(x_126, 4);
lean_dec(x_142);
x_143 = lean_ctor_get(x_126, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_126, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_126, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_126, 0);
lean_dec(x_146);
lean_ctor_set(x_126, 7, x_135);
lean_ctor_set(x_126, 6, x_134);
lean_ctor_set(x_126, 5, x_133);
lean_ctor_set(x_126, 4, x_132);
lean_ctor_set(x_126, 3, x_131);
lean_ctor_set(x_126, 2, x_130);
lean_ctor_set(x_126, 1, x_129);
lean_ctor_set(x_126, 0, x_128);
x_147 = lean_st_ref_set(x_6, x_124, x_127);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_94 = x_148;
goto block_119;
}
else
{
uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get_uint8(x_126, sizeof(void*)*8);
lean_dec(x_126);
x_150 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_150, 0, x_128);
lean_ctor_set(x_150, 1, x_129);
lean_ctor_set(x_150, 2, x_130);
lean_ctor_set(x_150, 3, x_131);
lean_ctor_set(x_150, 4, x_132);
lean_ctor_set(x_150, 5, x_133);
lean_ctor_set(x_150, 6, x_134);
lean_ctor_set(x_150, 7, x_135);
lean_ctor_set_uint8(x_150, sizeof(void*)*8, x_149);
lean_ctor_set(x_124, 0, x_150);
x_151 = lean_st_ref_set(x_6, x_124, x_127);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_94 = x_152;
goto block_119;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = lean_ctor_get(x_124, 1);
x_154 = lean_ctor_get(x_124, 2);
x_155 = lean_ctor_get(x_124, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_124);
x_156 = lean_ctor_get_uint8(x_126, sizeof(void*)*8);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 lean_ctor_release(x_126, 5);
 lean_ctor_release(x_126, 6);
 lean_ctor_release(x_126, 7);
 x_157 = x_126;
} else {
 lean_dec_ref(x_126);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 8, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_128);
lean_ctor_set(x_158, 1, x_129);
lean_ctor_set(x_158, 2, x_130);
lean_ctor_set(x_158, 3, x_131);
lean_ctor_set(x_158, 4, x_132);
lean_ctor_set(x_158, 5, x_133);
lean_ctor_set(x_158, 6, x_134);
lean_ctor_set(x_158, 7, x_135);
lean_ctor_set_uint8(x_158, sizeof(void*)*8, x_156);
x_159 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_155);
x_160 = lean_st_ref_set(x_6, x_159, x_127);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_94 = x_161;
goto block_119;
}
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_123, 1);
lean_inc(x_162);
lean_dec(x_123);
x_163 = !lean_is_exclusive(x_120);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_124);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_124, 0);
lean_dec(x_165);
x_166 = 1;
lean_ctor_set_uint8(x_120, sizeof(void*)*8, x_166);
lean_ctor_set(x_124, 0, x_120);
x_167 = lean_st_ref_set(x_6, x_124, x_162);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_94 = x_168;
goto block_119;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_124, 1);
x_170 = lean_ctor_get(x_124, 2);
x_171 = lean_ctor_get(x_124, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_124);
x_172 = 1;
lean_ctor_set_uint8(x_120, sizeof(void*)*8, x_172);
x_173 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_173, 0, x_120);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_170);
lean_ctor_set(x_173, 3, x_171);
x_174 = lean_st_ref_set(x_6, x_173, x_162);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_94 = x_175;
goto block_119;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_176 = lean_ctor_get(x_120, 0);
x_177 = lean_ctor_get(x_120, 1);
x_178 = lean_ctor_get(x_120, 2);
x_179 = lean_ctor_get(x_120, 3);
x_180 = lean_ctor_get(x_120, 4);
x_181 = lean_ctor_get(x_120, 5);
x_182 = lean_ctor_get(x_120, 6);
x_183 = lean_ctor_get(x_120, 7);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_120);
x_184 = lean_ctor_get(x_124, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_124, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_124, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 x_187 = x_124;
} else {
 lean_dec_ref(x_124);
 x_187 = lean_box(0);
}
x_188 = 1;
x_189 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_189, 0, x_176);
lean_ctor_set(x_189, 1, x_177);
lean_ctor_set(x_189, 2, x_178);
lean_ctor_set(x_189, 3, x_179);
lean_ctor_set(x_189, 4, x_180);
lean_ctor_set(x_189, 5, x_181);
lean_ctor_set(x_189, 6, x_182);
lean_ctor_set(x_189, 7, x_183);
lean_ctor_set_uint8(x_189, sizeof(void*)*8, x_188);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 4, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_184);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_186);
x_191 = lean_st_ref_set(x_6, x_190, x_162);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_94 = x_192;
goto block_119;
}
}
block_119:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_st_ref_take(x_8, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_96, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 2);
lean_inc(x_102);
lean_dec(x_93);
lean_ctor_set(x_96, 2, x_102);
lean_ctor_set(x_96, 1, x_101);
x_103 = lean_st_ref_set(x_8, x_96, x_97);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set(x_103, 0, x_92);
x_47 = x_103;
goto block_67;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_92);
lean_ctor_set(x_107, 1, x_106);
x_47 = x_107;
goto block_67;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_108 = lean_ctor_get(x_96, 0);
x_109 = lean_ctor_get(x_96, 3);
x_110 = lean_ctor_get(x_96, 4);
x_111 = lean_ctor_get(x_96, 5);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_96);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_93, 2);
lean_inc(x_113);
lean_dec(x_93);
x_114 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set(x_114, 4, x_110);
lean_ctor_set(x_114, 5, x_111);
x_115 = lean_st_ref_set(x_8, x_114, x_97);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_92);
lean_ctor_set(x_118, 1, x_116);
x_47 = x_118;
goto block_67;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_193 = lean_ctor_get(x_91, 1);
lean_inc(x_193);
lean_dec(x_91);
x_219 = lean_ctor_get(x_193, 0);
lean_inc(x_219);
x_220 = lean_st_ref_get(x_8, x_85);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_st_ref_take(x_6, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_219, sizeof(void*)*8);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_ctor_get(x_219, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_219, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_219, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_219, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_219, 4);
lean_inc(x_231);
x_232 = lean_ctor_get(x_219, 5);
lean_inc(x_232);
x_233 = lean_ctor_get(x_219, 6);
lean_inc(x_233);
x_234 = lean_ctor_get(x_219, 7);
lean_inc(x_234);
lean_dec(x_219);
x_235 = !lean_is_exclusive(x_223);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_223, 0);
lean_dec(x_236);
x_237 = !lean_is_exclusive(x_225);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_238 = lean_ctor_get(x_225, 7);
lean_dec(x_238);
x_239 = lean_ctor_get(x_225, 6);
lean_dec(x_239);
x_240 = lean_ctor_get(x_225, 5);
lean_dec(x_240);
x_241 = lean_ctor_get(x_225, 4);
lean_dec(x_241);
x_242 = lean_ctor_get(x_225, 3);
lean_dec(x_242);
x_243 = lean_ctor_get(x_225, 2);
lean_dec(x_243);
x_244 = lean_ctor_get(x_225, 1);
lean_dec(x_244);
x_245 = lean_ctor_get(x_225, 0);
lean_dec(x_245);
lean_ctor_set(x_225, 7, x_234);
lean_ctor_set(x_225, 6, x_233);
lean_ctor_set(x_225, 5, x_232);
lean_ctor_set(x_225, 4, x_231);
lean_ctor_set(x_225, 3, x_230);
lean_ctor_set(x_225, 2, x_229);
lean_ctor_set(x_225, 1, x_228);
lean_ctor_set(x_225, 0, x_227);
x_246 = lean_st_ref_set(x_6, x_223, x_226);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_194 = x_247;
goto block_218;
}
else
{
uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get_uint8(x_225, sizeof(void*)*8);
lean_dec(x_225);
x_249 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_249, 0, x_227);
lean_ctor_set(x_249, 1, x_228);
lean_ctor_set(x_249, 2, x_229);
lean_ctor_set(x_249, 3, x_230);
lean_ctor_set(x_249, 4, x_231);
lean_ctor_set(x_249, 5, x_232);
lean_ctor_set(x_249, 6, x_233);
lean_ctor_set(x_249, 7, x_234);
lean_ctor_set_uint8(x_249, sizeof(void*)*8, x_248);
lean_ctor_set(x_223, 0, x_249);
x_250 = lean_st_ref_set(x_6, x_223, x_226);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_194 = x_251;
goto block_218;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_252 = lean_ctor_get(x_223, 1);
x_253 = lean_ctor_get(x_223, 2);
x_254 = lean_ctor_get(x_223, 3);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_223);
x_255 = lean_ctor_get_uint8(x_225, sizeof(void*)*8);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 lean_ctor_release(x_225, 6);
 lean_ctor_release(x_225, 7);
 x_256 = x_225;
} else {
 lean_dec_ref(x_225);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(0, 8, 1);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_227);
lean_ctor_set(x_257, 1, x_228);
lean_ctor_set(x_257, 2, x_229);
lean_ctor_set(x_257, 3, x_230);
lean_ctor_set(x_257, 4, x_231);
lean_ctor_set(x_257, 5, x_232);
lean_ctor_set(x_257, 6, x_233);
lean_ctor_set(x_257, 7, x_234);
lean_ctor_set_uint8(x_257, sizeof(void*)*8, x_255);
x_258 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_252);
lean_ctor_set(x_258, 2, x_253);
lean_ctor_set(x_258, 3, x_254);
x_259 = lean_st_ref_set(x_6, x_258, x_226);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_194 = x_260;
goto block_218;
}
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_222, 1);
lean_inc(x_261);
lean_dec(x_222);
x_262 = !lean_is_exclusive(x_219);
if (x_262 == 0)
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_223);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_223, 0);
lean_dec(x_264);
x_265 = 1;
lean_ctor_set_uint8(x_219, sizeof(void*)*8, x_265);
lean_ctor_set(x_223, 0, x_219);
x_266 = lean_st_ref_set(x_6, x_223, x_261);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_194 = x_267;
goto block_218;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_223, 1);
x_269 = lean_ctor_get(x_223, 2);
x_270 = lean_ctor_get(x_223, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_223);
x_271 = 1;
lean_ctor_set_uint8(x_219, sizeof(void*)*8, x_271);
x_272 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_272, 0, x_219);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_269);
lean_ctor_set(x_272, 3, x_270);
x_273 = lean_st_ref_set(x_6, x_272, x_261);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_194 = x_274;
goto block_218;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_275 = lean_ctor_get(x_219, 0);
x_276 = lean_ctor_get(x_219, 1);
x_277 = lean_ctor_get(x_219, 2);
x_278 = lean_ctor_get(x_219, 3);
x_279 = lean_ctor_get(x_219, 4);
x_280 = lean_ctor_get(x_219, 5);
x_281 = lean_ctor_get(x_219, 6);
x_282 = lean_ctor_get(x_219, 7);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_219);
x_283 = lean_ctor_get(x_223, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_223, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_223, 3);
lean_inc(x_285);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 x_286 = x_223;
} else {
 lean_dec_ref(x_223);
 x_286 = lean_box(0);
}
x_287 = 1;
x_288 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_288, 0, x_275);
lean_ctor_set(x_288, 1, x_276);
lean_ctor_set(x_288, 2, x_277);
lean_ctor_set(x_288, 3, x_278);
lean_ctor_set(x_288, 4, x_279);
lean_ctor_set(x_288, 5, x_280);
lean_ctor_set(x_288, 6, x_281);
lean_ctor_set(x_288, 7, x_282);
lean_ctor_set_uint8(x_288, sizeof(void*)*8, x_287);
if (lean_is_scalar(x_286)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_286;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_283);
lean_ctor_set(x_289, 2, x_284);
lean_ctor_set(x_289, 3, x_285);
x_290 = lean_st_ref_set(x_6, x_289, x_261);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_194 = x_291;
goto block_218;
}
}
block_218:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_st_ref_take(x_8, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = lean_ctor_get(x_196, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_196, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 2);
lean_inc(x_202);
lean_dec(x_193);
lean_ctor_set(x_196, 2, x_202);
lean_ctor_set(x_196, 1, x_201);
x_203 = lean_st_ref_set(x_8, x_196, x_197);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_206 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_205, x_5, x_6, x_7, x_8, x_204);
x_47 = x_206;
goto block_67;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_207 = lean_ctor_get(x_196, 0);
x_208 = lean_ctor_get(x_196, 3);
x_209 = lean_ctor_get(x_196, 4);
x_210 = lean_ctor_get(x_196, 5);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_196);
x_211 = lean_ctor_get(x_193, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_193, 2);
lean_inc(x_212);
lean_dec(x_193);
x_213 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_208);
lean_ctor_set(x_213, 4, x_209);
lean_ctor_set(x_213, 5, x_210);
x_214 = lean_st_ref_set(x_8, x_213, x_197);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_217 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_216, x_5, x_6, x_7, x_8, x_215);
x_47 = x_217;
goto block_67;
}
}
}
block_46:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_MVarId_revert___lambda__1(x_32, x_14, x_40, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
block_67:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = 2;
x_51 = l_Lean_MVarId_setKind(x_29, x_50, x_5, x_6, x_7, x_8, x_49);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_51, 0, x_54);
x_37 = x_51;
goto block_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_37 = x_58;
goto block_46;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_dec(x_47);
x_61 = 2;
x_62 = l_Lean_MVarId_setKind(x_29, x_61, x_5, x_6, x_7, x_8, x_60);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_59);
x_37 = x_62;
goto block_46;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
x_37 = x_66;
goto block_46;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_292 = !lean_is_exclusive(x_31);
if (x_292 == 0)
{
return x_31;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_31, 0);
x_294 = lean_ctor_get(x_31, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_31);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_296 = !lean_is_exclusive(x_26);
if (x_296 == 0)
{
return x_26;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_26, 0);
x_298 = lean_ctor_get(x_26, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_26);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_19);
if (x_300 == 0)
{
return x_19;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_19, 0);
x_302 = lean_ctor_get(x_19, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_19);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_16);
if (x_304 == 0)
{
return x_16;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_16, 0);
x_306 = lean_ctor_get(x_16, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_16);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_10);
if (x_308 == 0)
{
return x_10;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_10, 0);
x_310 = lean_ctor_get(x_10, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_10);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("revert", 6);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_MVarId_revert___closed__2;
x_11 = lean_box(x_3);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lambda__2___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
x_13 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_revert___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_MVarId_revert(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_revert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_revert(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4);
l_Lean_MVarId_revert___lambda__2___closed__1 = _init_l_Lean_MVarId_revert___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__1);
l_Lean_MVarId_revert___lambda__2___closed__2 = _init_l_Lean_MVarId_revert___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__2);
l_Lean_MVarId_revert___lambda__2___closed__3 = _init_l_Lean_MVarId_revert___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__3);
l_Lean_MVarId_revert___lambda__2___closed__4 = _init_l_Lean_MVarId_revert___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__4);
l_Lean_MVarId_revert___closed__1 = _init_l_Lean_MVarId_revert___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___closed__1);
l_Lean_MVarId_revert___closed__2 = _init_l_Lean_MVarId_revert___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
