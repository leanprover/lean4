// Lean compiler output
// Module: Lean.Util.CollectLevelMVars
// Imports: Lean.Expr
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_CollectLevelMVars_main___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitLevel___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__2;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitLevel___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitExpr___spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__1;
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_CollectLevelMVars_instInhabitedState___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_CollectLevelMVars_instInhabitedState___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CollectLevelMVars_instInhabitedState___closed__3;
x_2 = l_Lean_CollectLevelMVars_instInhabitedState___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectLevelMVars_instInhabitedState___closed__5;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_level_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Level_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Level_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitLevel___spec__4(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitLevel___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitLevel___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Level_hasMVar(x_1);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_array_get_size(x_9);
x_11 = l_Lean_Level_hash(x_1);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1(x_1, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_2, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_8, x_29);
lean_dec(x_8);
x_31 = lean_box(0);
lean_inc(x_1);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_23);
x_33 = lean_array_uset(x_9, x_22, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_30, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitLevel___spec__2(x_33);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_30);
x_41 = l_Lean_CollectLevelMVars_collect(x_1, x_2);
return x_41;
}
else
{
lean_object* x_42; 
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_30);
x_42 = l_Lean_CollectLevelMVars_collect(x_1, x_2);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_2);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_8, x_43);
lean_dec(x_8);
x_45 = lean_box(0);
lean_inc(x_1);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_23);
x_47 = lean_array_uset(x_9, x_22, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_44, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitLevel___spec__2(x_47);
lean_ctor_set(x_4, 1, x_54);
lean_ctor_set(x_4, 0, x_44);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_5);
lean_ctor_set(x_55, 2, x_6);
x_56 = l_Lean_CollectLevelMVars_collect(x_1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_44);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_5);
lean_ctor_set(x_57, 2, x_6);
x_58 = l_Lean_CollectLevelMVars_collect(x_1, x_57);
return x_58;
}
}
}
else
{
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_array_get_size(x_60);
x_62 = l_Lean_Level_hash(x_1);
x_63 = 32;
x_64 = lean_uint64_shift_right(x_62, x_63);
x_65 = lean_uint64_xor(x_62, x_64);
x_66 = 16;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = 1;
x_72 = lean_usize_sub(x_70, x_71);
x_73 = lean_usize_land(x_69, x_72);
x_74 = lean_array_uget(x_60, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1(x_1, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_76 = x_2;
} else {
 lean_dec_ref(x_2);
 x_76 = lean_box(0);
}
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_59, x_77);
lean_dec(x_59);
x_79 = lean_box(0);
lean_inc(x_1);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_74);
x_81 = lean_array_uset(x_60, x_73, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_mul(x_78, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitLevel___spec__2(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_76)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_76;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_90, 2, x_6);
x_91 = l_Lean_CollectLevelMVars_collect(x_1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_81);
if (lean_is_scalar(x_76)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_76;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_5);
lean_ctor_set(x_93, 2, x_6);
x_94 = l_Lean_CollectLevelMVars_collect(x_1, x_93);
return x_94;
}
}
else
{
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_CollectLevelMVars_visitLevel(x_3, x_2);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_CollectLevelMVars_visitLevel(x_5, x_2);
x_8 = l_Lean_CollectLevelMVars_visitLevel(x_6, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_CollectLevelMVars_visitLevel(x_9, x_2);
x_12 = l_Lean_CollectLevelMVars_visitLevel(x_10, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_array_push(x_16, x_13);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_CollectLevelMVars_visitExpr___spec__4(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_CollectLevelMVars_visitExpr___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_array_get_size(x_9);
x_11 = l_Lean_Expr_hash(x_1);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_1, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_2, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_8, x_29);
lean_dec(x_8);
x_31 = lean_box(0);
lean_inc(x_1);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_23);
x_33 = lean_array_uset(x_9, x_22, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_30, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_33);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_30);
x_41 = l_Lean_CollectLevelMVars_main(x_1, x_2);
return x_41;
}
else
{
lean_object* x_42; 
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_30);
x_42 = l_Lean_CollectLevelMVars_main(x_1, x_2);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_2);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_8, x_43);
lean_dec(x_8);
x_45 = lean_box(0);
lean_inc(x_1);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_23);
x_47 = lean_array_uset(x_9, x_22, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_44, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_47);
lean_ctor_set(x_4, 1, x_54);
lean_ctor_set(x_4, 0, x_44);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_4);
lean_ctor_set(x_55, 2, x_6);
x_56 = l_Lean_CollectLevelMVars_main(x_1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_44);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_6);
x_58 = l_Lean_CollectLevelMVars_main(x_1, x_57);
return x_58;
}
}
}
else
{
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_array_get_size(x_60);
x_62 = l_Lean_Expr_hash(x_1);
x_63 = 32;
x_64 = lean_uint64_shift_right(x_62, x_63);
x_65 = lean_uint64_xor(x_62, x_64);
x_66 = 16;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = 1;
x_72 = lean_usize_sub(x_70, x_71);
x_73 = lean_usize_land(x_69, x_72);
x_74 = lean_array_uget(x_60, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_1, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_76 = x_2;
} else {
 lean_dec_ref(x_2);
 x_76 = lean_box(0);
}
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_59, x_77);
lean_dec(x_59);
x_79 = lean_box(0);
lean_inc(x_1);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_74);
x_81 = lean_array_uset(x_60, x_73, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_mul(x_78, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_76)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_76;
}
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_6);
x_91 = l_Lean_CollectLevelMVars_main(x_1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_81);
if (lean_is_scalar(x_76)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_76;
}
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_6);
x_94 = l_Lean_CollectLevelMVars_main(x_1, x_93);
return x_94;
}
}
else
{
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_CollectLevelMVars_main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_CollectLevelMVars_visitLevel(x_3, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_CollectLevelMVars_visitLevel(x_3, x_2);
return x_4;
}
case 4:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at_Lean_CollectLevelMVars_main___spec__1(x_2, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_CollectLevelMVars_visitExpr(x_7, x_2);
x_10 = l_Lean_CollectLevelMVars_visitExpr(x_8, x_9);
return x_10;
}
case 6:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_CollectLevelMVars_visitExpr(x_11, x_2);
x_14 = l_Lean_CollectLevelMVars_visitExpr(x_12, x_13);
return x_14;
}
case 7:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_CollectLevelMVars_visitExpr(x_15, x_2);
x_18 = l_Lean_CollectLevelMVars_visitExpr(x_16, x_17);
return x_18;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_CollectLevelMVars_visitExpr(x_19, x_2);
x_23 = l_Lean_CollectLevelMVars_visitExpr(x_20, x_22);
x_24 = l_Lean_CollectLevelMVars_visitExpr(x_21, x_23);
return x_24;
}
case 10:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_CollectLevelMVars_visitExpr(x_25, x_2);
return x_26;
}
case 11:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_CollectLevelMVars_visitExpr(x_27, x_2);
return x_28;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectLevelMVars_main(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLevelMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelMVars_instInhabitedState___closed__1 = _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState___closed__1);
l_Lean_CollectLevelMVars_instInhabitedState___closed__2 = _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState___closed__2);
l_Lean_CollectLevelMVars_instInhabitedState___closed__3 = _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState___closed__3);
l_Lean_CollectLevelMVars_instInhabitedState___closed__4 = _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState___closed__4);
l_Lean_CollectLevelMVars_instInhabitedState___closed__5 = _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState___closed__5);
l_Lean_CollectLevelMVars_instInhabitedState = _init_l_Lean_CollectLevelMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
