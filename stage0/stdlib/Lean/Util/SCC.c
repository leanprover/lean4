// Lean compiler output
// Module: Lean.Util.SCC
// Imports: Std.Data.HashMap.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_SCC_scc___spec__1(lean_object*);
static lean_object* l_Lean_SCC_scc___rarg___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SCC_scc(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object*);
static lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_SCC_scc___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object*);
static lean_object* l_Lean_SCC_scc___rarg___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_SCC_scc___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SCC_scc___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_array_get_size(x_7);
lean_inc(x_3);
x_10 = lean_apply_1(x_2, x_3);
x_11 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_7, x_22);
lean_dec(x_7);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_25);
return x_5;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_array_get_size(x_27);
lean_inc(x_3);
x_29 = lean_apply_1(x_2, x_3);
x_30 = lean_unbox_uint64(x_29);
lean_dec(x_29);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_27, x_41);
lean_dec(x_27);
x_43 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = 1;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_array_get_size(x_17);
lean_inc(x_2);
lean_inc(x_3);
x_19 = lean_apply_1(x_2, x_3);
x_20 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_17, x_31);
lean_inc(x_32);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_1);
x_34 = lean_nat_add(x_16, x_10);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_14);
lean_ctor_set(x_35, 2, x_32);
x_36 = lean_array_uset(x_17, x_31, x_35);
x_37 = lean_unsigned_to_nat(4u);
x_38 = lean_nat_mul(x_34, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_div(x_38, x_39);
lean_dec(x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_le(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_36);
lean_ctor_set(x_8, 1, x_43);
lean_ctor_set(x_8, 0, x_34);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
lean_ctor_set(x_8, 1, x_36);
lean_ctor_set(x_8, 0, x_34);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = lean_array_uset(x_17, x_31, x_48);
x_50 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_14, x_32);
x_51 = lean_array_uset(x_49, x_31, x_50);
lean_ctor_set(x_8, 1, x_51);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_54 = lean_ctor_get(x_8, 0);
x_55 = lean_ctor_get(x_8, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_8);
x_56 = lean_array_get_size(x_55);
lean_inc(x_2);
lean_inc(x_3);
x_57 = lean_apply_1(x_2, x_3);
x_58 = lean_unbox_uint64(x_57);
lean_dec(x_57);
x_59 = 32;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = 16;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_67 = 1;
x_68 = lean_usize_sub(x_66, x_67);
x_69 = lean_usize_land(x_65, x_68);
x_70 = lean_array_uget(x_55, x_69);
lean_inc(x_70);
lean_inc(x_3);
lean_inc(x_1);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_1);
x_72 = lean_nat_add(x_54, x_10);
lean_dec(x_54);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_3);
lean_ctor_set(x_73, 1, x_14);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_55, x_69, x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_nat_mul(x_72, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_4, 2, x_82);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_4);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_74);
lean_ctor_set(x_4, 2, x_85);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_4);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_2);
x_88 = lean_box(0);
x_89 = lean_array_uset(x_55, x_69, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_14, x_70);
x_91 = lean_array_uset(x_89, x_69, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_54);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_4, 2, x_92);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; uint8_t x_123; 
x_95 = lean_ctor_get(x_4, 0);
x_96 = lean_ctor_get(x_4, 1);
x_97 = lean_ctor_get(x_4, 2);
x_98 = lean_ctor_get(x_4, 3);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_4);
lean_inc(x_3);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_95);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_96, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_96);
x_103 = 1;
lean_inc(x_102);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_103);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
x_108 = lean_array_get_size(x_106);
lean_inc(x_2);
lean_inc(x_3);
x_109 = lean_apply_1(x_2, x_3);
x_110 = lean_unbox_uint64(x_109);
lean_dec(x_109);
x_111 = 32;
x_112 = lean_uint64_shift_right(x_110, x_111);
x_113 = lean_uint64_xor(x_110, x_112);
x_114 = 16;
x_115 = lean_uint64_shift_right(x_113, x_114);
x_116 = lean_uint64_xor(x_113, x_115);
x_117 = lean_uint64_to_usize(x_116);
x_118 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_119 = 1;
x_120 = lean_usize_sub(x_118, x_119);
x_121 = lean_usize_land(x_117, x_120);
x_122 = lean_array_uget(x_106, x_121);
lean_inc(x_122);
lean_inc(x_3);
lean_inc(x_1);
x_123 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_1);
x_124 = lean_nat_add(x_105, x_100);
lean_dec(x_105);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_3);
lean_ctor_set(x_125, 1, x_104);
lean_ctor_set(x_125, 2, x_122);
x_126 = lean_array_uset(x_106, x_121, x_125);
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_mul(x_124, x_127);
x_129 = lean_unsigned_to_nat(3u);
x_130 = lean_nat_div(x_128, x_129);
lean_dec(x_128);
x_131 = lean_array_get_size(x_126);
x_132 = lean_nat_dec_le(x_130, x_131);
lean_dec(x_131);
lean_dec(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_126);
if (lean_is_scalar(x_107)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_107;
}
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_99);
lean_ctor_set(x_135, 1, x_101);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_98);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
if (lean_is_scalar(x_107)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_107;
}
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_126);
x_139 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_139, 0, x_99);
lean_ctor_set(x_139, 1, x_101);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_98);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_2);
x_142 = lean_box(0);
x_143 = lean_array_uset(x_106, x_121, x_142);
x_144 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_104, x_122);
x_145 = lean_array_uset(x_143, x_121, x_144);
if (lean_is_scalar(x_107)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_107;
}
lean_ctor_set(x_146, 0, x_105);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_99);
lean_ctor_set(x_147, 1, x_101);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_98);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_inc(x_2);
lean_inc(x_3);
x_11 = lean_apply_1(x_2, x_3);
x_12 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_7, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_apply_1(x_4, x_31);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_24);
x_37 = lean_array_uset(x_9, x_23, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_37);
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_35);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_array_uset(x_9, x_23, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_32, x_24);
x_52 = lean_array_uset(x_50, x_23, x_51);
lean_ctor_set(x_7, 1, x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_7);
x_55 = lean_ctor_get(x_25, 0);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_apply_1(x_4, x_55);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_1);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_8, x_58);
lean_dec(x_8);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_24);
x_61 = lean_array_uset(x_9, x_23, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_nat_mul(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_5, 2, x_69);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_5, 2, x_72);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_5);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_array_uset(x_9, x_23, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_56, x_24);
x_78 = lean_array_uset(x_76, x_23, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_5, 2, x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_82 = lean_ctor_get(x_5, 2);
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 3);
lean_inc(x_85);
lean_inc(x_82);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
lean_inc(x_2);
lean_inc(x_3);
x_89 = lean_apply_1(x_2, x_3);
x_90 = lean_unbox_uint64(x_89);
lean_dec(x_89);
x_91 = 32;
x_92 = lean_uint64_shift_right(x_90, x_91);
x_93 = lean_uint64_xor(x_90, x_92);
x_94 = 16;
x_95 = lean_uint64_shift_right(x_93, x_94);
x_96 = lean_uint64_xor(x_93, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_99 = 1;
x_100 = lean_usize_sub(x_98, x_99);
x_101 = lean_usize_land(x_97, x_100);
x_102 = lean_array_uget(x_87, x_101);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_103 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_84);
lean_ctor_set(x_104, 2, x_82);
lean_ctor_set(x_104, 3, x_85);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_107 = x_82;
} else {
 lean_dec_ref(x_82);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_apply_1(x_4, x_108);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_102);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_1);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_86, x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_102);
x_114 = lean_array_uset(x_87, x_101, x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_mul(x_112, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_div(x_116, x_117);
lean_dec(x_116);
x_119 = lean_array_get_size(x_114);
x_120 = lean_nat_dec_le(x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_114);
if (lean_is_scalar(x_107)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_107;
}
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_83);
lean_ctor_set(x_123, 1, x_84);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_85);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_2);
if (lean_is_scalar(x_107)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_107;
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_114);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_83);
lean_ctor_set(x_127, 1, x_84);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_85);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_130 = lean_box(0);
x_131 = lean_array_uset(x_87, x_101, x_130);
x_132 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_109, x_102);
x_133 = lean_array_uset(x_131, x_101, x_132);
if (lean_is_scalar(x_107)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_107;
}
lean_ctor_set(x_134, 0, x_86);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_83);
lean_ctor_set(x_135, 1, x_84);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_85);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_inc(x_2);
lean_inc(x_3);
x_11 = lean_apply_1(x_2, x_3);
x_12 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_7, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_apply_1(x_4, x_31);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_24);
x_37 = lean_array_uset(x_9, x_23, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_37);
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_35);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_array_uset(x_9, x_23, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_32, x_24);
x_52 = lean_array_uset(x_50, x_23, x_51);
lean_ctor_set(x_7, 1, x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_7);
x_55 = lean_ctor_get(x_25, 0);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_apply_1(x_4, x_55);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_1);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_8, x_58);
lean_dec(x_8);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_24);
x_61 = lean_array_uset(x_9, x_23, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_nat_mul(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_5, 2, x_69);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_5, 2, x_72);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_5);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_array_uset(x_9, x_23, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_56, x_24);
x_78 = lean_array_uset(x_76, x_23, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_5, 2, x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_82 = lean_ctor_get(x_5, 2);
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 3);
lean_inc(x_85);
lean_inc(x_82);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
lean_inc(x_2);
lean_inc(x_3);
x_89 = lean_apply_1(x_2, x_3);
x_90 = lean_unbox_uint64(x_89);
lean_dec(x_89);
x_91 = 32;
x_92 = lean_uint64_shift_right(x_90, x_91);
x_93 = lean_uint64_xor(x_90, x_92);
x_94 = 16;
x_95 = lean_uint64_shift_right(x_93, x_94);
x_96 = lean_uint64_xor(x_93, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_99 = 1;
x_100 = lean_usize_sub(x_98, x_99);
x_101 = lean_usize_land(x_97, x_100);
x_102 = lean_array_uget(x_87, x_101);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_103 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_84);
lean_ctor_set(x_104, 2, x_82);
lean_ctor_set(x_104, 3, x_85);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_107 = x_82;
} else {
 lean_dec_ref(x_82);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_apply_1(x_4, x_108);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_102);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_1);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_86, x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_102);
x_114 = lean_array_uset(x_87, x_101, x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_mul(x_112, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_div(x_116, x_117);
lean_dec(x_116);
x_119 = lean_array_get_size(x_114);
x_120 = lean_nat_dec_le(x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_114);
if (lean_is_scalar(x_107)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_107;
}
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_83);
lean_ctor_set(x_123, 1, x_84);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_85);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_2);
if (lean_is_scalar(x_107)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_107;
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_114);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_83);
lean_ctor_set(x_127, 1, x_84);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_85);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_130 = lean_box(0);
x_131 = lean_array_uset(x_87, x_101, x_130);
x_132 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_109, x_102);
x_133 = lean_array_uset(x_131, x_101, x_132);
if (lean_is_scalar(x_107)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_107;
}
lean_ctor_set(x_134, 0, x_86);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_83);
lean_ctor_set(x_135, 1, x_84);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_85);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_6);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
x_6 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_inc(x_2);
lean_inc(x_3);
x_11 = lean_apply_1(x_2, x_3);
x_12 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_7, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_apply_1(x_4, x_31);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_24);
x_37 = lean_array_uset(x_9, x_23, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_37);
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_35);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_array_uset(x_9, x_23, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_32, x_24);
x_52 = lean_array_uset(x_50, x_23, x_51);
lean_ctor_set(x_7, 1, x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_7);
x_55 = lean_ctor_get(x_25, 0);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_apply_1(x_4, x_55);
lean_inc(x_24);
lean_inc(x_3);
lean_inc(x_1);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_24);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_1);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_8, x_58);
lean_dec(x_8);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_24);
x_61 = lean_array_uset(x_9, x_23, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_nat_mul(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_5, 2, x_69);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_5, 2, x_72);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_5);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_array_uset(x_9, x_23, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_56, x_24);
x_78 = lean_array_uset(x_76, x_23, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_5, 2, x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_82 = lean_ctor_get(x_5, 2);
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 3);
lean_inc(x_85);
lean_inc(x_82);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
lean_inc(x_2);
lean_inc(x_3);
x_89 = lean_apply_1(x_2, x_3);
x_90 = lean_unbox_uint64(x_89);
lean_dec(x_89);
x_91 = 32;
x_92 = lean_uint64_shift_right(x_90, x_91);
x_93 = lean_uint64_xor(x_90, x_92);
x_94 = 16;
x_95 = lean_uint64_shift_right(x_93, x_94);
x_96 = lean_uint64_xor(x_93, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_99 = 1;
x_100 = lean_usize_sub(x_98, x_99);
x_101 = lean_usize_land(x_97, x_100);
x_102 = lean_array_uget(x_87, x_101);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_103 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_1, x_3, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_84);
lean_ctor_set(x_104, 2, x_82);
lean_ctor_set(x_104, 3, x_85);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_107 = x_82;
} else {
 lean_dec_ref(x_82);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_apply_1(x_4, x_108);
lean_inc(x_102);
lean_inc(x_3);
lean_inc(x_1);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_1, x_3, x_102);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_1);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_86, x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_102);
x_114 = lean_array_uset(x_87, x_101, x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_mul(x_112, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_div(x_116, x_117);
lean_dec(x_116);
x_119 = lean_array_get_size(x_114);
x_120 = lean_nat_dec_le(x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_2, x_114);
if (lean_is_scalar(x_107)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_107;
}
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_83);
lean_ctor_set(x_123, 1, x_84);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_85);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_2);
if (lean_is_scalar(x_107)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_107;
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_114);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_83);
lean_ctor_set(x_127, 1, x_84);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_85);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_130 = lean_box(0);
x_131 = lean_array_uset(x_87, x_101, x_130);
x_132 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_1, x_3, x_109, x_102);
x_133 = lean_array_uset(x_131, x_101, x_132);
if (lean_is_scalar(x_107)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_107;
}
lean_ctor_set(x_134, 0, x_86);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_83);
lean_ctor_set(x_135, 1, x_84);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_85);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
return x_2;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_nat_dec_lt(x_16, x_18);
if (x_19 == 0)
{
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_dec(x_18);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_nat_dec_lt(x_16, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_2, 1, x_23);
return x_2;
}
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_28 = x_1;
} else {
 lean_dec_ref(x_1);
 x_28 = lean_box(0);
}
x_29 = lean_nat_dec_lt(x_26, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_26);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_25);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___spec__1___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_6, 3, x_11);
lean_ctor_set(x_6, 0, x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
lean_inc(x_22);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(x_1, x_2, x_22, x_24, x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_inc(x_22);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_29 = lean_apply_2(x_1, x_3, x_22);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_free_object(x_25);
{
lean_object* _tmp_3 = x_23;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_27;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 3);
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_27, 3, x_35);
lean_ctor_set(x_27, 0, x_23);
x_36 = lean_box(0);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_27, 1);
x_38 = lean_ctor_get(x_27, 2);
x_39 = lean_ctor_get(x_27, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_box(0);
lean_ctor_set(x_25, 1, x_41);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
lean_inc(x_22);
lean_ctor_set(x_4, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_44 = lean_apply_2(x_1, x_3, x_22);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
{
lean_object* _tmp_3 = x_23;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_43;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 3);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_49);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_4);
x_57 = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
lean_inc(x_55);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___spec__1___rarg(x_1, x_2, x_55, x_57, x_6);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
lean_inc(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_5);
lean_inc(x_1);
lean_inc(x_3);
x_62 = lean_apply_2(x_1, x_3, x_55);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_60);
x_4 = x_56;
x_5 = x_61;
x_6 = x_59;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_67);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 4, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_60;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___rarg(x_1, x_2, x_3, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_9, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(x_1, x_2, x_3, x_9, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(x_1, x_2, x_4, x_20, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_5 = x_10;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
x_24 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_dec(x_12);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_5 = x_10;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg(x_1, x_2, x_4, x_13, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_5 = x_10;
x_6 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Util_SCC_0__Lean_SCC_push___rarg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_4);
x_8 = lean_apply_1(x_3, x_4);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_List_forM___at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; 
lean_free_object(x_11);
x_19 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(x_1, x_2, x_4, x_14);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___rarg(x_1, x_2, x_4, x_21);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Util_SCC_0__Lean_SCC_sccAux___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_SCC_scc___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg(x_1, x_2, x_8, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___rarg(x_1, x_2, x_3, x_8, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_4 = x_9;
x_5 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_SCC_scc___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at_Lean_SCC_scc___spec__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_SCC_scc___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_SCC_scc___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SCC_scc___rarg___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SCC_scc___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_SCC_scc___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_SCC_scc___rarg___closed__3;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_5);
x_9 = l_List_forM___at_Lean_SCC_scc___spec__1___rarg(x_1, x_2, x_4, x_3, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_List_reverse___rarg(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SCC_scc___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SCC(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1);
l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1);
l_Lean_SCC_scc___rarg___closed__1 = _init_l_Lean_SCC_scc___rarg___closed__1();
lean_mark_persistent(l_Lean_SCC_scc___rarg___closed__1);
l_Lean_SCC_scc___rarg___closed__2 = _init_l_Lean_SCC_scc___rarg___closed__2();
lean_mark_persistent(l_Lean_SCC_scc___rarg___closed__2);
l_Lean_SCC_scc___rarg___closed__3 = _init_l_Lean_SCC_scc___rarg___closed__3();
lean_mark_persistent(l_Lean_SCC_scc___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
