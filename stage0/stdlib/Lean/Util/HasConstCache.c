// Lean compiler output
// Module: Lean.Util.HasConstCache
// Imports: Lean.Expr Std.Data.HashMap.Raw
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
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_HasConstCache_containsUnsafe_cache___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_HasConstCache_containsUnsafe_cache___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_HasConstCache_containsUnsafe_cache___spec__2(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___rarg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_HasConstCache_containsUnsafe_cache___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_HasConstCache_containsUnsafe_cache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_HasConstCache_containsUnsafe_cache___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_HasConstCache_containsUnsafe_cache___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_HasConstCache_containsUnsafe_cache___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_box(x_2);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_ptr_addr(x_1);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(x_1, x_2, x_16);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = lean_box(x_2);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_16);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_array_get_size(x_12);
x_14 = l_Lean_Expr_hash(x_1);
x_15 = 32;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = 16;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = 1;
x_24 = lean_usize_sub(x_22, x_23);
x_25 = lean_usize_land(x_21, x_24);
x_26 = lean_array_uget(x_12, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_30 = lean_box(x_2);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_26);
x_32 = lean_array_uset(x_12, x_25, x_31);
x_33 = lean_unsigned_to_nat(4u);
x_34 = lean_nat_mul(x_29, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_HasConstCache_containsUnsafe_cache___spec__2(x_32);
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_29);
x_40 = lean_box(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_29);
x_42 = lean_box(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_box(0);
x_45 = lean_array_uset(x_12, x_25, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(x_1, x_2, x_26);
x_47 = lean_array_uset(x_45, x_25, x_46);
lean_ctor_set(x_3, 1, x_47);
x_48 = lean_box(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_array_get_size(x_51);
x_53 = l_Lean_Expr_hash(x_1);
x_54 = 32;
x_55 = lean_uint64_shift_right(x_53, x_54);
x_56 = lean_uint64_xor(x_53, x_55);
x_57 = 16;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_62 = 1;
x_63 = lean_usize_sub(x_61, x_62);
x_64 = lean_usize_land(x_60, x_63);
x_65 = lean_array_uget(x_51, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_50, x_67);
lean_dec(x_50);
x_69 = lean_box(x_2);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_65);
x_71 = lean_array_uset(x_51, x_64, x_70);
x_72 = lean_unsigned_to_nat(4u);
x_73 = lean_nat_mul(x_68, x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = lean_nat_div(x_73, x_74);
lean_dec(x_73);
x_76 = lean_array_get_size(x_71);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_HasConstCache_containsUnsafe_cache___spec__2(x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_box(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_68);
lean_ctor_set(x_82, 1, x_71);
x_83 = lean_box(x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_box(0);
x_86 = lean_array_uset(x_51, x_64, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(x_1, x_2, x_65);
x_88 = lean_array_uset(x_86, x_64, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_50);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_box(x_2);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HasConstCache_containsUnsafe_cache___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_HasConstCache_containsUnsafe_cache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_HasConstCache_containsUnsafe_cache___spec__5(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HasConstCache_containsUnsafe_cache(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
x_90 = lean_array_get_size(x_89);
lean_dec(x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_nat_dec_lt(x_91, x_90);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_4 = x_93;
goto block_88;
}
else
{
lean_object* x_94; lean_object* x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_94 = lean_ctor_get(x_3, 1);
lean_inc(x_94);
x_95 = lean_array_get_size(x_94);
x_96 = l_Lean_Expr_hash(x_2);
x_97 = 32;
x_98 = lean_uint64_shift_right(x_96, x_97);
x_99 = lean_uint64_xor(x_96, x_98);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_94, x_107);
lean_dec(x_94);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3(x_2, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_box(0);
x_4 = x_110;
goto block_88;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
block_88:
{
lean_dec(x_4);
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1(x_1, x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = l_Lean_HasConstCache_containsUnsafe(x_1, x_9, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_HasConstCache_containsUnsafe(x_1, x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unbox(x_16);
lean_dec(x_16);
x_19 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_18, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_unbox(x_12);
lean_dec(x_12);
x_22 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_21, x_20);
return x_22;
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = l_Lean_HasConstCache_containsUnsafe(x_1, x_23, x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_HasConstCache_containsUnsafe(x_1, x_24, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
x_33 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_32, x_31);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_unbox(x_26);
lean_dec(x_26);
x_36 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_35, x_34);
return x_36;
}
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = l_Lean_HasConstCache_containsUnsafe(x_1, x_37, x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_40);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_HasConstCache_containsUnsafe(x_1, x_38, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_46, x_45);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_38);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_unbox(x_40);
lean_dec(x_40);
x_50 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_49, x_48);
return x_50;
}
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
x_54 = l_Lean_HasConstCache_containsUnsafe(x_1, x_51, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_HasConstCache_containsUnsafe(x_1, x_52, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
lean_dec(x_59);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_HasConstCache_containsUnsafe(x_1, x_53, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_66 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_65, x_64);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
lean_dec(x_53);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_unbox(x_59);
lean_dec(x_59);
x_69 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_68, x_67);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
lean_dec(x_53);
lean_dec(x_52);
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
lean_dec(x_54);
x_71 = lean_unbox(x_55);
lean_dec(x_55);
x_72 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_71, x_70);
return x_72;
}
}
case 10:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
x_74 = l_Lean_HasConstCache_containsUnsafe(x_1, x_73, x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
x_78 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_77, x_76);
return x_78;
}
case 11:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = l_Lean_HasConstCache_containsUnsafe(x_1, x_79, x_3);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_84 = l_Lean_HasConstCache_containsUnsafe_cache___rarg(x_2, x_83, x_82);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_3);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_HasConstCache_containsUnsafe___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_HasConstCache_containsUnsafe___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_HasConstCache_containsUnsafe___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HasConstCache_containsUnsafe(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
