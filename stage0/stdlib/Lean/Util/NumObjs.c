// Lean compiler output
// Module: Lean.Util.NumObjs
// Imports: Lean.Expr Lean.Util.PtrSet
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
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs_unsafe__1(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_NumObjs_visit___spec__4___at_Lean_Expr_NumObjs_visit___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_NumObjs_visit___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_NumObjs_main___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_NumObjs_visit___spec__3(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_NumObjs_main___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_NumObjs_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_NumObjs_visit___spec__4___at_Lean_Expr_NumObjs_visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_NumObjs_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_NumObjs_visit___spec__4___at_Lean_Expr_NumObjs_visit___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_NumObjs_visit___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; uint8_t x_55; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_array_get_size(x_36);
x_39 = lean_ptr_addr(x_1);
x_40 = lean_usize_to_uint64(x_39);
x_41 = 11;
x_42 = lean_uint64_mix_hash(x_40, x_41);
x_43 = 32;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = 16;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = lean_uint64_to_usize(x_48);
x_50 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_51 = 1;
x_52 = lean_usize_sub(x_50, x_51);
x_53 = lean_usize_land(x_49, x_52);
x_54 = lean_array_uget(x_36, x_53);
lean_dec(x_36);
x_55 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_free_object(x_34);
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_58, x_59);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
x_64 = lean_array_get_size(x_63);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = lean_usize_sub(x_65, x_51);
x_67 = lean_usize_land(x_49, x_66);
x_68 = lean_array_uget(x_63, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_70 = lean_nat_add(x_62, x_59);
lean_dec(x_62);
x_71 = lean_box(0);
lean_inc(x_1);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_68);
x_73 = lean_array_uset(x_63, x_67, x_72);
x_74 = lean_unsigned_to_nat(4u);
x_75 = lean_nat_mul(x_70, x_74);
x_76 = lean_unsigned_to_nat(3u);
x_77 = lean_nat_div(x_75, x_76);
lean_dec(x_75);
x_78 = lean_array_get_size(x_73);
x_79 = lean_nat_dec_le(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(x_73);
lean_ctor_set(x_57, 1, x_80);
lean_ctor_set(x_57, 0, x_70);
lean_ctor_set(x_2, 1, x_60);
x_3 = x_2;
goto block_33;
}
else
{
lean_ctor_set(x_57, 1, x_73);
lean_ctor_set(x_57, 0, x_70);
lean_ctor_set(x_2, 1, x_60);
x_3 = x_2;
goto block_33;
}
}
else
{
lean_dec(x_68);
lean_ctor_set(x_2, 1, x_60);
x_3 = x_2;
goto block_33;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_57, 0);
x_82 = lean_ctor_get(x_57, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_57);
x_83 = lean_array_get_size(x_82);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = lean_usize_sub(x_84, x_51);
x_86 = lean_usize_land(x_49, x_85);
x_87 = lean_array_uget(x_82, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_nat_add(x_81, x_59);
lean_dec(x_81);
x_90 = lean_box(0);
lean_inc(x_1);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_87);
x_92 = lean_array_uset(x_82, x_86, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_89, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_100);
x_3 = x_2;
goto block_33;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_101);
x_3 = x_2;
goto block_33;
}
}
else
{
lean_object* x_102; 
lean_dec(x_87);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_81);
lean_ctor_set(x_102, 1, x_82);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_102);
x_3 = x_2;
goto block_33;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; size_t x_113; lean_object* x_114; uint8_t x_115; 
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_2);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_104, x_105);
lean_dec(x_104);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_get_size(x_108);
x_111 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_112 = lean_usize_sub(x_111, x_51);
x_113 = lean_usize_land(x_49, x_112);
x_114 = lean_array_uget(x_108, x_113);
x_115 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_116 = lean_nat_add(x_107, x_105);
lean_dec(x_107);
x_117 = lean_box(0);
lean_inc(x_1);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_114);
x_119 = lean_array_uset(x_108, x_113, x_118);
x_120 = lean_unsigned_to_nat(4u);
x_121 = lean_nat_mul(x_116, x_120);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_div(x_121, x_122);
lean_dec(x_121);
x_124 = lean_array_get_size(x_119);
x_125 = lean_nat_dec_le(x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(x_119);
if (lean_is_scalar(x_109)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_109;
}
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_106);
x_3 = x_128;
goto block_33;
}
else
{
lean_object* x_129; lean_object* x_130; 
if (lean_is_scalar(x_109)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_109;
}
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_119);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_106);
x_3 = x_130;
goto block_33;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_114);
if (lean_is_scalar(x_109)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_109;
}
lean_ctor_set(x_131, 0, x_107);
lean_ctor_set(x_131, 1, x_108);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_106);
x_3 = x_132;
goto block_33;
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_1);
x_133 = lean_box(0);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 0, x_133);
return x_34;
}
}
else
{
lean_object* x_134; lean_object* x_135; size_t x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; size_t x_146; size_t x_147; size_t x_148; size_t x_149; size_t x_150; lean_object* x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_34, 1);
lean_inc(x_134);
lean_dec(x_34);
x_135 = lean_array_get_size(x_134);
x_136 = lean_ptr_addr(x_1);
x_137 = lean_usize_to_uint64(x_136);
x_138 = 11;
x_139 = lean_uint64_mix_hash(x_137, x_138);
x_140 = 32;
x_141 = lean_uint64_shift_right(x_139, x_140);
x_142 = lean_uint64_xor(x_139, x_141);
x_143 = 16;
x_144 = lean_uint64_shift_right(x_142, x_143);
x_145 = lean_uint64_xor(x_142, x_144);
x_146 = lean_uint64_to_usize(x_145);
x_147 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_148 = 1;
x_149 = lean_usize_sub(x_147, x_148);
x_150 = lean_usize_land(x_146, x_149);
x_151 = lean_array_uget(x_134, x_150);
lean_dec(x_134);
x_152 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; size_t x_164; lean_object* x_165; uint8_t x_166; 
x_153 = lean_ctor_get(x_2, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_155 = x_2;
} else {
 lean_dec_ref(x_2);
 x_155 = lean_box(0);
}
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_add(x_154, x_156);
lean_dec(x_154);
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_160 = x_153;
} else {
 lean_dec_ref(x_153);
 x_160 = lean_box(0);
}
x_161 = lean_array_get_size(x_159);
x_162 = lean_usize_of_nat(x_161);
lean_dec(x_161);
x_163 = lean_usize_sub(x_162, x_148);
x_164 = lean_usize_land(x_146, x_163);
x_165 = lean_array_uget(x_159, x_164);
x_166 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_167 = lean_nat_add(x_158, x_156);
lean_dec(x_158);
x_168 = lean_box(0);
lean_inc(x_1);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_165);
x_170 = lean_array_uset(x_159, x_164, x_169);
x_171 = lean_unsigned_to_nat(4u);
x_172 = lean_nat_mul(x_167, x_171);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_div(x_172, x_173);
lean_dec(x_172);
x_175 = lean_array_get_size(x_170);
x_176 = lean_nat_dec_le(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_NumObjs_visit___spec__2(x_170);
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_167);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_155)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_155;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_157);
x_3 = x_179;
goto block_33;
}
else
{
lean_object* x_180; lean_object* x_181; 
if (lean_is_scalar(x_160)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_160;
}
lean_ctor_set(x_180, 0, x_167);
lean_ctor_set(x_180, 1, x_170);
if (lean_is_scalar(x_155)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_155;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_157);
x_3 = x_181;
goto block_33;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_165);
if (lean_is_scalar(x_160)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_160;
}
lean_ctor_set(x_182, 0, x_158);
lean_ctor_set(x_182, 1, x_159);
if (lean_is_scalar(x_155)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_155;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_157);
x_3 = x_183;
goto block_33;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_1);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_2);
return x_185;
}
}
block_33:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Expr_NumObjs_visit(x_4, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Expr_NumObjs_visit(x_9, x_3);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Expr_NumObjs_visit(x_14, x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_1 = x_15;
x_2 = x_17;
goto _start;
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Expr_NumObjs_visit(x_19, x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Expr_NumObjs_visit(x_20, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_1 = x_21;
x_2 = x_25;
goto _start;
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_1 = x_27;
x_2 = x_3;
goto _start;
}
case 11:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_1 = x_29;
x_2 = x_3;
goto _start;
}
default: 
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_NumObjs_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrSet___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_NumObjs_main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Expr_NumObjs_main___closed__2;
x_3 = l_Lean_Expr_NumObjs_visit(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_NumObjs_main(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_NumObjs_main(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_NumObjs_main___closed__1 = _init_l_Lean_Expr_NumObjs_main___closed__1();
lean_mark_persistent(l_Lean_Expr_NumObjs_main___closed__1);
l_Lean_Expr_NumObjs_main___closed__2 = _init_l_Lean_Expr_NumObjs_main___closed__2();
lean_mark_persistent(l_Lean_Expr_NumObjs_main___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
