// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: Init Lean.Expr Lean.Environment
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
lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t l_Lean_Expr_FoldConstsImpl_cacheSize;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight_match__1(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants___closed__1;
lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight___boxed__const__1;
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight___lambda__1(lean_object*, lean_object*, uint32_t);
extern lean_object* l_Lean_Expr_FindImpl_initCache___closed__1;
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts___boxed(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
extern lean_object* l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*);
lean_object* l_Lean_getMaxHeight_match__2(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts___rarg(lean_object*, lean_object*);
static size_t _init_l_Lean_Expr_FoldConstsImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ptr_addr(x_1);
x_5 = x_2 == 0 ? 0 : x_4 % x_2;
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_4;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_array_uset(x_6, x_5, x_1);
lean_ctor_set(x_3, 0, x_14);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_18 = lean_array_uset(x_6, x_5, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_FoldConstsImpl_visited(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_8, x_10, x_11, x_13);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_6, x_15, x_16, x_18);
return x_19;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_3, x_20, x_21, x_22, x_24);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_4(x_2, x_26, x_27, x_28, x_30);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_5(x_5, x_32, x_33, x_34, x_35, x_37);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_3(x_4, x_39, x_40, x_42);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_4(x_7, x_44, x_45, x_46, x_48);
return x_49;
}
default: 
{
lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_apply_1(x_9, x_1);
return x_50;
}
}
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold_visit_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; uint8_t x_64; 
x_58 = lean_ptr_addr(x_3);
x_59 = x_2 == 0 ? 0 : x_58 % x_2;
x_60 = lean_ctor_get(x_5, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_array_uget(x_60, x_59);
x_63 = lean_ptr_addr(x_62);
lean_dec(x_62);
x_64 = x_63 == x_58;
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_5);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_5, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_5, 0);
lean_dec(x_67);
lean_inc(x_3);
x_68 = lean_array_uset(x_60, x_59, x_3);
lean_ctor_set(x_5, 0, x_68);
x_69 = 0;
x_6 = x_69;
x_7 = x_5;
goto block_57;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_5);
lean_inc(x_3);
x_70 = lean_array_uset(x_60, x_59, x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
x_72 = 0;
x_6 = x_72;
x_7 = x_71;
goto block_57;
}
}
else
{
uint8_t x_73; 
lean_dec(x_61);
lean_dec(x_60);
x_73 = 1;
x_6 = x_73;
x_7 = x_5;
goto block_57;
}
block_57:
{
if (x_6 == 0)
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_10, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_8);
x_15 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
lean_ctor_set(x_7, 1, x_15);
x_16 = lean_apply_2(x_1, x_8, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_inc(x_8);
x_18 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_apply_2(x_1, x_8, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_dec(x_3);
lean_inc(x_1);
x_25 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_23, x_4, x_7);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_3 = x_24;
x_4 = x_26;
x_5 = x_27;
goto _start;
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_1);
x_31 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_29, x_4, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_3 = x_30;
x_4 = x_32;
x_5 = x_33;
goto _start;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_dec(x_3);
lean_inc(x_1);
x_37 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_35, x_4, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_3 = x_36;
x_4 = x_38;
x_5 = x_39;
goto _start;
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 3);
lean_inc(x_43);
lean_dec(x_3);
lean_inc(x_1);
x_44 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_41, x_4, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_42, x_45, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_3 = x_43;
x_4 = x_48;
x_5 = x_49;
goto _start;
}
case 10:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_dec(x_3);
x_3 = x_51;
x_5 = x_7;
goto _start;
}
case 11:
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
lean_dec(x_3);
x_3 = x_53;
x_5 = x_7;
goto _start;
}
default: 
{
lean_object* x_55; 
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FindImpl_initCache___closed__1;
x_2 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 8192;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_4, x_1, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_foldConsts___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Expr_foldConsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_foldConsts___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Expr_foldConsts___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_foldConsts___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_foldConsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_foldConsts(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstants___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstants___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Expr_getUsedConstants(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = 8192;
x_3 = l_Lean_Expr_getUsedConstants___closed__1;
x_4 = l_Array_empty___closed__1;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_getMaxHeight_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get_uint32(x_1, 0);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_getMaxHeight_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getMaxHeight_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_getMaxHeight_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_getMaxHeight_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getMaxHeight_match__2___rarg), 3, 0);
return x_2;
}
}
uint32_t l_Lean_getMaxHeight___lambda__1(lean_object* x_1, lean_object* x_2, uint32_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 2)
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint32(x_7, 0);
lean_dec(x_7);
x_9 = x_3 < x_8;
if (x_9 == 0)
{
return x_3;
}
else
{
return x_8;
}
}
else
{
lean_dec(x_7);
return x_3;
}
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
static lean_object* _init_l_Lean_getMaxHeight___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l_Lean_getMaxHeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lean_getMaxHeight___lambda__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_getMaxHeight___boxed__const__1;
x_7 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_4, x_2, x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = l_Lean_getMaxHeight___lambda__1(x_1, x_2, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_FoldConsts(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FoldConstsImpl_cacheSize = _init_l_Lean_Expr_FoldConstsImpl_cacheSize();
l_Lean_Expr_FoldConstsImpl_initCache___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache___closed__1);
l_Lean_Expr_FoldConstsImpl_initCache = _init_l_Lean_Expr_FoldConstsImpl_initCache();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache);
l_Lean_Expr_getUsedConstants___closed__1 = _init_l_Lean_Expr_getUsedConstants___closed__1();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__1);
l_Lean_getMaxHeight___boxed__const__1 = _init_l_Lean_getMaxHeight___boxed__const__1();
lean_mark_persistent(l_Lean_getMaxHeight___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
