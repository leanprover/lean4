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
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_FoldConstsImpl_cacheSize;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*);
static lean_object* l_Lean_Expr_getUsedConstants___closed__1;
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lambda__1(lean_object*, lean_object*, uint32_t);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
static lean_object* l_Lean_Expr_getUsedConstants___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__2;
lean_object* l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___boxed(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___rarg(lean_object*, lean_object*);
static size_t _init_l_Lean_Expr_FoldConstsImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ptr_addr(x_1);
x_5 = x_2 == 0 ? x_4 : x_4 % x_2;
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
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_FoldConstsImpl_visited(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; uint8_t x_88; 
x_82 = lean_ptr_addr(x_3);
x_83 = x_2 == 0 ? x_82 : x_82 % x_2;
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 1);
lean_inc(x_85);
x_86 = lean_array_uget(x_84, x_83);
x_87 = lean_ptr_addr(x_86);
lean_dec(x_86);
x_88 = x_87 == x_82;
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_5);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_5, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_5, 0);
lean_dec(x_91);
lean_inc(x_3);
x_92 = lean_array_uset(x_84, x_83, x_3);
lean_ctor_set(x_5, 0, x_92);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
x_6 = x_95;
goto block_81;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_5);
lean_inc(x_3);
x_96 = lean_array_uset(x_84, x_83, x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_85);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
x_6 = x_100;
goto block_81;
}
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
lean_dec(x_84);
x_101 = 1;
x_102 = lean_box(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_5);
x_6 = x_103;
goto block_81;
}
block_81:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
switch (lean_obj_tag(x_3)) {
case 4:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_14, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
lean_inc(x_12);
x_19 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_14, x_12);
lean_ctor_set(x_10, 1, x_19);
x_20 = lean_apply_2(x_1, x_12, x_4);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_inc(x_12);
x_21 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_14, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_apply_2(x_1, x_12, x_4);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_27, x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
lean_inc(x_25);
x_30 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_27, x_25);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_apply_2(x_1, x_25, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
lean_inc(x_1);
x_38 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_36, x_4, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_3 = x_37;
x_4 = x_39;
x_5 = x_40;
goto _start;
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
lean_dec(x_3);
lean_inc(x_1);
x_45 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_43, x_4, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_3 = x_44;
x_4 = x_46;
x_5 = x_47;
goto _start;
}
case 7:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 2);
lean_inc(x_51);
lean_dec(x_3);
lean_inc(x_1);
x_52 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_50, x_4, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_3 = x_51;
x_4 = x_53;
x_5 = x_54;
goto _start;
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 3);
lean_inc(x_59);
lean_dec(x_3);
lean_inc(x_1);
x_60 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_57, x_4, x_56);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_1);
x_63 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_58, x_61, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_3 = x_59;
x_4 = x_64;
x_5 = x_65;
goto _start;
}
case 10:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
lean_dec(x_6);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
lean_dec(x_3);
x_3 = x_68;
x_5 = x_67;
goto _start;
}
case 11:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_6, 1);
lean_inc(x_70);
lean_dec(x_6);
x_71 = lean_ctor_get(x_3, 2);
lean_inc(x_71);
lean_dec(x_3);
x_3 = x_71;
x_5 = x_70;
goto _start;
}
default: 
{
uint8_t x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_6);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_6, 0);
lean_dec(x_74);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_6);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_6, 0);
lean_dec(x_78);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_4);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
x_2 = l_Lean_Expr_FoldConstsImpl_initCache___closed__2;
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
x_1 = l_Lean_Expr_FoldConstsImpl_initCache___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_foldConsts___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_foldConsts___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldConsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_foldConsts(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstants___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstants___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = 8192;
x_3 = l_Lean_Expr_getUsedConstants___closed__2;
x_4 = l_Lean_Expr_getUsedConstants___closed__1;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lambda__1(lean_object* x_1, lean_object* x_2, uint32_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_getMaxHeight(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(lean_object* w) {
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
l_Lean_Expr_FoldConstsImpl_initCache___closed__2 = _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache___closed__2);
l_Lean_Expr_FoldConstsImpl_initCache___closed__3 = _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache___closed__3);
l_Lean_Expr_FoldConstsImpl_initCache = _init_l_Lean_Expr_FoldConstsImpl_initCache();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache);
l_Lean_Expr_getUsedConstants___closed__1 = _init_l_Lean_Expr_getUsedConstants___closed__1();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__1);
l_Lean_Expr_getUsedConstants___closed__2 = _init_l_Lean_Expr_getUsedConstants___closed__2();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__2);
l_Lean_getMaxHeight___boxed__const__1 = _init_l_Lean_getMaxHeight___boxed__const__1();
lean_mark_persistent(l_Lean_getMaxHeight___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
