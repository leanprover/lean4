// Lean compiler output
// Module: Init.Lean.Util.FoldConsts
// Imports: Init.Control.Option Init.Lean.Expr Init.Lean.Environment
#include "runtime/lean.h"
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
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(lean_object*, size_t, lean_object*, uint32_t, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t l_Lean_Expr_FoldConstsImpl_cacheSize;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
lean_object* l_Lean_Expr_foldConsts___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__2;
extern lean_object* l_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Expr_foldConsts___boxed(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_foldConsts___rarg(lean_object*, lean_object*);
size_t _init_l_Lean_Expr_FoldConstsImpl_cacheSize() {
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
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_10, x_8);
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
x_15 = l_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
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
x_18 = l_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
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
x_25 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_23, x_4, x_7);
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
x_31 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_29, x_4, x_7);
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
x_37 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_35, x_4, x_7);
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
x_44 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_41, x_4, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_42, x_45, x_46);
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
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
x_2 = l_HashSet_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_FoldConstsImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FoldConstsImpl_initCache___closed__2;
return x_1;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 8192;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold___main___rarg(x_3, x_4, x_1, x_2, x_5);
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
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ptr_addr(x_3);
x_95 = x_2 == 0 ? 0 : x_94 % x_2;
x_96 = lean_ctor_get(x_5, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
x_98 = lean_array_uget(x_96, x_95);
x_99 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_100 = x_99 == x_94;
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_5, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_5, 0);
lean_dec(x_103);
lean_inc(x_3);
x_104 = lean_array_uset(x_96, x_95, x_3);
lean_ctor_set(x_5, 0, x_104);
x_105 = 0;
x_6 = x_105;
x_7 = x_5;
goto block_93;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_5);
lean_inc(x_3);
x_106 = lean_array_uset(x_96, x_95, x_3);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = 0;
x_6 = x_108;
x_7 = x_107;
goto block_93;
}
}
else
{
uint8_t x_109; 
lean_dec(x_97);
lean_dec(x_96);
x_109 = 1;
x_6 = x_109;
x_7 = x_5;
goto block_93;
}
block_93:
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
x_11 = l_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_10, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_8);
x_15 = l_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
lean_ctor_set(x_7, 1, x_15);
x_16 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box_uint32(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 2)
{
uint32_t x_22; uint8_t x_23; 
x_22 = lean_ctor_get_uint32(x_21, 0);
lean_dec(x_21);
x_23 = x_4 < x_22;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box_uint32(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box_uint32(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_28 = lean_box_uint32(x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
x_30 = lean_box_uint32(x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_inc(x_8);
x_32 = l_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box_uint32(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 2)
{
uint32_t x_40; uint8_t x_41; 
x_40 = lean_ctor_get_uint32(x_39, 0);
lean_dec(x_39);
x_41 = x_4 < x_40;
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box_uint32(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box_uint32(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
x_46 = lean_box_uint32(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_33);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
x_48 = lean_box_uint32(x_4);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_33);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_50 = lean_box_uint32(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
}
case 5:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_dec(x_3);
lean_inc(x_1);
x_54 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_2, x_52, x_4, x_7);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox_uint32(x_55);
lean_dec(x_55);
x_3 = x_53;
x_4 = x_57;
x_5 = x_56;
goto _start;
}
case 6:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint32_t x_64; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
lean_dec(x_3);
lean_inc(x_1);
x_61 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_2, x_59, x_4, x_7);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox_uint32(x_62);
lean_dec(x_62);
x_3 = x_60;
x_4 = x_64;
x_5 = x_63;
goto _start;
}
case 7:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint32_t x_71; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_1);
x_68 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_2, x_66, x_4, x_7);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox_uint32(x_69);
lean_dec(x_69);
x_3 = x_67;
x_4 = x_71;
x_5 = x_70;
goto _start;
}
case 8:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint32_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; 
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 3);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_1);
x_76 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_2, x_73, x_4, x_7);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox_uint32(x_77);
lean_dec(x_77);
lean_inc(x_1);
x_80 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_2, x_74, x_79, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox_uint32(x_81);
lean_dec(x_81);
x_3 = x_75;
x_4 = x_83;
x_5 = x_82;
goto _start;
}
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
lean_dec(x_3);
x_3 = x_85;
x_5 = x_7;
goto _start;
}
case 11:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
lean_dec(x_3);
x_3 = x_87;
x_5 = x_7;
goto _start;
}
default: 
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_box_uint32(x_4);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_7);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_3);
lean_dec(x_1);
x_91 = lean_box_uint32(x_4);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_7);
return x_92;
}
}
}
}
lean_object* l_Lean_getMaxHeight(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = 0;
x_4 = 8192;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_4, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; uint32_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_FoldConstsImpl_fold___main___at_Lean_getMaxHeight___spec__1(x_1, x_6, x_3, x_7, x_5);
return x_8;
}
}
lean_object* initialize_Init_Control_Option(lean_object*);
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_FoldConsts(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FoldConstsImpl_cacheSize = _init_l_Lean_Expr_FoldConstsImpl_cacheSize();
l_Lean_Expr_FoldConstsImpl_initCache___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache___closed__1);
l_Lean_Expr_FoldConstsImpl_initCache___closed__2 = _init_l_Lean_Expr_FoldConstsImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache___closed__2);
l_Lean_Expr_FoldConstsImpl_initCache = _init_l_Lean_Expr_FoldConstsImpl_initCache();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_initCache);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
