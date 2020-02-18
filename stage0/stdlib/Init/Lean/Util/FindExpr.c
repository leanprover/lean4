// Lean compiler output
// Module: Init.Lean.Util.FindExpr
// Imports: Init.Control.Option Init.Lean.Expr
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
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t l_Lean_Expr_FindImpl_cacheSize;
lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_initCache___closed__1;
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Expr_FindImpl_visited(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_FindImpl_initCache;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_find_x3f___main(lean_object*, lean_object*);
size_t _init_l_Lean_Expr_FindImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_FindImpl_visited(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ptr_addr(x_1);
x_5 = x_2 == 0 ? 0 : x_4 % x_2;
x_6 = lean_array_uget(x_3, x_5);
x_7 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_8 = x_7 == x_4;
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uset(x_3, x_5, x_1);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
lean_object* l_Lean_Expr_FindImpl_visited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_FindImpl_visited(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; size_t x_98; size_t x_99; lean_object* x_100; size_t x_101; uint8_t x_102; 
x_98 = lean_ptr_addr(x_3);
x_99 = x_2 == 0 ? 0 : x_98 % x_2;
x_100 = lean_array_uget(x_4, x_99);
x_101 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_102 = x_101 == x_98;
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
lean_inc(x_3);
x_103 = lean_array_uset(x_4, x_99, x_3);
x_104 = 0;
x_5 = x_104;
x_6 = x_103;
goto block_97;
}
else
{
uint8_t x_105; 
x_105 = 1;
x_5 = x_105;
x_6 = x_4;
goto block_97;
}
block_97:
{
if (x_5 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
lean_inc(x_3);
x_7 = lean_apply_1(x_1, x_3);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_9, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_3 = x_10;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_22 = x_12;
} else {
 lean_dec_ref(x_12);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_1);
x_27 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_25, x_6);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_3 = x_26;
x_4 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_38 = x_28;
} else {
 lean_dec_ref(x_28);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
lean_dec(x_3);
lean_inc(x_1);
x_43 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_41, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_3 = x_42;
x_4 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_42);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 3);
lean_inc(x_59);
lean_dec(x_3);
lean_inc(x_1);
x_60 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_57, x_6);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_1);
x_63 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_58, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_3 = x_59;
x_4 = x_65;
goto _start;
}
else
{
uint8_t x_67; 
lean_dec(x_59);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_63, 0, x_71);
return x_63;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_74 = x_64;
} else {
 lean_dec_ref(x_64);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_60, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_60;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_80);
lean_dec(x_61);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_60, 0, x_81);
return x_60;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
lean_dec(x_60);
x_83 = lean_ctor_get(x_61, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_84 = x_61;
} else {
 lean_dec_ref(x_61);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
}
case 10:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_3, 1);
lean_inc(x_87);
lean_dec(x_3);
x_3 = x_87;
x_4 = x_6;
goto _start;
}
case 11:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_3, 2);
lean_inc(x_89);
lean_dec(x_3);
x_3 = x_89;
x_4 = x_6;
goto _start;
}
default: 
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_3);
lean_dec(x_1);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_6);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_3);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_6);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_3);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_6);
return x_96;
}
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Expr_FindImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_FindImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FindImpl_initCache___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_find_x3f___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Lean_Expr_find_x3f___main(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Expr_find_x3f___main(x_1, x_9);
if (lean_obj_tag(x_11) == 0)
{
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
case 7:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_15 = l_Lean_Expr_find_x3f___main(x_1, x_13);
if (lean_obj_tag(x_15) == 0)
{
x_2 = x_14;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_1);
return x_15;
}
}
case 8:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_20 = l_Lean_Expr_find_x3f___main(x_1, x_17);
lean_inc(x_1);
x_21 = l_Lean_Expr_find_x3f___main(x_1, x_18);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
x_2 = x_19;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_dec(x_19);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
return x_21;
}
else
{
lean_dec(x_21);
return x_20;
}
}
}
case 10:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_2 = x_23;
goto _start;
}
case 11:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
return x_28;
}
}
}
lean_object* l_Lean_Expr_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_find_x3f___main(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Control_Option(lean_object*);
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_FindExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FindImpl_cacheSize = _init_l_Lean_Expr_FindImpl_cacheSize();
l_Lean_Expr_FindImpl_initCache___closed__1 = _init_l_Lean_Expr_FindImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_FindImpl_initCache___closed__1);
l_Lean_Expr_FindImpl_initCache = _init_l_Lean_Expr_FindImpl_initCache();
lean_mark_persistent(l_Lean_Expr_FindImpl_initCache);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
