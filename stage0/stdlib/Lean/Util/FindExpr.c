// Lean compiler output
// Module: Lean.Util.FindExpr
// Imports: Init Lean.Expr
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_FindImpl_cacheSize;
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FindImpl_initCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_visited(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t _init_l_Lean_Expr_FindImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8191;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_visited(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ptr_addr(x_1);
x_5 = lean_usize_mod(x_4, x_2);
x_6 = lean_array_uget(x_3, x_5);
x_7 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_8 = lean_usize_dec_eq(x_7, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_visited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_FindImpl_visited(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l_Lean_Expr_FindImpl_visited(x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
x_15 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_13, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_3 = x_14;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_26 = x_16;
} else {
 lean_dec_ref(x_16);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_5);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_1);
x_31 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_29, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_3 = x_30;
x_4 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_30);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_31, 0, x_39);
return x_31;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_42 = x_32;
} else {
 lean_dec_ref(x_32);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_5);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_1);
x_47 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_45, x_9);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_3 = x_46;
x_4 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_47, 0, x_55);
return x_47;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_5);
x_61 = lean_ctor_get(x_3, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 3);
lean_inc(x_63);
lean_dec(x_3);
lean_inc(x_1);
x_64 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_61, x_9);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_1);
x_67 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_62, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_3 = x_63;
x_4 = x_69;
goto _start;
}
else
{
uint8_t x_71; 
lean_dec(x_63);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_67, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_67, 0, x_75);
return x_67;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_78 = x_68;
} else {
 lean_dec_ref(x_68);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_64);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_64, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_64;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_65, 0);
lean_inc(x_84);
lean_dec(x_65);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_64, 0, x_85);
return x_64;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_64, 1);
lean_inc(x_86);
lean_dec(x_64);
x_87 = lean_ctor_get(x_65, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_88 = x_65;
} else {
 lean_dec_ref(x_65);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
}
case 10:
{
lean_object* x_91; 
lean_free_object(x_5);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_dec(x_3);
x_3 = x_91;
x_4 = x_9;
goto _start;
}
case 11:
{
lean_object* x_93; 
lean_free_object(x_5);
x_93 = lean_ctor_get(x_3, 2);
lean_inc(x_93);
lean_dec(x_3);
x_3 = x_93;
x_4 = x_9;
goto _start;
}
default: 
{
lean_object* x_95; 
lean_dec(x_3);
lean_dec(x_1);
x_95 = lean_box(0);
lean_ctor_set(x_5, 0, x_95);
return x_5;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_5, 0, x_96);
return x_5;
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_98 = lean_apply_1(x_1, x_3);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_3, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_3, 1);
lean_inc(x_101);
lean_dec(x_3);
lean_inc(x_1);
x_102 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_100, x_97);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_3 = x_101;
x_4 = x_104;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_101);
lean_dec(x_1);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
case 6:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_3, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 2);
lean_inc(x_113);
lean_dec(x_3);
lean_inc(x_1);
x_114 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_112, x_97);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_3 = x_113;
x_4 = x_116;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_113);
lean_dec(x_1);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
}
case 7:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_3, 2);
lean_inc(x_125);
lean_dec(x_3);
lean_inc(x_1);
x_126 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_124, x_97);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_3 = x_125;
x_4 = x_128;
goto _start;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_1);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_3, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 3);
lean_inc(x_138);
lean_dec(x_3);
lean_inc(x_1);
x_139 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_136, x_97);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_1);
x_142 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_137, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_3 = x_138;
x_4 = x_144;
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_138);
lean_dec(x_1);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_152 = lean_ctor_get(x_139, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_153 = x_139;
} else {
 lean_dec_ref(x_139);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_140, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_155 = x_140;
} else {
 lean_dec_ref(x_140);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
}
case 10:
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_3, 1);
lean_inc(x_158);
lean_dec(x_3);
x_3 = x_158;
x_4 = x_97;
goto _start;
}
case 11:
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_3, 2);
lean_inc(x_160);
lean_dec(x_3);
x_3 = x_160;
x_4 = x_97;
goto _start;
}
default: 
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_97);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_1);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_3);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_97);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_3);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_5);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_5, 0);
lean_dec(x_167);
x_168 = lean_box(0);
lean_ctor_set(x_5, 0, x_168);
return x_5;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_5, 1);
lean_inc(x_169);
lean_dec(x_5);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_FindImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8191u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_FindImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FindImpl_initCache___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8191;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_occurs___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_occurs___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_occurs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_FindStep_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_FindStep_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_FindStep_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FindStep_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindStep_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_18 = x_8;
} else {
 lean_dec_ref(x_8);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(1, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_3, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l_Lean_Expr_FindImpl_visited(x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
case 1:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_14; 
lean_free_object(x_5);
x_14 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_2, x_3, x_9);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_5);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_1);
x_17 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_15, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_3 = x_16;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_16);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_28 = x_18;
} else {
 lean_dec_ref(x_18);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_5);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_1);
x_33 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_31, x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_3 = x_32;
x_4 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
case 8:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_5);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 3);
lean_inc(x_49);
lean_dec(x_3);
lean_inc(x_1);
x_50 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_47, x_9);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_1);
x_53 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_48, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_3 = x_49;
x_4 = x_55;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_53, 0, x_61);
return x_53;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_50);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_50, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_50;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_50, 0, x_71);
return x_50;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_dec(x_50);
x_73 = lean_ctor_get(x_51, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_74 = x_51;
} else {
 lean_dec_ref(x_51);
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
case 10:
{
lean_object* x_77; 
lean_free_object(x_5);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_3 = x_77;
x_4 = x_9;
goto _start;
}
case 11:
{
lean_object* x_79; 
lean_free_object(x_5);
x_79 = lean_ctor_get(x_3, 2);
lean_inc(x_79);
lean_dec(x_3);
x_3 = x_79;
x_4 = x_9;
goto _start;
}
default: 
{
lean_object* x_81; 
lean_dec(x_3);
lean_dec(x_1);
x_81 = lean_box(0);
lean_ctor_set(x_5, 0, x_81);
return x_5;
}
}
}
default: 
{
lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
lean_ctor_set(x_5, 0, x_82);
return x_5;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_5, 1);
lean_inc(x_83);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_84 = lean_apply_1(x_1, x_3);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
switch (x_85) {
case 0:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_3);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
case 1:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_88; 
x_88 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_2, x_3, x_83);
return x_88;
}
case 6:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
lean_inc(x_1);
x_91 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_89, x_83);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_3 = x_90;
x_4 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
lean_dec(x_1);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_3, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
lean_dec(x_3);
lean_inc(x_1);
x_103 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_101, x_83);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_3 = x_102;
x_4 = x_105;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_102);
lean_dec(x_1);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_108 = x_103;
} else {
 lean_dec_ref(x_103);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_3, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 3);
lean_inc(x_115);
lean_dec(x_3);
lean_inc(x_1);
x_116 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_113, x_83);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_1);
x_119 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_114, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_3 = x_115;
x_4 = x_121;
goto _start;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
lean_dec(x_1);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_123);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_130 = x_116;
} else {
 lean_dec_ref(x_116);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_132 = x_117;
} else {
 lean_dec_ref(x_117);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
case 10:
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_3, 1);
lean_inc(x_135);
lean_dec(x_3);
x_3 = x_135;
x_4 = x_83;
goto _start;
}
case 11:
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_3, 2);
lean_inc(x_137);
lean_dec(x_3);
x_3 = x_137;
x_4 = x_83;
goto _start;
}
default: 
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_1);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_83);
return x_140;
}
}
}
default: 
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_83);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_5);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_5, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_5, 0, x_145);
return x_5;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_5, 1);
lean_inc(x_146);
lean_dec(x_5);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindExtImpl_findM_x3f(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findUnsafe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8191;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FindImpl_cacheSize = _init_l_Lean_Expr_FindImpl_cacheSize();
l_Lean_Expr_FindImpl_initCache___closed__1 = _init_l_Lean_Expr_FindImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_FindImpl_initCache___closed__1);
l_Lean_Expr_FindImpl_initCache = _init_l_Lean_Expr_FindImpl_initCache();
lean_mark_persistent(l_Lean_Expr_FindImpl_initCache);
l_Lean_Expr_FindStep_noConfusion___rarg___closed__1 = _init_l_Lean_Expr_FindStep_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_FindStep_noConfusion___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
