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
static lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Expr_getUsedConstantsAsSet___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
static lean_object* l_Lean_Expr_getUsedConstants___closed__2;
lean_object* l_Lean_NameSet_append___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__1;
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lambda__1(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT size_t l_Lean_Expr_FoldConstsImpl_cacheSize;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Expr_FoldConstsImpl_initCache___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getUsedConstants___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object*, size_t, lean_object*);
static size_t _init_l_Lean_Expr_FoldConstsImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8191;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_visited(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ptr_addr(x_1);
x_5 = lean_usize_mod(x_4, x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_9, x_4);
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_3);
x_6 = l_Lean_Expr_FoldConstsImpl_visited(x_3, x_2, x_5);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_12);
x_16 = l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_13, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_1, x_12, x_4);
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_20);
x_24 = l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_21, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_2(x_1, x_20, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_1);
x_32 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_30, x_4, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_3 = x_31;
x_4 = x_33;
x_5 = x_34;
goto _start;
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_1);
x_39 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_37, x_4, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_3 = x_38;
x_4 = x_40;
x_5 = x_41;
goto _start;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_1);
x_46 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_44, x_4, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_3 = x_45;
x_4 = x_47;
x_5 = x_48;
goto _start;
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_dec(x_6);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 3);
lean_inc(x_53);
lean_dec(x_3);
lean_inc(x_1);
x_54 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_51, x_4, x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_1);
x_57 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_52, x_55, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_3 = x_53;
x_4 = x_58;
x_5 = x_59;
goto _start;
}
case 10:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_dec(x_6);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
lean_dec(x_3);
x_3 = x_62;
x_5 = x_61;
goto _start;
}
case 11:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_3 = x_65;
x_5 = x_64;
goto _start;
}
default: 
{
uint8_t x_67; 
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_6);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_6, 0);
lean_dec(x_68);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_6, 1);
lean_inc(x_69);
lean_dec(x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_6);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_6, 0);
lean_dec(x_72);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_73);
return x_74;
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
x_1 = lean_unsigned_to_nat(8191u);
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
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
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
x_4 = 8191;
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
x_2 = 8191;
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
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstantsAsSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstantsAsSet___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = 8191;
x_3 = l_Lean_Expr_getUsedConstantsAsSet___closed__1;
x_4 = l_Lean_NameSet_empty;
x_5 = l_Lean_Expr_FoldConstsImpl_initCache;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_5, x_3, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_NameSet_append___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_ConstantInfo_type(x_1);
x_3 = l_Lean_Expr_getUsedConstantsAsSet(x_2);
x_4 = l_Lean_ConstantInfo_value_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Expr_getUsedConstantsAsSet(x_6);
x_8 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_10 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_8, x_9, x_3, x_7);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_12);
x_14 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_15 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_16 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_14, x_15, x_3, x_13);
return x_16;
}
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_NameSet_empty;
x_21 = lean_box(0);
x_22 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_20, x_19, x_21);
x_23 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_24 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_25 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_23, x_24, x_3, x_22);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_27);
x_29 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_30 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_31 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_29, x_30, x_3, x_28);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_32 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_33 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_34 = l_Lean_NameSet_empty;
x_35 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_32, x_33, x_3, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_Expr_getUsedConstantsAsSet(x_36);
x_38 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_39 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_40 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_38, x_39, x_3, x_37);
return x_40;
}
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
x_9 = lean_uint32_dec_lt(x_3, x_8);
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
x_4 = 8191;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
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
l_Lean_Expr_getUsedConstantsAsSet___closed__1 = _init_l_Lean_Expr_getUsedConstantsAsSet___closed__1();
lean_mark_persistent(l_Lean_Expr_getUsedConstantsAsSet___closed__1);
l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1 = _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1();
lean_mark_persistent(l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1);
l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2 = _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2();
lean_mark_persistent(l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2);
l_Lean_getMaxHeight___boxed__const__1 = _init_l_Lean_getMaxHeight___boxed__const__1();
lean_mark_persistent(l_Lean_getMaxHeight___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
