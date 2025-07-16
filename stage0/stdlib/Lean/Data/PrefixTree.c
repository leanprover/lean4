// Lean compiler output
// Module: Lean.Data.PrefixTree
// Imports: Lean.Data.RBMap
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
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrefixTree_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedPrefixTreeNode___closed__0;
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_singleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedPrefixTreeNode___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPrefixTreeNode___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPrefixTreeNode___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(x_1, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_RBNode_singleton___redArg(x_7, x_9);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(x_1, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_RBNode_singleton___redArg(x_12, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_9, x_3, x_4);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
default: 
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_12, x_3, x_4);
lean_ctor_set(x_2, 3, x_16);
return x_2;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_18);
lean_inc(x_3);
x_21 = lean_apply_2(x_1, x_3, x_18);
x_22 = lean_unbox(x_21);
switch (x_22) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_17, x_3, x_4);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_7);
return x_24;
}
case 1:
{
lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_20, x_3, x_4);
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_7);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_32 = x_2;
} else {
 lean_dec_ref(x_2);
 x_32 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_29);
lean_inc(x_3);
x_33 = lean_apply_2(x_1, x_3, x_29);
x_34 = lean_unbox(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_28, x_3, x_4);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*4);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
if (x_36 == 0)
{
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_55; 
lean_dec(x_32);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_35, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_35, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_35, 0);
lean_dec(x_59);
lean_ctor_set(x_35, 0, x_40);
x_60 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_60, 0, x_35);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_30);
lean_ctor_set(x_60, 3, x_31);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_7);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_61, 1, x_38);
lean_ctor_set(x_61, 2, x_39);
lean_ctor_set(x_61, 3, x_40);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_36);
x_62 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_29);
lean_ctor_set(x_62, 2, x_30);
lean_ctor_set(x_62, 3, x_31);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_7);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_35);
x_64 = lean_ctor_get(x_40, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_40, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_40, 3);
lean_inc(x_67);
lean_dec(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_68; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_40, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_40, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_40, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_40, 0);
lean_dec(x_72);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_7);
return x_40;
}
else
{
lean_object* x_73; 
lean_dec(x_40);
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_35);
lean_ctor_set(x_73, 1, x_29);
lean_ctor_set(x_73, 2, x_30);
lean_ctor_set(x_73, 3, x_31);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_7);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_35);
x_75 = lean_ctor_get(x_37, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_37, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_37, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_37, 3);
lean_inc(x_78);
lean_dec(x_37);
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_38;
x_46 = x_39;
x_47 = x_40;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_79; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_79 = !lean_is_exclusive(x_37);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_37, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_37, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_37, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_37, 0);
lean_dec(x_83);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_84; 
lean_dec(x_37);
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_35);
lean_ctor_set(x_84, 1, x_29);
lean_ctor_set(x_84, 2, x_30);
lean_ctor_set(x_84, 3, x_31);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_7);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_35);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_35, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_35, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_35, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_35, 0);
lean_dec(x_89);
x_90 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_35);
x_91 = lean_ctor_get(x_40, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_40, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_40, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_40, 3);
lean_inc(x_94);
lean_dec(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_91;
x_45 = x_92;
x_46 = x_93;
x_47 = x_94;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_95; 
lean_dec(x_32);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
lean_object* x_96; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_90);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_35);
lean_ctor_set(x_96, 1, x_29);
lean_ctor_set(x_96, 2, x_30);
lean_ctor_set(x_96, 3, x_31);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_37, 0);
x_98 = lean_ctor_get(x_37, 1);
x_99 = lean_ctor_get(x_37, 2);
x_100 = lean_ctor_get(x_37, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_37);
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_90);
lean_ctor_set(x_35, 0, x_101);
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_35);
lean_ctor_set(x_102, 1, x_29);
lean_ctor_set(x_102, 2, x_30);
lean_ctor_set(x_102, 3, x_31);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_7);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_35);
x_103 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_40, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_40, 3);
lean_inc(x_107);
lean_dec(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_104;
x_45 = x_105;
x_46 = x_106;
x_47 = x_107;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_32);
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_112 = x_37;
} else {
 lean_dec_ref(x_37);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_103);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_38);
lean_ctor_set(x_114, 2, x_39);
lean_ctor_set(x_114, 3, x_40);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_36);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_29);
lean_ctor_set(x_115, 2, x_30);
lean_ctor_set(x_115, 3, x_31);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_7);
return x_115;
}
}
}
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_35);
lean_ctor_set(x_116, 1, x_29);
lean_ctor_set(x_116, 2, x_30);
lean_ctor_set(x_116, 3, x_31);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_7);
return x_116;
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 4, 1);
} else {
 x_51 = x_32;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_7);
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_7);
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_36);
return x_53;
}
}
case 1:
{
lean_object* x_117; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
if (lean_is_scalar(x_32)) {
 x_117 = lean_alloc_ctor(1, 4, 1);
} else {
 x_117 = x_32;
}
lean_ctor_set(x_117, 0, x_28);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 2, x_4);
lean_ctor_set(x_117, 3, x_31);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
default: 
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_118 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_31, x_3, x_4);
x_119 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
if (x_119 == 0)
{
if (lean_obj_tag(x_120) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_138; 
lean_dec(x_32);
x_138 = !lean_is_exclusive(x_118);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_118, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_118, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_118, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_118, 0);
lean_dec(x_142);
lean_ctor_set(x_118, 0, x_123);
x_143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_143, 0, x_28);
lean_ctor_set(x_143, 1, x_29);
lean_ctor_set(x_143, 2, x_30);
lean_ctor_set(x_143, 3, x_118);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_7);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_118);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_121);
lean_ctor_set(x_144, 2, x_122);
lean_ctor_set(x_144, 3, x_123);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_119);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_28);
lean_ctor_set(x_145, 1, x_29);
lean_ctor_set(x_145, 2, x_30);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_7);
return x_145;
}
}
else
{
uint8_t x_146; 
x_146 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_118);
x_147 = lean_ctor_get(x_123, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_123, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_123, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_123, 3);
lean_inc(x_150);
lean_dec(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_147;
x_131 = x_148;
x_132 = x_149;
x_133 = x_150;
goto block_137;
}
else
{
uint8_t x_151; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_151 = !lean_is_exclusive(x_123);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_123, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_123, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_123, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_123, 0);
lean_dec(x_155);
lean_ctor_set(x_123, 3, x_118);
lean_ctor_set(x_123, 2, x_30);
lean_ctor_set(x_123, 1, x_29);
lean_ctor_set(x_123, 0, x_28);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_7);
return x_123;
}
else
{
lean_object* x_156; 
lean_dec(x_123);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_28);
lean_ctor_set(x_156, 1, x_29);
lean_ctor_set(x_156, 2, x_30);
lean_ctor_set(x_156, 3, x_118);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_7);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
x_157 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_118);
x_158 = lean_ctor_get(x_120, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_120, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_120, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_120, 3);
lean_inc(x_161);
lean_dec(x_120);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_158;
x_128 = x_159;
x_129 = x_160;
x_130 = x_161;
x_131 = x_121;
x_132 = x_122;
x_133 = x_123;
goto block_137;
}
else
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_162; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_162 = !lean_is_exclusive(x_120);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_120, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_120, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_120, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_120, 0);
lean_dec(x_166);
lean_ctor_set(x_120, 3, x_118);
lean_ctor_set(x_120, 2, x_30);
lean_ctor_set(x_120, 1, x_29);
lean_ctor_set(x_120, 0, x_28);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_167; 
lean_dec(x_120);
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_28);
lean_ctor_set(x_167, 1, x_29);
lean_ctor_set(x_167, 2, x_30);
lean_ctor_set(x_167, 3, x_118);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_7);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_118);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_118, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_118, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_118, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_118, 0);
lean_dec(x_172);
x_173 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_118);
x_174 = lean_ctor_get(x_123, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_123, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_123, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_123, 3);
lean_inc(x_177);
lean_dec(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_174;
x_131 = x_175;
x_132 = x_176;
x_133 = x_177;
goto block_137;
}
else
{
uint8_t x_178; 
lean_dec(x_32);
x_178 = !lean_is_exclusive(x_120);
if (x_178 == 0)
{
lean_object* x_179; 
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_173);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_28);
lean_ctor_set(x_179, 1, x_29);
lean_ctor_set(x_179, 2, x_30);
lean_ctor_set(x_179, 3, x_118);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_7);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_120, 0);
x_181 = lean_ctor_get(x_120, 1);
x_182 = lean_ctor_get(x_120, 2);
x_183 = lean_ctor_get(x_120, 3);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_120);
x_184 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_181);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_173);
lean_ctor_set(x_118, 0, x_184);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_28);
lean_ctor_set(x_185, 1, x_29);
lean_ctor_set(x_185, 2, x_30);
lean_ctor_set(x_185, 3, x_118);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_7);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_118);
x_186 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_123, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_123, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_123, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_123, 3);
lean_inc(x_190);
lean_dec(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_187;
x_131 = x_188;
x_132 = x_189;
x_133 = x_190;
goto block_137;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_32);
x_191 = lean_ctor_get(x_120, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_120, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_120, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_120, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 x_195 = x_120;
} else {
 lean_dec_ref(x_120);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_186);
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_121);
lean_ctor_set(x_197, 2, x_122);
lean_ctor_set(x_197, 3, x_123);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_119);
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_28);
lean_ctor_set(x_198, 1, x_29);
lean_ctor_set(x_198, 2, x_30);
lean_ctor_set(x_198, 3, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_7);
return x_198;
}
}
}
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_32);
x_199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_199, 0, x_28);
lean_ctor_set(x_199, 1, x_29);
lean_ctor_set(x_199, 2, x_30);
lean_ctor_set(x_199, 3, x_118);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_7);
return x_199;
}
block_137:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_scalar(x_32)) {
 x_134 = lean_alloc_ctor(1, 4, 1);
} else {
 x_134 = x_32;
}
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_125);
lean_ctor_set(x_134, 2, x_126);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_7);
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_7);
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_119);
return x_136;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
default: 
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_13 = x_3;
} else {
 lean_dec_ref(x_3);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_1);
x_20 = l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(x_1, x_12, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_PrefixTreeNode_insert_insertEmpty___redArg(x_2, x_15);
x_16 = x_21;
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_1, x_2, x_22, x_15);
x_16 = x_23;
goto block_19;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0___redArg(x_1, x_12, x_14, x_16);
if (lean_is_scalar(x_13)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_13;
}
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_2, x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_4, x_6, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(x_1, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_find_x3f_loop___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_find_x3f_loop___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_find_x3f_loop___redArg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
lean_dec(x_2);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
x_10 = l_Lean_RBNode_find___at___Lean_PrefixTreeNode_insert_loop_spec__2___redArg(x_1, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_2 = x_6;
x_3 = x_13;
x_4 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(x_2, x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_9);
x_12 = lean_apply_2(x_7, lean_box(0), x_4);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_9);
x_16 = lean_apply_2(x_2, x_14, x_4);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lean_PrefixTreeNode_foldMatchingM_fold___redArg(x_1, x_4, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
lean_inc(x_2);
x_14 = l_Lean_RBNode_find___redArg(x_2, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_2(x_10, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_5 = x_12;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_1, x_3, x_5, x_6, x_4, x_2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
x_11 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_5, x_7, x_9, x_10, x_8, x_6, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_PrefixTree_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPrefixTree(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instEmptyCollectionPrefixTree(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrefixTreeNode_insert_loop___redArg(x_3, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_find_x3f_loop___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_find_x3f_loop___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_2, x_1, x_5, x_6, x_4, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
x_11 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_6, x_4, x_9, x_10, x_8, x_7, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
lean_inc(x_4);
x_7 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_2, x_1, x_4, x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_inc(x_8);
x_11 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_6, x_4, x_8, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_2, x_1, x_7, x_6, x_4, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_5, x_4, x_10, x_9, x_7, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_forMatchingM___redArg___lam__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_2, x_1, x_7, x_5, x_6, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = l_Lean_PrefixTreeNode_foldMatchingM_find___redArg(x_5, x_4, x_10, x_8, x_9, x_6, x_10);
return x_11;
}
}
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PrefixTree(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedPrefixTreeNode___closed__0 = _init_l_Lean_instInhabitedPrefixTreeNode___closed__0();
lean_mark_persistent(l_Lean_instInhabitedPrefixTreeNode___closed__0);
l_Lean_PrefixTree_empty___closed__0 = _init_l_Lean_PrefixTree_empty___closed__0();
lean_mark_persistent(l_Lean_PrefixTree_empty___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
