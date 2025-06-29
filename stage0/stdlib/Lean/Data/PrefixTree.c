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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_3);
x_14 = lean_apply_2(x_1, x_3, x_11);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
switch (x_15) {
case 0:
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_10, x_3, x_4);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
case 1:
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
default: 
{
lean_object* x_17; 
x_17 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_13, x_3, x_4);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_19);
lean_inc(x_3);
x_22 = lean_apply_2(x_1, x_3, x_19);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
switch (x_23) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_18, x_3, x_4);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_8);
return x_25;
}
case 1:
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_8);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_21, x_3, x_4);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_8);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_33 = x_2;
} else {
 lean_dec_ref(x_2);
 x_33 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_30);
lean_inc(x_3);
x_34 = lean_apply_2(x_1, x_3, x_30);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
switch (x_35) {
case 0:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_29, x_3, x_4);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 3);
lean_inc(x_41);
if (x_37 == 0)
{
if (lean_obj_tag(x_38) == 0)
{
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_56; 
lean_dec(x_33);
x_56 = !lean_is_exclusive(x_36);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_36, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_36, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_36, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_36, 0);
lean_dec(x_60);
lean_ctor_set(x_36, 0, x_41);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_36);
lean_ctor_set(x_61, 1, x_30);
lean_ctor_set(x_61, 2, x_31);
lean_ctor_set(x_61, 3, x_32);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_8);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_36);
x_62 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_39);
lean_ctor_set(x_62, 2, x_40);
lean_ctor_set(x_62, 3, x_41);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_37);
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_30);
lean_ctor_set(x_63, 2, x_31);
lean_ctor_set(x_63, 3, x_32);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_8);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_36);
x_65 = lean_ctor_get(x_41, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_41, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_41, 3);
lean_inc(x_68);
lean_dec(x_41);
x_42 = x_38;
x_43 = x_39;
x_44 = x_40;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
goto block_55;
}
else
{
uint8_t x_69; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_33);
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_41, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_41, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_41, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_41, 0);
lean_dec(x_73);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_8);
return x_41;
}
else
{
lean_object* x_74; 
lean_dec(x_41);
x_74 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_74, 0, x_36);
lean_ctor_set(x_74, 1, x_30);
lean_ctor_set(x_74, 2, x_31);
lean_ctor_set(x_74, 3, x_32);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_8);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
x_75 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_36);
x_76 = lean_ctor_get(x_38, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 3);
lean_inc(x_79);
lean_dec(x_38);
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_79;
x_46 = x_39;
x_47 = x_40;
x_48 = x_41;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
goto block_55;
}
else
{
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_80; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_33);
x_80 = !lean_is_exclusive(x_38);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_38, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_38, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_38, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_38, 0);
lean_dec(x_84);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_8);
return x_38;
}
else
{
lean_object* x_85; 
lean_dec(x_38);
x_85 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_85, 0, x_36);
lean_ctor_set(x_85, 1, x_30);
lean_ctor_set(x_85, 2, x_31);
lean_ctor_set(x_85, 3, x_32);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_8);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_36, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_36, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_36, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_36, 0);
lean_dec(x_90);
x_91 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_36);
x_92 = lean_ctor_get(x_41, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_41, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_41, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_41, 3);
lean_inc(x_95);
lean_dec(x_41);
x_42 = x_38;
x_43 = x_39;
x_44 = x_40;
x_45 = x_92;
x_46 = x_93;
x_47 = x_94;
x_48 = x_95;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
goto block_55;
}
else
{
uint8_t x_96; 
lean_dec(x_33);
x_96 = !lean_is_exclusive(x_38);
if (x_96 == 0)
{
lean_object* x_97; 
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_91);
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_36);
lean_ctor_set(x_97, 1, x_30);
lean_ctor_set(x_97, 2, x_31);
lean_ctor_set(x_97, 3, x_32);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_8);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_38, 0);
x_99 = lean_ctor_get(x_38, 1);
x_100 = lean_ctor_get(x_38, 2);
x_101 = lean_ctor_get(x_38, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_38);
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_91);
lean_ctor_set(x_36, 0, x_102);
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_36);
lean_ctor_set(x_103, 1, x_30);
lean_ctor_set(x_103, 2, x_31);
lean_ctor_set(x_103, 3, x_32);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_8);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_36);
x_104 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_41, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_41, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_41, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_41, 3);
lean_inc(x_108);
lean_dec(x_41);
x_42 = x_38;
x_43 = x_39;
x_44 = x_40;
x_45 = x_105;
x_46 = x_106;
x_47 = x_107;
x_48 = x_108;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
goto block_55;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_33);
x_109 = lean_ctor_get(x_38, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_38, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_38, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_38, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_113 = x_38;
} else {
 lean_dec_ref(x_38);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_104);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_39);
lean_ctor_set(x_115, 2, x_40);
lean_ctor_set(x_115, 3, x_41);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_37);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_30);
lean_ctor_set(x_116, 2, x_31);
lean_ctor_set(x_116, 3, x_32);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_8);
return x_116;
}
}
}
}
}
}
else
{
lean_object* x_117; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_33);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_36);
lean_ctor_set(x_117, 1, x_30);
lean_ctor_set(x_117, 2, x_31);
lean_ctor_set(x_117, 3, x_32);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_8);
return x_117;
}
block_55:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_33)) {
 x_52 = lean_alloc_ctor(1, 4, 1);
} else {
 x_52 = x_33;
}
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_8);
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_8);
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_37);
return x_54;
}
}
case 1:
{
lean_object* x_118; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
if (lean_is_scalar(x_33)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_33;
}
lean_ctor_set(x_118, 0, x_29);
lean_ctor_set(x_118, 1, x_3);
lean_ctor_set(x_118, 2, x_4);
lean_ctor_set(x_118, 3, x_32);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_8);
return x_118;
}
default: 
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_PrefixTreeNode_insert_loop_spec__0_spec__0___redArg(x_1, x_32, x_3, x_4);
x_120 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 3);
lean_inc(x_124);
if (x_120 == 0)
{
if (lean_obj_tag(x_121) == 0)
{
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_139; 
lean_dec(x_33);
x_139 = !lean_is_exclusive(x_119);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_119, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_119, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_119, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_119, 0);
lean_dec(x_143);
lean_ctor_set(x_119, 0, x_124);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_29);
lean_ctor_set(x_144, 1, x_30);
lean_ctor_set(x_144, 2, x_31);
lean_ctor_set(x_144, 3, x_119);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_8);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_119);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_124);
lean_ctor_set(x_145, 1, x_122);
lean_ctor_set(x_145, 2, x_123);
lean_ctor_set(x_145, 3, x_124);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_120);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_29);
lean_ctor_set(x_146, 1, x_30);
lean_ctor_set(x_146, 2, x_31);
lean_ctor_set(x_146, 3, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_8);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = lean_ctor_get_uint8(x_124, sizeof(void*)*4);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_119);
x_148 = lean_ctor_get(x_124, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_124, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_124, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_124, 3);
lean_inc(x_151);
lean_dec(x_124);
x_125 = x_29;
x_126 = x_30;
x_127 = x_31;
x_128 = x_121;
x_129 = x_122;
x_130 = x_123;
x_131 = x_148;
x_132 = x_149;
x_133 = x_150;
x_134 = x_151;
goto block_138;
}
else
{
uint8_t x_152; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_33);
x_152 = !lean_is_exclusive(x_124);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_124, 3);
lean_dec(x_153);
x_154 = lean_ctor_get(x_124, 2);
lean_dec(x_154);
x_155 = lean_ctor_get(x_124, 1);
lean_dec(x_155);
x_156 = lean_ctor_get(x_124, 0);
lean_dec(x_156);
lean_ctor_set(x_124, 3, x_119);
lean_ctor_set(x_124, 2, x_31);
lean_ctor_set(x_124, 1, x_30);
lean_ctor_set(x_124, 0, x_29);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_8);
return x_124;
}
else
{
lean_object* x_157; 
lean_dec(x_124);
x_157 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_157, 0, x_29);
lean_ctor_set(x_157, 1, x_30);
lean_ctor_set(x_157, 2, x_31);
lean_ctor_set(x_157, 3, x_119);
lean_ctor_set_uint8(x_157, sizeof(void*)*4, x_8);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
x_158 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_119);
x_159 = lean_ctor_get(x_121, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_121, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_121, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
lean_dec(x_121);
x_125 = x_29;
x_126 = x_30;
x_127 = x_31;
x_128 = x_159;
x_129 = x_160;
x_130 = x_161;
x_131 = x_162;
x_132 = x_122;
x_133 = x_123;
x_134 = x_124;
goto block_138;
}
else
{
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_163; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_33);
x_163 = !lean_is_exclusive(x_121);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_121, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_121, 2);
lean_dec(x_165);
x_166 = lean_ctor_get(x_121, 1);
lean_dec(x_166);
x_167 = lean_ctor_get(x_121, 0);
lean_dec(x_167);
lean_ctor_set(x_121, 3, x_119);
lean_ctor_set(x_121, 2, x_31);
lean_ctor_set(x_121, 1, x_30);
lean_ctor_set(x_121, 0, x_29);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_8);
return x_121;
}
else
{
lean_object* x_168; 
lean_dec(x_121);
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_29);
lean_ctor_set(x_168, 1, x_30);
lean_ctor_set(x_168, 2, x_31);
lean_ctor_set(x_168, 3, x_119);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_8);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_119);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_119, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_119, 2);
lean_dec(x_171);
x_172 = lean_ctor_get(x_119, 1);
lean_dec(x_172);
x_173 = lean_ctor_get(x_119, 0);
lean_dec(x_173);
x_174 = lean_ctor_get_uint8(x_124, sizeof(void*)*4);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_free_object(x_119);
x_175 = lean_ctor_get(x_124, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_124, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_124, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_124, 3);
lean_inc(x_178);
lean_dec(x_124);
x_125 = x_29;
x_126 = x_30;
x_127 = x_31;
x_128 = x_121;
x_129 = x_122;
x_130 = x_123;
x_131 = x_175;
x_132 = x_176;
x_133 = x_177;
x_134 = x_178;
goto block_138;
}
else
{
uint8_t x_179; 
lean_dec(x_33);
x_179 = !lean_is_exclusive(x_121);
if (x_179 == 0)
{
lean_object* x_180; 
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_174);
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_29);
lean_ctor_set(x_180, 1, x_30);
lean_ctor_set(x_180, 2, x_31);
lean_ctor_set(x_180, 3, x_119);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_8);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_121, 0);
x_182 = lean_ctor_get(x_121, 1);
x_183 = lean_ctor_get(x_121, 2);
x_184 = lean_ctor_get(x_121, 3);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_121);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_182);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_174);
lean_ctor_set(x_119, 0, x_185);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_29);
lean_ctor_set(x_186, 1, x_30);
lean_ctor_set(x_186, 2, x_31);
lean_ctor_set(x_186, 3, x_119);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_8);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_119);
x_187 = lean_ctor_get_uint8(x_124, sizeof(void*)*4);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_124, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_124, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_124, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_124, 3);
lean_inc(x_191);
lean_dec(x_124);
x_125 = x_29;
x_126 = x_30;
x_127 = x_31;
x_128 = x_121;
x_129 = x_122;
x_130 = x_123;
x_131 = x_188;
x_132 = x_189;
x_133 = x_190;
x_134 = x_191;
goto block_138;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_33);
x_192 = lean_ctor_get(x_121, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_121, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_121, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_121, 3);
lean_inc(x_195);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_196 = x_121;
} else {
 lean_dec_ref(x_121);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 4, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set(x_197, 2, x_194);
lean_ctor_set(x_197, 3, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_187);
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_122);
lean_ctor_set(x_198, 2, x_123);
lean_ctor_set(x_198, 3, x_124);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_120);
x_199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_199, 0, x_29);
lean_ctor_set(x_199, 1, x_30);
lean_ctor_set(x_199, 2, x_31);
lean_ctor_set(x_199, 3, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_8);
return x_199;
}
}
}
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_33);
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_29);
lean_ctor_set(x_200, 1, x_30);
lean_ctor_set(x_200, 2, x_31);
lean_ctor_set(x_200, 3, x_119);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_8);
return x_200;
}
block_138:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
if (lean_is_scalar(x_33)) {
 x_135 = lean_alloc_ctor(1, 4, 1);
} else {
 x_135 = x_33;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_127);
lean_ctor_set(x_135, 3, x_128);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_8);
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_8);
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_130);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_120);
return x_137;
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
lean_dec(x_9);
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
lean_dec(x_3);
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
