// Lean compiler output
// Module: Lean.Data.NameMap
// Imports: Std.Data.HashSet.Basic Lean.Data.RBMap Lean.Data.RBTree Lean.Data.SSet Lean.Data.Name
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
static lean_object* l_Lean_NameHashSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_NameHashSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_NameHashSet_filter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instInhabited;
LEAN_EXPORT lean_object* l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_NameMap_instForInProdName___closed__0;
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1(lean_object*, size_t, size_t, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object*, lean_object*);
static lean_object* l_Lean_NameHashSet_empty___closed__4;
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_RBMap_instForInProd___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instAppend;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_NameHashSet_empty___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_NameSet_instForInName___closed__0;
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_instInhabited;
static lean_object* l_Lean_NameSSet_empty___closed__0;
static lean_object* l_Lean_NameSSet_empty___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_append___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_NameSet_instAppend___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_empty;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_NameSSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object*);
lean_object* l_Lean_RBTree_instForIn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instEmptyCollection;
lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_RBTree_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lean_NameMap_instRepr___redArg___closed__0;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object*);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_empty;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInhabited;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_NameHashSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_append___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_filterMap___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
static lean_object* l_Lean_NameMap_filter___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_NameMap_instRepr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_reprPrec___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_NameMap_instRepr___redArg___closed__0;
x_3 = l_Lean_RBMap_instRepr___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameMap_instRepr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickCmp(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Name_quickCmp(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_NameMap_contains___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_NameMap_contains___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_NameMap_contains(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameMap_find_x3f___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameMap_find_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_NameMap_instForInProdName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___lam__2), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameMap_instForInProdName___closed__0;
return x_3;
}
}
static lean_object* _init_l_Lean_NameMap_filter___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_NameMap_filter___redArg___closed__0;
x_4 = l_Lean_RBMap_filter___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameMap_filter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_NameMap_filter___redArg___closed__0;
x_4 = l_Lean_RBMap_filterMap___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_NameMap_filterMap___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_NameSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_NameSet_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_NameSet_instForInName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBTree_instForIn___lam__2), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_NameSet_instForInName___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_NameSet_append___lam__0___boxed), 3, 0);
x_4 = l_Lean_NameMap_filter___redArg___closed__0;
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(x_4, x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameSet_append___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_NameSet_instAppend___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_NameSet_append), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSet_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_instAppend___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_NameMap_filter___redArg___closed__0;
x_4 = l_Lean_RBTree_filter___redArg(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSSet_empty___closed__1;
x_2 = l_Lean_NameSSet_empty___closed__0;
x_3 = l_Lean_SMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_NameSSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSSet_empty___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSSet_empty___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSSet_empty___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_NameSSet_empty___closed__0;
x_4 = l_Lean_NameSSet_empty___closed__1;
x_5 = lean_box(0);
x_6 = l_Lean_SMap_insert___redArg(x_3, x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_NameSSet_empty___closed__0;
x_4 = l_Lean_NameSSet_empty___closed__1;
x_5 = l_Lean_SMap_contains___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_NameSSet_contains(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_NameHashSet_empty___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameHashSet_empty___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameHashSet_empty___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameHashSet_empty___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameHashSet_empty___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameHashSet_empty___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameHashSet_empty___closed__4;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Name_hash___override(x_4);
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
x_26 = l_Lean_Name_hash___override(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_Name_hash___override(x_2);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_18);
x_27 = lean_array_uset(x_4, x_17, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_dec(x_3);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_18);
x_39 = lean_array_uset(x_4, x_17, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_NameHashSet_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_NameHashSet_filter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_3, 2, x_2);
x_2 = x_3;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_12);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_2);
x_2 = x_18;
x_3 = x_14;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_NameHashSet_filter_spec__0(x_1, x_9, x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_length___redArg(x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1(x_1, x_6, x_7, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_10, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
size_t x_13; lean_object* x_14; 
x_13 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2(x_8, x_7, x_13, x_9);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
}
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1(x_1, x_16, x_17, x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
size_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_26 = l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2(x_18, x_17, x_25, x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_NameHashSet_filter_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_NameHashSet_filter_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_15 = l_Lean_Name_isPrefixOf(x_3, x_7);
if (x_15 == 0)
{
x_11 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0(x_6, x_10);
x_11 = x_16;
goto block_14;
}
block_14:
{
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_name_eq(x_5, x_9);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_name_eq(x_4, x_8);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MacroScopesView_isPrefixOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_15 = l_Lean_Name_isSuffixOf(x_3, x_7);
if (x_15 == 0)
{
x_11 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = l_List_beq___at___Lean_MacroScopesView_isPrefixOf_spec__0(x_6, x_10);
x_11 = x_16;
goto block_14;
}
block_14:
{
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_name_eq(x_5, x_9);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_name_eq(x_4, x_8);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MacroScopesView_isSuffixOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_SSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameMap(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_NameMap_instRepr___redArg___closed__0 = _init_l_Lean_NameMap_instRepr___redArg___closed__0();
lean_mark_persistent(l_Lean_NameMap_instRepr___redArg___closed__0);
l_Lean_NameMap_instForInProdName___closed__0 = _init_l_Lean_NameMap_instForInProdName___closed__0();
lean_mark_persistent(l_Lean_NameMap_instForInProdName___closed__0);
l_Lean_NameMap_filter___redArg___closed__0 = _init_l_Lean_NameMap_filter___redArg___closed__0();
lean_mark_persistent(l_Lean_NameMap_filter___redArg___closed__0);
l_Lean_NameSet_empty = _init_l_Lean_NameSet_empty();
lean_mark_persistent(l_Lean_NameSet_empty);
l_Lean_NameSet_instEmptyCollection = _init_l_Lean_NameSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSet_instEmptyCollection);
l_Lean_NameSet_instInhabited = _init_l_Lean_NameSet_instInhabited();
lean_mark_persistent(l_Lean_NameSet_instInhabited);
l_Lean_NameSet_instForInName___closed__0 = _init_l_Lean_NameSet_instForInName___closed__0();
lean_mark_persistent(l_Lean_NameSet_instForInName___closed__0);
l_Lean_NameSet_instAppend___closed__0 = _init_l_Lean_NameSet_instAppend___closed__0();
lean_mark_persistent(l_Lean_NameSet_instAppend___closed__0);
l_Lean_NameSet_instAppend = _init_l_Lean_NameSet_instAppend();
lean_mark_persistent(l_Lean_NameSet_instAppend);
l_Lean_NameSSet_empty___closed__0 = _init_l_Lean_NameSSet_empty___closed__0();
lean_mark_persistent(l_Lean_NameSSet_empty___closed__0);
l_Lean_NameSSet_empty___closed__1 = _init_l_Lean_NameSSet_empty___closed__1();
lean_mark_persistent(l_Lean_NameSSet_empty___closed__1);
l_Lean_NameSSet_empty___closed__2 = _init_l_Lean_NameSSet_empty___closed__2();
lean_mark_persistent(l_Lean_NameSSet_empty___closed__2);
l_Lean_NameSSet_empty = _init_l_Lean_NameSSet_empty();
lean_mark_persistent(l_Lean_NameSSet_empty);
l_Lean_NameSSet_instEmptyCollection = _init_l_Lean_NameSSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSSet_instEmptyCollection);
l_Lean_NameSSet_instInhabited = _init_l_Lean_NameSSet_instInhabited();
lean_mark_persistent(l_Lean_NameSSet_instInhabited);
l_Lean_NameHashSet_empty___closed__0 = _init_l_Lean_NameHashSet_empty___closed__0();
lean_mark_persistent(l_Lean_NameHashSet_empty___closed__0);
l_Lean_NameHashSet_empty___closed__1 = _init_l_Lean_NameHashSet_empty___closed__1();
lean_mark_persistent(l_Lean_NameHashSet_empty___closed__1);
l_Lean_NameHashSet_empty___closed__2 = _init_l_Lean_NameHashSet_empty___closed__2();
lean_mark_persistent(l_Lean_NameHashSet_empty___closed__2);
l_Lean_NameHashSet_empty___closed__3 = _init_l_Lean_NameHashSet_empty___closed__3();
lean_mark_persistent(l_Lean_NameHashSet_empty___closed__3);
l_Lean_NameHashSet_empty___closed__4 = _init_l_Lean_NameHashSet_empty___closed__4();
lean_mark_persistent(l_Lean_NameHashSet_empty___closed__4);
l_Lean_NameHashSet_empty = _init_l_Lean_NameHashSet_empty();
lean_mark_persistent(l_Lean_NameHashSet_empty);
l_Lean_NameHashSet_instEmptyCollection = _init_l_Lean_NameHashSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameHashSet_instEmptyCollection);
l_Lean_NameHashSet_instInhabited = _init_l_Lean_NameHashSet_instInhabited();
lean_mark_persistent(l_Lean_NameHashSet_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
