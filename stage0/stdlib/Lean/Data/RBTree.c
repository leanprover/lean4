// Lean compiler output
// Module: Lean.Data.RBTree
// Imports: public import Lean.Data.RBMap
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
static lean_object* l_Lean_RBTree_toArray___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_subset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_contains(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_RBTree_toList___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_subset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object*);
lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_min___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_RBNode_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBTree_toArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedRBTree(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkRBTree(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instEmptyCollectionRBTree(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBTree_empty(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBTree_depth___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_depth___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBTree_depth(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_RBNode_fold___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Lean_RBNode_fold___redArg(x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBTree_fold(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_RBNode_revFold___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Lean_RBNode_revFold___redArg(x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBTree_revFold(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_RBNode_foldM___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = l_Lean_RBNode_foldM___redArg(x_5, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RBTree_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_foldM___redArg(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_foldM___redArg(x_4, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBTree_forM(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_1, x_8, x_2, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(x_12, 0, x_8);
x_13 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_5, x_12, x_6, x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RBTree_forIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_1, x_9, x_3, x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBTree_instForInOfMonad(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBTree_isEmpty___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_RBTree_toList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBTree_toList___redArg___lam__0), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_RBTree_toList___redArg___closed__0;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_revFold___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_toList___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_toList(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_RBTree_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBTree_toArray___redArg___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBTree_toArray___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_RBTree_toArray___redArg___closed__0;
x_3 = l_Lean_RBTree_toArray___redArg___closed__1;
x_4 = l_Lean_RBNode_fold___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_toArray___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_toArray(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___redArg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBTree_min___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_min___redArg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_min(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___redArg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBTree_max___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_max___redArg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_max(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_RBTree_instRepr___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.rbtreeOf ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_RBTree_instRepr___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBTree_instRepr___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_RBTree_instRepr___redArg___lam__0___closed__1;
x_5 = l_Lean_RBTree_toList___redArg(x_2);
x_6 = l_List_repr___redArg(x_1, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_instRepr___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_instRepr(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_insert___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_insert___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_erase___redArg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_6 = l_Lean_RBTree_ofList___redArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_RBNode_insert___redArg(x_1, x_6, x_4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_ofList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_findCore___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec_ref(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_contains___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_findCore___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec_ref(x_5);
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBTree_contains(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec_ref(x_1);
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
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_9, x_3, x_4);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
default: 
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_12, x_3, x_4);
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
lean_inc_ref(x_1);
lean_inc(x_18);
lean_inc(x_3);
x_21 = lean_apply_2(x_1, x_3, x_18);
x_22 = lean_unbox(x_21);
switch (x_22) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_17, x_3, x_4);
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
lean_dec_ref(x_1);
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
x_26 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_20, x_3, x_4);
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
lean_inc_ref(x_1);
lean_inc(x_29);
lean_inc(x_3);
x_33 = lean_apply_2(x_1, x_3, x_29);
x_34 = lean_unbox(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; 
x_35 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_28, x_3, x_4);
if (lean_obj_tag(x_35) == 1)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
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
if (lean_obj_tag(x_37) == 1)
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_35);
x_56 = lean_ctor_get(x_37, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_37, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_37, 3);
lean_inc(x_59);
lean_dec_ref(x_37);
x_41 = x_56;
x_42 = x_57;
x_43 = x_58;
x_44 = x_59;
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
if (lean_obj_tag(x_40) == 1)
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_35);
x_61 = lean_ctor_get(x_40, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_40, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_40, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_40, 3);
lean_inc(x_64);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_64;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_65; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_32);
x_65 = !lean_is_exclusive(x_40);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_40, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_40, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_40, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_40, 0);
lean_dec(x_69);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_7);
return x_40;
}
else
{
lean_object* x_70; 
lean_dec(x_40);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_35);
lean_ctor_set(x_70, 1, x_29);
lean_ctor_set(x_70, 2, x_30);
lean_ctor_set(x_70, 3, x_31);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_71 = !lean_is_exclusive(x_37);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_37, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_37, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_37, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_37, 0);
lean_dec(x_75);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_76; 
lean_dec(x_37);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_29);
lean_ctor_set(x_76, 2, x_30);
lean_ctor_set(x_76, 3, x_31);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_7);
return x_76;
}
}
}
}
else
{
if (lean_obj_tag(x_40) == 1)
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_35);
x_78 = lean_ctor_get(x_40, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 3);
lean_inc(x_81);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_78;
x_45 = x_79;
x_46 = x_80;
x_47 = x_81;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_82; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_82 = !lean_is_exclusive(x_40);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_40, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_40, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_40, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_40, 0);
lean_dec(x_86);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_7);
return x_40;
}
else
{
lean_object* x_87; 
lean_dec(x_40);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_35);
lean_ctor_set(x_87, 1, x_29);
lean_ctor_set(x_87, 2, x_30);
lean_ctor_set(x_87, 3, x_31);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_7);
return x_87;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_35);
lean_ctor_set(x_88, 1, x_29);
lean_ctor_set(x_88, 2, x_30);
lean_ctor_set(x_88, 3, x_31);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_7);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_89 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_89, 0, x_35);
lean_ctor_set(x_89, 1, x_29);
lean_ctor_set(x_89, 2, x_30);
lean_ctor_set(x_89, 3, x_31);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_7);
return x_89;
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
else
{
lean_object* x_90; 
if (lean_is_scalar(x_32)) {
 x_90 = lean_alloc_ctor(1, 4, 1);
} else {
 x_90 = x_32;
}
lean_ctor_set(x_90, 0, x_35);
lean_ctor_set(x_90, 1, x_29);
lean_ctor_set(x_90, 2, x_30);
lean_ctor_set(x_90, 3, x_31);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_7);
return x_90;
}
}
case 1:
{
lean_object* x_91; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_1);
if (lean_is_scalar(x_32)) {
 x_91 = lean_alloc_ctor(1, 4, 1);
} else {
 x_91 = x_32;
}
lean_ctor_set(x_91, 0, x_28);
lean_ctor_set(x_91, 1, x_3);
lean_ctor_set(x_91, 2, x_4);
lean_ctor_set(x_91, 3, x_31);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_7);
return x_91;
}
default: 
{
lean_object* x_92; 
x_92 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_31, x_3, x_4);
if (lean_obj_tag(x_92) == 1)
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get_uint8(x_92, sizeof(void*)*4);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 3);
lean_inc(x_97);
if (x_93 == 0)
{
if (lean_obj_tag(x_94) == 1)
{
uint8_t x_112; 
x_112 = lean_ctor_get_uint8(x_94, sizeof(void*)*4);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_92);
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_94, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_94, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_94, 3);
lean_inc(x_116);
lean_dec_ref(x_94);
x_98 = x_28;
x_99 = x_29;
x_100 = x_30;
x_101 = x_113;
x_102 = x_114;
x_103 = x_115;
x_104 = x_116;
x_105 = x_95;
x_106 = x_96;
x_107 = x_97;
goto block_111;
}
else
{
if (lean_obj_tag(x_97) == 1)
{
uint8_t x_117; 
x_117 = lean_ctor_get_uint8(x_97, sizeof(void*)*4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_92);
x_118 = lean_ctor_get(x_97, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_97, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_97, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_97, 3);
lean_inc(x_121);
lean_dec_ref(x_97);
x_98 = x_28;
x_99 = x_29;
x_100 = x_30;
x_101 = x_94;
x_102 = x_95;
x_103 = x_96;
x_104 = x_118;
x_105 = x_119;
x_106 = x_120;
x_107 = x_121;
goto block_111;
}
else
{
uint8_t x_122; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_32);
x_122 = !lean_is_exclusive(x_97);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_97, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_97, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_97, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_97, 0);
lean_dec(x_126);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 2, x_30);
lean_ctor_set(x_97, 1, x_29);
lean_ctor_set(x_97, 0, x_28);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_7);
return x_97;
}
else
{
lean_object* x_127; 
lean_dec(x_97);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_28);
lean_ctor_set(x_127, 1, x_29);
lean_ctor_set(x_127, 2, x_30);
lean_ctor_set(x_127, 3, x_92);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_7);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_32);
x_128 = !lean_is_exclusive(x_94);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_94, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_94, 2);
lean_dec(x_130);
x_131 = lean_ctor_get(x_94, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_94, 0);
lean_dec(x_132);
lean_ctor_set(x_94, 3, x_92);
lean_ctor_set(x_94, 2, x_30);
lean_ctor_set(x_94, 1, x_29);
lean_ctor_set(x_94, 0, x_28);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_7);
return x_94;
}
else
{
lean_object* x_133; 
lean_dec(x_94);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_28);
lean_ctor_set(x_133, 1, x_29);
lean_ctor_set(x_133, 2, x_30);
lean_ctor_set(x_133, 3, x_92);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_7);
return x_133;
}
}
}
}
else
{
if (lean_obj_tag(x_97) == 1)
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_97, sizeof(void*)*4);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_92);
x_135 = lean_ctor_get(x_97, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_97, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_97, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_97, 3);
lean_inc(x_138);
lean_dec_ref(x_97);
x_98 = x_28;
x_99 = x_29;
x_100 = x_30;
x_101 = x_94;
x_102 = x_95;
x_103 = x_96;
x_104 = x_135;
x_105 = x_136;
x_106 = x_137;
x_107 = x_138;
goto block_111;
}
else
{
uint8_t x_139; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_32);
x_139 = !lean_is_exclusive(x_97);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_97, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_97, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_97, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_97, 0);
lean_dec(x_143);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 2, x_30);
lean_ctor_set(x_97, 1, x_29);
lean_ctor_set(x_97, 0, x_28);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_7);
return x_97;
}
else
{
lean_object* x_144; 
lean_dec(x_97);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_28);
lean_ctor_set(x_144, 1, x_29);
lean_ctor_set(x_144, 2, x_30);
lean_ctor_set(x_144, 3, x_92);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_7);
return x_144;
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_32);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_28);
lean_ctor_set(x_145, 1, x_29);
lean_ctor_set(x_145, 2, x_30);
lean_ctor_set(x_145, 3, x_92);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_7);
return x_145;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_32);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_28);
lean_ctor_set(x_146, 1, x_29);
lean_ctor_set(x_146, 2, x_30);
lean_ctor_set(x_146, 3, x_92);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_7);
return x_146;
}
block_111:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
if (lean_is_scalar(x_32)) {
 x_108 = lean_alloc_ctor(1, 4, 1);
} else {
 x_108 = x_32;
}
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_100);
lean_ctor_set(x_108, 3, x_101);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_7);
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_7);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_102);
lean_ctor_set(x_110, 2, x_103);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_93);
return x_110;
}
}
else
{
lean_object* x_147; 
if (lean_is_scalar(x_32)) {
 x_147 = lean_alloc_ctor(1, 4, 1);
} else {
 x_147 = x_32;
}
lean_ctor_set(x_147, 0, x_28);
lean_ctor_set(x_147, 1, x_29);
lean_ctor_set(x_147, 2, x_30);
lean_ctor_set(x_147, 3, x_92);
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_7);
return x_147;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_box(0);
lean_inc_ref(x_1);
x_7 = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(x_1, x_2, x_4, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_fromList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_box(0);
lean_inc_ref(x_1);
x_9 = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(x_1, x_5, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(x_2, x_1, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBTree_fromArray___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_fromArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_fromArray(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_all___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_RBNode_all___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBTree_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_RBNode_all___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBTree_all(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_RBNode_any___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBTree_any___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_RBNode_any___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBTree_any(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec_ref(x_3);
lean_inc(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(x_2, x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_8);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_1, x_2, x_5);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_subset___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBTree_subset(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_4 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_3, x_1, x_2);
if (x_4 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(x_2, x_1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_seteq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBTree_seteq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBTree_seteq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_7 = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(x_1, x_2, x_4);
x_8 = lean_box(0);
lean_inc_ref(x_1);
x_9 = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(x_1, x_7, x_5, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBTree_union___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
uint8_t x_11; 
x_11 = l_Lean_RBNode_isBlack___redArg(x_5);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_5);
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_12);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
x_14 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_5);
x_15 = l_Lean_RBNode_balLeft___redArg(x_14, x_6, x_7, x_8);
return x_15;
}
}
case 1:
{
lean_object* x_16; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = l_Lean_RBNode_appendTrees___redArg(x_5, x_8);
return x_16;
}
default: 
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___redArg(x_8);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_8);
lean_ctor_set(x_3, 3, x_19);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_18);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_3);
x_20 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_8);
x_21 = l_Lean_RBNode_balRight___redArg(x_5, x_6, x_7, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc_ref(x_1);
lean_inc(x_23);
lean_inc(x_2);
x_26 = lean_apply_2(x_1, x_2, x_23);
x_27 = lean_unbox(x_26);
switch (x_27) {
case 0:
{
uint8_t x_28; 
x_28 = l_Lean_RBNode_isBlack___redArg(x_22);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_22);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_22);
x_33 = l_Lean_RBNode_balLeft___redArg(x_32, x_23, x_24, x_25);
return x_33;
}
}
case 1:
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = l_Lean_RBNode_appendTrees___redArg(x_22, x_25);
return x_34;
}
default: 
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 0;
x_37 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_25);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_25);
x_40 = l_Lean_RBNode_balRight___redArg(x_22, x_23, x_24, x_39);
return x_40;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_5 = l_Lean_RBNode_setBlack___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_7 = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(x_1, x_2, x_4);
lean_inc_ref(x_1);
x_8 = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(x_1, x_5, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBTree_filter___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBTree_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_RBMap_filter___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBTree_filter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBTree_fromList___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBTree_fromList___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RBTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_RBMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RBTree_toList___redArg___closed__0 = _init_l_Lean_RBTree_toList___redArg___closed__0();
lean_mark_persistent(l_Lean_RBTree_toList___redArg___closed__0);
l_Lean_RBTree_toArray___redArg___closed__0 = _init_l_Lean_RBTree_toArray___redArg___closed__0();
lean_mark_persistent(l_Lean_RBTree_toArray___redArg___closed__0);
l_Lean_RBTree_toArray___redArg___closed__1 = _init_l_Lean_RBTree_toArray___redArg___closed__1();
lean_mark_persistent(l_Lean_RBTree_toArray___redArg___closed__1);
l_Lean_RBTree_instRepr___redArg___lam__0___closed__0 = _init_l_Lean_RBTree_instRepr___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_RBTree_instRepr___redArg___lam__0___closed__0);
l_Lean_RBTree_instRepr___redArg___lam__0___closed__1 = _init_l_Lean_RBTree_instRepr___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
