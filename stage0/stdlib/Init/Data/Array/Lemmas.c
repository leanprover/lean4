// Lean compiler output
// Module: Init.Data.Array.Lemmas
// Imports: Init.Data.Nat.Lemmas Init.Data.List.Impl Init.Data.List.Monadic Init.Data.List.Range Init.Data.List.Nat.TakeDrop Init.Data.List.Nat.Modify Init.Data.List.Nat.Erase Init.Data.List.Monadic Init.Data.List.OfFn Init.Data.Array.Mem Init.Data.Array.DecidableEq Init.TacticsExtra
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListRev___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfDecidableEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListRev___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27Unsafe_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_forIn_x27__cons_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfDecidableEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27Unsafe_loop_match__1_splitter(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27Unsafe_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27Unsafe_loop_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27Unsafe_loop_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_forIn_x27__cons_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__List_forIn_x27__cons_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_3, x_1, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_findSomeM_x3f_match__2_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__List_findSomeM_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_findM_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___rarg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toListRev___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_toListRev___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_toListRev___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Lemmas_0__Nat_fold_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Lemmas_0__Array_take_loop_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_7, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg(x_1, x_3, x_2, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfDecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instDecidableMemOfDecidableEq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Array_instDecidableMemOfDecidableEq___spec__2___rarg(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_contains___at_Array_instDecidableMemOfDecidableEq___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfDecidableEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_instDecidableMemOfDecidableEq___rarg(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Modify(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Erase(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Modify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
