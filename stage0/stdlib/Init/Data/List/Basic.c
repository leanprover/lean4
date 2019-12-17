// Lean compiler output
// Module: Init.Data.List.Basic
// Imports: Init.Core Init.Data.Nat.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_List_HasAppend(lean_object*);
lean_object* l_List_erase___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main(lean_object*, lean_object*);
lean_object* l_List_isEqv___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_List_and___spec__1(uint8_t, lean_object*);
lean_object* l_List_foldr___main___at_List_all___spec__1(lean_object*);
lean_object* l_List_intercalate___rarg(lean_object*, lean_object*);
lean_object* l_List_isEqv(lean_object*);
uint8_t l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseIdx___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_partitionAux___main(lean_object*);
lean_object* l_List_contains(lean_object*);
lean_object* l_List_notElem___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_List_erase___main(lean_object*);
lean_object* l_List_findSome_x3f___main(lean_object*, lean_object*);
lean_object* l_List_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_all(lean_object*);
lean_object* l_List_spanAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_HasLessEq(lean_object*, lean_object*);
lean_object* l_List_lookup___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_HasLess___boxed(lean_object*, lean_object*);
lean_object* l_List_spanAux(lean_object*);
lean_object* l_List_iota(lean_object*);
lean_object* l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___main(lean_object*, lean_object*);
lean_object* l_List_unzip___rarg(lean_object*);
uint8_t l_List_notElem___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_isPrefixOf___main(lean_object*);
lean_object* l_List_filterAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverseAux(lean_object*);
lean_object* l_List_lengthAux___rarg___boxed(lean_object*, lean_object*);
uint8_t l_List_isSuffixOf___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isPrefixOf___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_isPrefixOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_join(lean_object*);
lean_object* l_List_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_spanAux___main(lean_object*);
lean_object* l_List_isEqv___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_set___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEqv___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_intersperse___main___rarg(lean_object*, lean_object*);
lean_object* l_List_partition(lean_object*);
uint8_t l_List_isEqv___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_init___main(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* l_List_zipWith___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filter___rarg(lean_object*, lean_object*);
lean_object* l_List_find(lean_object*);
lean_object* l_List_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_dropWhile(lean_object*);
lean_object* l_List_reverseAux___main(lean_object*);
lean_object* l_List_find___main___rarg(lean_object*, lean_object*);
uint8_t l_List_hasDecidableLe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
lean_object* l_List_lengthAux___main(lean_object*);
lean_object* l_List_hasDecEq___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_pure___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_set___main(lean_object*);
lean_object* l_List_unzip___main(lean_object*, lean_object*);
lean_object* l_List_lengthAux(lean_object*);
lean_object* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1(lean_object*);
lean_object* l_List_drop(lean_object*);
lean_object* l_Nat_repeatAux___main___at_List_replicate___spec__1(lean_object*);
lean_object* l_List_find___rarg(lean_object*, lean_object*);
lean_object* l_List_or___boxed(lean_object*);
lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
lean_object* l_List_foldr1Opt___rarg(lean_object*, lean_object*);
lean_object* l_List_isEmpty___rarg___boxed(lean_object*);
uint8_t l_Not_Decidable___rarg(uint8_t);
lean_object* l_List_take___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_HasEmptyc(lean_object*);
lean_object* l_List_zipWith___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___main___rarg(lean_object*, lean_object*);
lean_object* l_List_any(lean_object*);
lean_object* l_List_bind___rarg(lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux___main(lean_object*);
lean_object* l_List_iota___main___boxed(lean_object*);
lean_object* l_List_foldr___main___at_List_any___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse(lean_object*);
lean_object* l_List_intersperse___main(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_enum(lean_object*);
lean_object* l_List_notElem(lean_object*);
lean_object* l_List_pure(lean_object*);
lean_object* l_List_eraseIdx(lean_object*);
lean_object* l_List_hasDecidableLt___main(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_List_all___rarg(lean_object*, lean_object*);
lean_object* l_List_HasLess(lean_object*, lean_object*);
lean_object* l_List_filterAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_zip___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_foldr1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_take___main___rarg(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_List_and___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_filterMap(lean_object*, lean_object*);
lean_object* l_List_eraseIdx___main(lean_object*);
lean_object* l_List_init___rarg(lean_object*);
lean_object* l_List_isSuffixOf(lean_object*);
uint8_t l_List_or(lean_object*);
uint8_t l_List_isPrefixOf___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicate(lean_object*);
lean_object* l_List_isPrefixOf___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_append(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_List_hasDecidableLe(lean_object*);
lean_object* l_List_foldl___main___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_List_or___spec__1(uint8_t, lean_object*);
lean_object* l_List_DecidableEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_enum___rarg(lean_object*);
lean_object* l_List_elem___main(lean_object*);
lean_object* l_List_set(lean_object*);
uint8_t l_List_hasDecEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_hasDecidableLt___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___rarg(lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___rarg(lean_object*, lean_object*);
lean_object* l_List_eraseIdx___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseDups(lean_object*);
lean_object* l_List_hasDecidableLe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_HasBeq___rarg(lean_object*);
lean_object* l_List_hasDecEq(lean_object*);
uint8_t l_List_foldr___main___at_List_any___spec__1___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_List_zipWith(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find___main(lean_object*);
lean_object* l_List_foldr1___main(lean_object*);
lean_object* l_List_hasDecEq___main___at_List_DecidableEq___spec__1(lean_object*);
lean_object* l_List_lookup(lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux(lean_object*);
lean_object* l_List_elem___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_hasDecidableLt(lean_object*);
lean_object* l_List_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lookup___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_take___main(lean_object*);
lean_object* l_List_unzip(lean_object*, lean_object*);
lean_object* l_List_map(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_List_any___spec__1(lean_object*);
lean_object* l_List_length(lean_object*);
lean_object* l_List_removeAll(lean_object*);
lean_object* l_List_map_u2082___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseIdx___main___rarg(lean_object*, lean_object*);
lean_object* l_List_enumFrom___rarg(lean_object*, lean_object*);
lean_object* l_List_rangeAux___main(lean_object*, lean_object*);
lean_object* l_List_HasLessEq___boxed(lean_object*, lean_object*);
lean_object* l_List_filterAux___main(lean_object*);
uint8_t l_List_hasDecidableLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_join___main___rarg(lean_object*);
lean_object* l_List_HasAppend___closed__1;
lean_object* l_List_partitionAux(lean_object*);
lean_object* l_List_isEmpty(lean_object*);
lean_object* l_List_drop___rarg(lean_object*, lean_object*);
lean_object* l_List_take___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_span___rarg(lean_object*, lean_object*);
lean_object* l_List_hasDecEq___main(lean_object*);
lean_object* l_List_erase(lean_object*);
uint8_t l_List_beq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_dropWhile___main___rarg(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_List_partition___rarg___closed__1;
lean_object* l_List_Inhabited(lean_object*);
lean_object* l_List_init(lean_object*);
lean_object* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main(lean_object*, lean_object*);
uint8_t l_List_hasDecidableLt___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_removeAll___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map_u2082___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_isSuffixOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_partitionAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_partitionAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr1___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_List_dropWhile___rarg(lean_object*, lean_object*);
lean_object* l_List_reverseAux___main___rarg(lean_object*, lean_object*);
uint8_t l_List_hasDecEq___main___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_and(lean_object*);
lean_object* l_List_init___main___rarg(lean_object*);
lean_object* l_List_intersperse___rarg(lean_object*, lean_object*);
lean_object* l_List_enumFrom___main___rarg(lean_object*, lean_object*);
lean_object* l_List_spanAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filter(lean_object*);
lean_object* l_List_span(lean_object*);
lean_object* l_List_enumFrom___main(lean_object*);
lean_object* l_List_eraseDupsAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_List_all___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_bind(lean_object*, lean_object*);
lean_object* l_List_zip(lean_object*, lean_object*);
lean_object* l_List_elem___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f(lean_object*, lean_object*);
lean_object* l_List_join___main(lean_object*);
lean_object* l_List_iota___main(lean_object*);
lean_object* l_List_lookup___main(lean_object*, lean_object*);
lean_object* l_List_zip___rarg(lean_object*, lean_object*);
lean_object* l_List_and___boxed(lean_object*);
lean_object* l_List_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_List_removeAll___spec__1(lean_object*);
lean_object* l_List_filterAux(lean_object*);
lean_object* l_List_foldr___main___at_List_or___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map_u2082___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr(lean_object*, lean_object*);
lean_object* l_List_enumFrom(lean_object*);
lean_object* l_List_foldr___main(lean_object*, lean_object*);
lean_object* l_List_beq___main(lean_object*);
lean_object* l_List_unzip___main___rarg(lean_object*);
lean_object* l_List_set___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_rangeAux(lean_object*, lean_object*);
lean_object* l_List_take___rarg(lean_object*, lean_object*);
uint8_t l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_take(lean_object*);
lean_object* l_List_drop___main(lean_object*);
uint8_t l_List_DecidableEq___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_List_all___spec__1___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_List_DecidableEq(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_List_filterMap___rarg(lean_object*, lean_object*);
lean_object* l_List_iota___boxed(lean_object*);
lean_object* l_List_reverseAux___rarg(lean_object*, lean_object*);
lean_object* l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___rarg(lean_object*, lean_object*);
lean_object* l_List_isEqv___main(lean_object*);
lean_object* l_List_isPrefixOf(lean_object*);
lean_object* l_List_dropWhile___main(lean_object*);
uint8_t l_List_beq___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_intercalate(lean_object*);
lean_object* l_List_beq___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq(lean_object*);
lean_object* l_List_zip___rarg___closed__1;
lean_object* l_List_intersperse(lean_object*);
lean_object* l_List_foldr1(lean_object*);
uint8_t l_List_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_HasBeq(lean_object*);
lean_object* l_List_eraseDups___rarg(lean_object*, lean_object*);
lean_object* l_List_length___rarg___boxed(lean_object*);
lean_object* l_List_filterAux___main___at_List_removeAll___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_hasDecEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipWith___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_hasDecidableLt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_List_set___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem(lean_object*);
lean_object* l_List_length___rarg(lean_object*);
lean_object* l_List_foldl(lean_object*, lean_object*);
lean_object* l_List_partition___rarg(lean_object*, lean_object*);
lean_object* l_List_foldr1Opt(lean_object*);
lean_object* l_List_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
uint8_t l_List_hasDecEq___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_List_hasDecEq___main___rarg(x_1, x_8, x_10);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
}
}
}
lean_object* l_List_hasDecEq___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecEq___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_hasDecEq___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_hasDecEq___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_hasDecEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_hasDecEq___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_hasDecEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecEq___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_hasDecEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_hasDecEq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg(x_1, x_8, x_10);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
}
}
}
lean_object* l_List_hasDecEq___main___at_List_DecidableEq___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_List_DecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_DecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_DecidableEq___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_hasDecEq___main___at_List_DecidableEq___spec__1___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_DecidableEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_DecidableEq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_reverseAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_4;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
}
}
}
lean_object* l_List_reverseAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reverseAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_reverseAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_reverseAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reverseAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_reverse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reverse___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___rarg(x_1);
x_4 = l_List_reverseAux___main___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_List_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_append___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_List_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_append___rarg), 2, 0);
return x_1;
}
}
lean_object* l_List_HasAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_HasAppend___closed__1;
return x_2;
}
}
lean_object* l_List_HasEmptyc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_List_erase___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_7 = lean_apply_2(x_1, x_5, x_3);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_erase___main___rarg(x_1, x_6, x_3);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_apply_2(x_1, x_10, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_List_erase___main___rarg(x_1, x_11, x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
}
}
}
lean_object* l_List_erase___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_erase___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_erase___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_erase___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_eraseIdx___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = l_List_eraseIdx___main___rarg(x_5, x_9);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_4);
return x_5;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
x_17 = l_List_eraseIdx___main___rarg(x_12, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
}
}
lean_object* l_List_eraseIdx___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseIdx___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_eraseIdx___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_eraseIdx___main___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_eraseIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_eraseIdx___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_eraseIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseIdx___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_eraseIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_eraseIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_lengthAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_List_lengthAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_lengthAux___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_lengthAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_lengthAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_lengthAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_lengthAux___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_lengthAux___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lengthAux___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_length___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_length(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_length___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_List_length___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_length___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_List_isEmpty___rarg(lean_object* x_1) {
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
lean_object* l_List_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_List_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_set___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = l_List_set___main___rarg(x_6, x_10, x_3);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
x_18 = l_List_set___main___rarg(x_13, x_17, x_3);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
}
lean_object* l_List_set___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_set___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_set___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_set___main___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_set___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_set___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_set(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_set___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_set___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_set___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_map___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_List_map___main___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_List_map___main___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_6, x_9);
x_12 = l_List_map_u2082___main___rarg(x_1, x_7, x_10);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_6, x_13);
x_16 = l_List_map_u2082___main___rarg(x_1, x_7, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
lean_object* l_List_map_u2082___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map_u2082___main___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_map_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map_u2082___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_map_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map_u2082___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_join___main___rarg(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_join___main___rarg(x_4);
x_6 = l_List_append___rarg(x_3, x_5);
return x_6;
}
}
}
lean_object* l_List_join___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_join___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_join___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_join___main___rarg(x_1);
return x_2;
}
}
lean_object* l_List_join(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_join___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_filterMap___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_free_object(x_2);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_filterMap___main___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_13) == 0)
{
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_filterMap___main___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
lean_object* l_List_filterMap___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_filterMap___main___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_filterMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_filterMap___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_filterMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_filterMap___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_filterAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
lean_object* l_List_filterAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_filterAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_filterAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_filter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_filterAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filter___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_partitionAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_16);
x_20 = lean_apply_1(x_1, x_16);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_ctor_set(x_2, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_2);
x_2 = x_25;
x_3 = x_30;
goto _start;
}
else
{
lean_object* x_32; 
lean_ctor_set(x_2, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_27);
x_2 = x_25;
x_3 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_38 = x_3;
} else {
 lean_dec_ref(x_3);
 x_38 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_34);
x_39 = lean_apply_1(x_1, x_34);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_37);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_35;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_2 = x_35;
x_3 = x_45;
goto _start;
}
}
}
}
}
lean_object* l_List_partitionAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_partitionAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_partitionAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partitionAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_partitionAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_partitionAux___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_List_partition___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_List_partition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_partition___rarg___closed__1;
x_4 = l_List_partitionAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_partition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_partition___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_dropWhile___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_dec(x_2);
x_2 = x_4;
goto _start;
}
}
}
}
lean_object* l_List_dropWhile___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_dropWhile___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_dropWhile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_dropWhile___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_dropWhile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_dropWhile___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_find___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
}
lean_object* l_List_find___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_find___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_find___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_find___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_find___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_findSome_x3f___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
}
}
lean_object* l_List_findSome_x3f___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_findSome_x3f___main___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_findSome_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_findSome_x3f___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_findSome_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_findSome_x3f___rarg), 2, 0);
return x_3;
}
}
uint8_t l_List_elem___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
}
}
}
lean_object* l_List_elem___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_elem___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_elem___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_elem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_elem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_elem___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_elem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_elem___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_notElem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
lean_object* l_List_notElem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_notElem___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_notElem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_notElem___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___main___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_List_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_contains___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_eraseDupsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_List_elem___main___rarg(x_1, x_6, x_3);
if (x_8 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_11);
lean_inc(x_1);
x_13 = l_List_elem___main___rarg(x_1, x_11, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
}
}
}
}
lean_object* l_List_eraseDupsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDupsAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_eraseDupsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_eraseDupsAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_eraseDupsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDupsAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_eraseDups___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_eraseDupsAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_eraseDups(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDups___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_spanAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_List_reverse___rarg(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_7;
x_3 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_List_spanAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_spanAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_spanAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_spanAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_spanAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_spanAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_span___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_spanAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_span(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_span___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_lookup___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
}
}
lean_object* l_List_lookup___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_lookup___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_List_lookup___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_lookup(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_lookup___rarg), 3, 0);
return x_3;
}
}
lean_object* l_List_filterAux___main___at_List_removeAll___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_List_notElem___rarg(x_1, x_7, x_2);
if (x_9 == 0)
{
lean_free_object(x_3);
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_1);
x_14 = l_List_notElem___rarg(x_1, x_12, x_2);
if (x_14 == 0)
{
lean_dec(x_12);
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_4);
x_3 = x_13;
x_4 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_List_filterAux___main___at_List_removeAll___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterAux___main___at_List_removeAll___spec__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_removeAll___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_List_filterAux___main___at_List_removeAll___spec__1___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
lean_object* l_List_removeAll(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_removeAll___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_drop___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_List_drop___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_drop___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_drop___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_drop___main___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_drop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_drop___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_drop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_drop___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_drop___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_drop___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_take___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = l_List_take___main___rarg(x_8, x_6);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
x_14 = l_List_take___main___rarg(x_13, x_11);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
}
}
lean_object* l_List_take___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_take___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_take___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_take___main___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_take___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_take___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_take(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_take___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_take___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_take___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_foldl___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_List_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_foldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___rarg), 3, 0);
return x_3;
}
}
lean_object* l_List_foldr___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___main___rarg(x_1, x_2, x_5);
x_7 = lean_apply_2(x_1, x_4, x_6);
return x_7;
}
}
}
lean_object* l_List_foldr___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldr___main___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_List_foldr___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr___main___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_foldr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldr___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_List_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldr1___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_List_foldr1___main___rarg(x_1, x_4, lean_box(0));
x_8 = lean_apply_2(x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l_List_foldr1___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr1___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldr1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr1___main___rarg(x_1, x_2, lean_box(0));
return x_4;
}
}
lean_object* l_List_foldr1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldr1Opt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_foldr1___main___rarg(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
lean_object* l_List_foldr1Opt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr1Opt___rarg), 2, 0);
return x_2;
}
}
uint8_t l_List_foldr___main___at_List_any___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___main___at_List_any___spec__1___rarg(x_1, x_2, x_5);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_List_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___main___at_List_any___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_List_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_List_foldr___main___at_List_any___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_List_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_any___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_foldr___main___at_List_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_List_any___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_List_foldr___main___at_List_all___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___main___at_List_all___spec__1___rarg(x_1, x_2, x_5);
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_6;
}
}
}
}
lean_object* l_List_foldr___main___at_List_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___main___at_List_all___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_List_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = l_List_foldr___main___at_List_all___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_List_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_all___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_List_foldr___main___at_List_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_List_all___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_List_foldr___main___at_List_or___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
uint8_t l_List_or(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_List_foldr___main___at_List_or___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_foldr___main___at_List_or___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_List_or___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_or___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_or(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at_List_and___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
x_2 = x_6;
goto _start;
}
}
}
}
uint8_t l_List_and(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 1;
x_3 = l_List_foldr___main___at_List_and___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_foldr___main___at_List_and___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_List_and___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_and___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_and(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_zipWith___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_6, x_9);
x_12 = l_List_zipWith___main___rarg(x_1, x_7, x_10);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_6, x_13);
x_16 = l_List_zipWith___main___rarg(x_1, x_7, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
lean_object* l_List_zipWith___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_zipWith___main___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_zipWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_zipWith___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_zipWith(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_zipWith___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_zip___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_zip___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_zip___rarg___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_List_zip___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_zip___rarg___closed__1;
x_4 = l_List_zipWith___main___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_List_zip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_zip___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_unzip___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_partition___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_List_unzip___main___rarg(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_6);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_List_unzip___main___rarg(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_List_unzip___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_unzip___main___rarg), 1, 0);
return x_3;
}
}
lean_object* l_List_unzip___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_unzip___main___rarg(x_1);
return x_2;
}
}
lean_object* l_List_unzip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_unzip___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Nat_repeatAux___main___at_List_replicate___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_replicate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_List_replicate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replicate___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_rangeAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_List_rangeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_rangeAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_range(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_rangeAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_iota___main(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_add(x_5, x_4);
x_7 = l_List_iota___main(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* l_List_iota___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_iota___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_iota(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_iota___main(x_1);
return x_2;
}
}
lean_object* l_List_iota___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_iota(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_enumFrom___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
lean_dec(x_1);
x_10 = l_List_enumFrom___main___rarg(x_9, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
x_16 = l_List_enumFrom___main___rarg(x_15, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_List_enumFrom___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enumFrom___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_enumFrom___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_enumFrom___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_enumFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enumFrom___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_enum___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_enumFrom___main___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_List_enum(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enum___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_init___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
lean_inc(x_2);
x_4 = l_List_init___main___rarg(x_2);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
}
}
lean_object* l_List_init___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_init___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_init___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_init___main___rarg(x_1);
return x_2;
}
}
lean_object* l_List_init(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_init___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_intersperse___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_List_intersperse___main___rarg(x_1, x_3);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_6);
lean_ctor_set(x_3, 0, x_1);
return x_2;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_List_intersperse___main___rarg(x_1, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_13 = x_3;
} else {
 lean_dec_ref(x_3);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
lean_object* l_List_intersperse___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intersperse___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_intersperse___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_intersperse___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_intersperse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intersperse___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_intercalate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_intersperse___main___rarg(x_1, x_2);
x_4 = l_List_join___main___rarg(x_3);
return x_4;
}
}
lean_object* l_List_intercalate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intercalate___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_map___main___rarg(x_2, x_1);
x_4 = l_List_join___main___rarg(x_3);
return x_4;
}
}
lean_object* l_List_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_bind___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_pure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_List_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_pure___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_HasLess(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_List_HasLess___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_HasLess(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_List_hasDecidableLt___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
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
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_8);
x_12 = lean_apply_2(x_2, x_8, x_10);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_10, x_8);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_9, x_11);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_19 = 0;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_20 = 1;
return x_20;
}
}
}
}
}
lean_object* l_List_hasDecidableLt___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecidableLt___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_List_hasDecidableLt___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_List_hasDecidableLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_hasDecidableLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecidableLt___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_List_hasDecidableLt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_hasDecidableLt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_HasLessEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_List_HasLessEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_HasLessEq(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
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
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_8);
x_12 = lean_apply_2(x_2, x_8, x_10);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_10, x_8);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_9, x_11);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_19 = 0;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_20 = 1;
return x_20;
}
}
}
}
}
lean_object* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8_t l_List_hasDecidableLe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_4, x_3);
x_6 = l_Not_Decidable___rarg(x_5);
return x_6;
}
}
lean_object* l_List_hasDecidableLe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecidableLe___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_hasDecidableLe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_hasDecidableLe___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_List_isPrefixOf___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_6, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_2 = x_7;
x_3 = x_9;
goto _start;
}
}
}
}
}
lean_object* l_List_isPrefixOf___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isPrefixOf___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_isPrefixOf___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isPrefixOf___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_isPrefixOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isPrefixOf___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_isPrefixOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isPrefixOf___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_isPrefixOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isPrefixOf___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_isSuffixOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = l_List_reverse___rarg(x_3);
x_6 = l_List_isPrefixOf___main___rarg(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_List_isSuffixOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isSuffixOf___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_isSuffixOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isSuffixOf___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_isEqv___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_13 = 0;
return x_13;
}
else
{
x_1 = x_8;
x_2 = x_10;
goto _start;
}
}
}
}
}
lean_object* l_List_isEqv___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isEqv___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_isEqv___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isEqv___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_isEqv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isEqv___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_isEqv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_isEqv___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isEqv___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_beq___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
x_2 = x_8;
x_3 = x_10;
goto _start;
}
}
}
}
}
lean_object* l_List_beq___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_beq___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_beq___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_beq___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_beq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_beq___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_beq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_beq___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_beq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_beq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_HasBeq___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_beq___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_HasBeq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_HasBeq___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_List_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_HasAppend___closed__1 = _init_l_List_HasAppend___closed__1();
lean_mark_persistent(l_List_HasAppend___closed__1);
l_List_partition___rarg___closed__1 = _init_l_List_partition___rarg___closed__1();
lean_mark_persistent(l_List_partition___rarg___closed__1);
l_List_zip___rarg___closed__1 = _init_l_List_zip___rarg___closed__1();
lean_mark_persistent(l_List_zip___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
