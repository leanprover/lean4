// Lean compiler output
// Module: init.data.list.basic
// Imports: init.core init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_List_eraseDupsAux___rarg(obj*, obj*, obj*);
obj* l_List_map_u2082___main(obj*, obj*, obj*);
obj* l_List_dropWhile(obj*);
obj* l_List_hasDecidableLt___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_join___main(obj*);
obj* l_List_getOpt___main___rarg___boxed(obj*, obj*);
uint8 l_List_elem___rarg(obj*, obj*, obj*);
obj* l_List_head___rarg___boxed(obj*, obj*);
obj* l_List_notElem(obj*);
obj* l_List_foldr1Opt___rarg(obj*, obj*);
obj* l_List_zipWith___main___rarg(obj*, obj*, obj*);
uint8 l_List_any___rarg(obj*, obj*);
obj* l_List_join(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_length___rarg(obj*);
obj* l_List_eraseDupsAux(obj*);
obj* l_List_isEmpty___main___rarg___boxed(obj*);
obj* l_List_getLastOfNonNil___rarg___boxed(obj*, obj*);
obj* l_List_getLastOfNonNil___main(obj*);
obj* l_List_range(obj*);
obj* l_List_unzip(obj*, obj*);
obj* l_List_get___rarg(obj*, obj*, obj*);
obj* l_List_length(obj*);
uint8 l_List_hasDecEq___main___rarg(obj*, obj*, obj*);
obj* l_List_tail___rarg(obj*);
obj* l_List_foldr___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(obj*, obj*, obj*);
obj* l_List_or___boxed(obj*);
obj* l_List_hasDecidableLe(obj*);
obj* l_List_head___main(obj*);
obj* l_List_enumFrom___rarg(obj*, obj*);
obj* l_List_intersperse___main___rarg(obj*, obj*);
obj* l_List_intersperse___main(obj*);
obj* l_List_lengthAux___main(obj*);
obj* l_List_and___boxed(obj*);
obj* l_List_get___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_lengthAux___main___rarg(obj*, obj*);
obj* l_List_head___main___rarg___boxed(obj*, obj*);
obj* l_List_removeAll___rarg(obj*, obj*, obj*);
obj* l_Nat_repeatAux___main___at_List_replicate___spec__1(obj*);
uint8 l_List_foldr___main___at_List_or___spec__1(uint8, obj*);
obj* l_List_rangeAux(obj*, obj*);
obj* l_List_getOpt___main___rarg(obj*, obj*);
obj* l_List_partition___rarg(obj*, obj*);
obj* l_List_foldr1Opt(obj*);
obj* l_List_filterMap(obj*, obj*);
obj* l_List_bind(obj*, obj*);
obj* l_List_take(obj*);
obj* l_List_HasLess(obj*, obj*);
uint8 l_List_hasDecidableLe___rarg(obj*, obj*, obj*, obj*);
obj* l_List_take___main___rarg___boxed(obj*, obj*);
obj* l_List_join___rarg(obj*);
obj* l_List_hasDecEq___rarg___boxed(obj*, obj*, obj*);
obj* l_List_tail(obj*);
obj* l_List_drop___rarg(obj*, obj*);
obj* l_List_getOpt___rarg___boxed(obj*, obj*);
obj* l_List_pure___rarg(obj*);
obj* l_List_take___main(obj*);
obj* l_List_set___main(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_List_hasDecidableLe___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_List_isEmpty___main___rarg(obj*);
obj* l_List_bind___rarg(obj*, obj*);
obj* l_List_hasDecEq___main(obj*);
obj* l_List_reverse(obj*);
obj* l_List_foldr___main___at_List_any___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_List_length___rarg___boxed(obj*);
obj* l_List_foldr1___rarg(obj*, obj*, obj*);
obj* l_List_enumFrom(obj*);
obj* l_List_elem___main(obj*);
obj* l_List_HasEmptyc(obj*);
obj* l_List_reverseAux(obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_List_HasLess___boxed(obj*, obj*);
uint8 l_List_notElem___rarg(obj*, obj*, obj*);
obj* l_List_drop(obj*);
obj* l_List_tail___rarg___boxed(obj*);
obj* l_List_filterAux___rarg(obj*, obj*, obj*);
obj* l_List_isPrefixOf___main(obj*);
obj* l_List_isEqv___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_drop___main(obj*);
obj* l_List_span(obj*);
obj* l_List_init___main___rarg(obj*);
obj* l_List_set___rarg___boxed(obj*, obj*, obj*);
obj* l_List_unzip___main___rarg(obj*);
obj* l_List_foldr___main___rarg(obj*, obj*, obj*);
obj* l_List_getLastOfNonNil(obj*);
obj* l_List_get___rarg___boxed(obj*, obj*, obj*);
obj* l_List_filterAux___main___rarg(obj*, obj*, obj*);
obj* l_List_append(obj*);
obj* l_List_isSuffixOf___rarg___boxed(obj*, obj*, obj*);
obj* l_List_lookup___main(obj*, obj*);
uint8 l_Not_Decidable___rarg(uint8);
obj* l_List_replicate(obj*);
obj* l_List_init(obj*);
uint8 l_List_foldr___main___at_List_all___spec__1___rarg(obj*, uint8, obj*);
obj* l_List_partitionAux___main___rarg(obj*, obj*, obj*);
obj* l_List_partitionAux___main(obj*);
obj* l_List_getLastOfNonNil___rarg(obj*, obj*);
obj* l_List_zipWith___main(obj*, obj*, obj*);
obj* l_List_filterAux(obj*);
obj* l_List_isEqv(obj*);
obj* l_List_partitionAux(obj*);
obj* l_List_foldr___rarg___boxed(obj*, obj*, obj*);
obj* l_List_foldr1Opt___main(obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
obj* l_List_take___rarg(obj*, obj*);
obj* l_List_set(obj*);
uint8 l_List_isSuffixOf___rarg(obj*, obj*, obj*);
obj* l_List_getLast___main___rarg(obj*, obj*);
obj* l_List_span___rarg(obj*, obj*);
obj* l_List_tail___main(obj*);
obj* l_List_elem(obj*);
obj* l_List_join___main___rarg(obj*);
obj* l_List_getOpt(obj*);
obj* l_List_erase___main(obj*);
obj* l_List_get(obj*);
obj* l_List_HasLessEq___boxed(obj*, obj*);
obj* l_List_intersperse___rarg(obj*, obj*);
obj* l_List_lengthAux(obj*);
obj* l_List_drop___main___rarg(obj*, obj*);
obj* l_List_foldr___rarg(obj*, obj*, obj*);
obj* l_List_map_u2082___rarg(obj*, obj*, obj*);
obj* l_List_enumFrom___main(obj*);
obj* l_List_foldl___rarg(obj*, obj*, obj*);
obj* l_List_hasDecidableLt___main(obj*);
obj* l_List_partition___rarg___closed__1;
obj* l_List_spanAux___main___rarg(obj*, obj*, obj*);
obj* l_List_rangeAux___main(obj*, obj*);
obj* l_List_HasLessEq(obj*, obj*);
obj* l_List_foldr1Opt___main___rarg(obj*, obj*);
obj* l_List_foldr1___main___rarg(obj*, obj*, obj*);
obj* l_List_filterAux___main___at_List_removeAll___spec__1(obj*);
uint8 l_List_isPrefixOf___main___rarg(obj*, obj*, obj*);
obj* l_List_DecidableEq(obj*);
obj* l_List_DecidableEq___rarg(obj*);
obj* l_List_filterMap___rarg(obj*, obj*);
obj* l_List_isEmpty___main(obj*);
obj* l_List_erase___main___rarg(obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_List_enum___rarg(obj*);
obj* l_List_isEmpty___rarg___boxed(obj*);
obj* l_List_getOpt___rarg(obj*, obj*);
obj* l_List_isPrefixOf(obj*);
obj* l_List_isEmpty(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_List_eraseDups(obj*);
obj* l_List_elem___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_foldr1(obj*);
obj* l_List_isEqv___rarg___boxed(obj*, obj*, obj*);
obj* l_List_pure(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_List_getLastOfNonNil___main___rarg(obj*, obj*);
uint8 l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_init___rarg(obj*);
obj* l_List_take___rarg___boxed(obj*, obj*);
obj* l_List_map___rarg(obj*, obj*);
uint8 l_List_isEmpty___rarg(obj*);
obj* l_List_init___main(obj*);
obj* l_List_iota___boxed(obj*);
obj* l_List_zipWith(obj*, obj*, obj*);
obj* l_List_isPrefixOf___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_set___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_foldr1___main(obj*);
uint8 l_List_isEqv___main___rarg(obj*, obj*, obj*);
obj* l_List_getLast___rarg(obj*, obj*);
obj* l_List_lengthAux___rarg___boxed(obj*, obj*);
obj* l_List_HasAppend(obj*);
obj* l_List_reverseAux___main(obj*);
obj* l_List_removeAll(obj*);
obj* l_List_dropWhile___main___rarg(obj*, obj*);
obj* l_List_dropWhile___rarg(obj*, obj*);
obj* l_List_set___rarg(obj*, obj*, obj*);
obj* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_List_all___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_List_set___main___rarg(obj*, obj*, obj*);
uint8 l_List_and(obj*);
obj* l_List_head(obj*);
obj* l_List_getLast___rarg___boxed(obj*, obj*);
obj* l_List_map___main(obj*, obj*);
obj* l_List_eraseDupsAux___main___rarg(obj*, obj*, obj*);
obj* l_List_foldr___main(obj*, obj*);
obj* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1(obj*);
uint8 l_List_hasDecidableLt___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___rarg(obj*, obj*, obj*);
obj* l_List_dropWhile___main(obj*);
obj* l_List_reverseAux___main___rarg(obj*, obj*);
obj* l_List_lengthAux___rarg(obj*, obj*);
obj* l_List_lengthAux___main___rarg___boxed(obj*, obj*);
obj* l_List_spanAux___rarg(obj*, obj*, obj*);
uint8 l_List_elem___main___rarg(obj*, obj*, obj*);
obj* l_List_getLastOfNonNil___main___rarg___boxed(obj*, obj*);
obj* l_List_lookup(obj*, obj*);
uint8 l_List_foldr___main___at_List_any___spec__1___rarg(obj*, uint8, obj*);
obj* l_List_filterMap___main___rarg(obj*, obj*);
obj* l_List_getLast(obj*);
obj* l_List_foldl___main(obj*, obj*);
uint8 l_List_all___rarg(obj*, obj*);
obj* l_List_intercalate(obj*);
obj* l_List_zip(obj*, obj*);
uint8 l_List_or(obj*);
obj* l_List_filter(obj*);
obj* l_List_foldr___main___at_List_and___spec__1___boxed(obj*, obj*);
obj* l_List_all___rarg___boxed(obj*, obj*);
obj* l_List_spanAux___main(obj*);
obj* l_List_notElem___rarg___boxed(obj*, obj*, obj*);
uint8 l_List_foldr___main___at_List_and___spec__1(uint8, obj*);
obj* l_List_isSuffixOf(obj*);
obj* l_List_hasDecEq(obj*);
obj* l_List_zipWith___rarg(obj*, obj*, obj*);
obj* l_List_head___main___rarg(obj*, obj*);
obj* l_List_foldr___main___at_List_all___spec__1(obj*);
obj* l_List_zip___rarg(obj*, obj*);
obj* l_List_partitionAux___rarg(obj*, obj*, obj*);
obj* l_List_erase___rarg(obj*, obj*, obj*);
uint8 l_List_isPrefixOf___rarg(obj*, obj*, obj*);
obj* l_List_drop___main___rarg___boxed(obj*, obj*);
obj* l_List_find___rarg(obj*, obj*);
obj* l_List_iota(obj*);
obj* l_List_map_u2082(obj*, obj*, obj*);
obj* l_List_intercalate___rarg(obj*, obj*);
obj* l_List_zip___rarg___closed__1;
obj* l_List_all(obj*);
obj* l_List_any___rarg___boxed(obj*, obj*);
obj* l_List_reverseAux___rarg(obj*, obj*);
obj* l_List_map(obj*, obj*);
obj* l_List_foldr(obj*, obj*);
obj* l_List_tail___main___rarg(obj*);
obj* l_List_get___main(obj*);
obj* l_List_lookup___rarg(obj*, obj*, obj*);
obj* l_List_filterAux___main(obj*);
obj* l_List_find___main___rarg(obj*, obj*);
obj* l_List_filterAux___main___at_List_removeAll___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_filter___rarg(obj*, obj*);
uint8 l_List_hasDecEq___rarg(obj*, obj*, obj*);
obj* l_List_isEqv___main(obj*);
uint8 l_List_hasDecidableLt___rarg(obj*, obj*, obj*, obj*);
obj* l_List_getLast___main___rarg___boxed(obj*, obj*);
obj* l_List_any(obj*);
obj* l_List_eraseDupsAux___main(obj*);
obj* l_List_hasDecEq___main___rarg___boxed(obj*, obj*, obj*);
obj* l_List_iota___main(obj*);
obj* l_List_partition(obj*);
obj* l_List_eraseDups___rarg(obj*, obj*);
obj* l_List_take___main___rarg(obj*, obj*);
obj* l_List_hasDecidableLt(obj*);
obj* l_List_erase(obj*);
obj* l_List_Inhabited(obj*);
obj* l_List_unzip___rarg(obj*);
obj* l_List_getOpt___main(obj*);
obj* l_List_lookup___main___rarg(obj*, obj*, obj*);
obj* l_List_drop___rarg___boxed(obj*, obj*);
obj* l_List_map_u2082___main___rarg(obj*, obj*, obj*);
obj* l_List_get___main___rarg(obj*, obj*, obj*);
obj* l_List_find___main(obj*);
obj* l_List_tail___main___rarg___boxed(obj*);
obj* l_List_spanAux(obj*);
obj* l_List_getLast___main(obj*);
obj* l_List_HasAppend___closed__1;
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_List_foldr___main___at_List_any___spec__1(obj*);
obj* l_List_isPrefixOf___rarg___boxed(obj*, obj*, obj*);
obj* l_List_foldl(obj*, obj*);
obj* l_List_enum(obj*);
uint8 l_List_isEqv___rarg(obj*, obj*, obj*);
obj* l_List_unzip___main(obj*, obj*);
obj* l_List_find(obj*);
obj* l_List_foldr___main___at_List_or___spec__1___boxed(obj*, obj*);
obj* l_List_iota___main___boxed(obj*);
obj* l_List_filterMap___main(obj*, obj*);
obj* l_List_hasDecidableLt___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_intersperse(obj*);
obj* l_List_head___rarg(obj*, obj*);
obj* l_List_replicate___rarg(obj*, obj*);
obj* l_List_elem___rarg___boxed(obj*, obj*, obj*);
obj* l_List_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_List_hasDecEq___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
lean::inc(x_1);
x_11 = lean::apply_2(x_1, x_7, x_9);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = l_List_hasDecEq___main___rarg(x_1, x_8, x_10);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
}
}
}
obj* l_List_hasDecEq___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecEq___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_hasDecEq___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_hasDecEq___main___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_hasDecEq___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_List_hasDecEq___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_hasDecEq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecEq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_hasDecEq___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_hasDecEq___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_DecidableEq___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecEq___rarg___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_DecidableEq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_DecidableEq___rarg), 1, 0);
return x_2;
}
}
obj* l_List_reverseAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::cnstr_set(x_1, 1, x_2);
{
obj* _tmp_0 = x_4;
obj* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_2);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
}
}
}
obj* l_List_reverseAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reverseAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_reverseAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_reverseAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reverseAux___rarg), 2, 0);
return x_2;
}
}
obj* l_List_reverse___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_reverse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reverse___rarg), 1, 0);
return x_2;
}
}
obj* l_List_append___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_List_reverse___rarg(x_1);
x_4 = l_List_reverseAux___main___rarg(x_3, x_2);
return x_4;
}
}
obj* l_List_append(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_append___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_List_HasAppend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_append___rarg), 2, 0);
return x_1;
}
}
obj* l_List_HasAppend(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_HasAppend___closed__1;
return x_2;
}
}
obj* l_List_HasEmptyc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_List_erase___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_5);
x_7 = lean::apply_2(x_1, x_5, x_3);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_List_erase___main___rarg(x_1, x_6, x_3);
lean::cnstr_set(x_2, 1, x_9);
return x_2;
}
else
{
lean::free_heap_obj(x_2);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_10);
x_12 = lean::apply_2(x_1, x_10, x_3);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_List_erase___main___rarg(x_1, x_11, x_3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_1);
return x_11;
}
}
}
}
}
obj* l_List_erase___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_erase___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_erase___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_erase___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_erase(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_List_lengthAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_2, x_4);
lean::dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
}
}
obj* l_List_lengthAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_lengthAux___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_lengthAux___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_lengthAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_lengthAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_lengthAux___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_lengthAux___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_lengthAux___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_length___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_length(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_length___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_length___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_length___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_List_isEmpty___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_List_isEmpty___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isEmpty___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_isEmpty___main___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_isEmpty___main___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_List_isEmpty___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_List_isEmpty___main___rarg(x_1);
return x_2;
}
}
obj* l_List_isEmpty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_List_get___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
}
else
{
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
return x_10;
}
}
}
}
obj* l_List_get___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_get___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_get___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_get___main___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_get___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_get___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_get(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_get___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_get___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_get___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_getOpt___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
}
obj* l_List_getOpt___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getOpt___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getOpt___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getOpt___main___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_getOpt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getOpt___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_getOpt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getOpt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getOpt___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getOpt___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_set___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_3);
return x_1;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
x_11 = l_List_set___main___rarg(x_6, x_10, x_3);
lean::dec(x_10);
lean::cnstr_set(x_1, 1, x_11);
return x_1;
}
else
{
lean::dec(x_5);
lean::cnstr_set(x_1, 0, x_3);
return x_1;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean::nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_2, x_16);
x_18 = l_List_set___main___rarg(x_13, x_17, x_3);
lean::dec(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
else
{
obj* x_20; 
lean::dec(x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
}
}
obj* l_List_set___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_set___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_set___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_set___main___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_set___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_set___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_set(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_set___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_set___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_set___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_head___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_List_head___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_head___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_head___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_head___main___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_head___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_head___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_head(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_head___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_head___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_head___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_tail___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_List_tail___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_tail___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_tail___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_tail___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_tail___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_tail___main___rarg(x_1);
return x_2;
}
}
obj* l_List_tail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_tail___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_tail___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_tail___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = l_List_map___main___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_9);
x_12 = l_List_map___main___rarg(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_map___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map_u2082___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
x_11 = lean::apply_2(x_1, x_6, x_9);
x_12 = l_List_map_u2082___main___rarg(x_1, x_7, x_10);
lean::cnstr_set(x_3, 1, x_12);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_3);
lean::inc(x_1);
x_15 = lean::apply_2(x_1, x_6, x_13);
x_16 = l_List_map_u2082___main___rarg(x_1, x_7, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
obj* l_List_map_u2082___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map_u2082___main___rarg), 3, 0);
return x_4;
}
}
obj* l_List_map_u2082___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_map_u2082___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_map_u2082(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map_u2082___rarg), 3, 0);
return x_4;
}
}
obj* l_List_join___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_List_join___main___rarg(x_4);
x_6 = l_List_append___rarg(x_3, x_5);
return x_6;
}
}
}
obj* l_List_join___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_join___main___rarg), 1, 0);
return x_2;
}
}
obj* l_List_join___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_join___main___rarg(x_1);
return x_2;
}
}
obj* l_List_join(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_join___rarg), 1, 0);
return x_2;
}
}
obj* l_List_filterMap___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
if (lean::obj_tag(x_7) == 0)
{
lean::free_heap_obj(x_2);
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = l_List_filterMap___main___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_13 = lean::apply_1(x_1, x_11);
if (lean::obj_tag(x_13) == 0)
{
x_2 = x_12;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = l_List_filterMap___main___rarg(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
obj* l_List_filterMap___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filterMap___main___rarg), 2, 0);
return x_3;
}
}
obj* l_List_filterMap___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_filterMap___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_filterMap(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filterMap___rarg), 2, 0);
return x_3;
}
}
obj* l_List_filterAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
lean::inc(x_6);
x_8 = lean::apply_1(x_1, x_6);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::free_heap_obj(x_2);
lean::dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean::cnstr_set(x_2, 1, x_3);
{
obj* _tmp_1 = x_7;
obj* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_12 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_12);
x_14 = lean::apply_1(x_1, x_12);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
lean::dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
obj* x_17; 
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
obj* l_List_filterAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filterAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_filterAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_filterAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_filterAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filterAux___rarg), 3, 0);
return x_2;
}
}
obj* l_List_filter___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_filterAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_filter(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filter___rarg), 2, 0);
return x_2;
}
}
obj* l_List_partitionAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean::cnstr_set(x_3, 1, x_8);
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_2);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_3);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get(x_2, 1);
x_18 = lean::cnstr_get(x_3, 0);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
lean::inc(x_16);
x_20 = lean::apply_1(x_1, x_16);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
lean::cnstr_set(x_2, 1, x_19);
lean::cnstr_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean::cnstr_set(x_2, 1, x_18);
lean::cnstr_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_24 = lean::cnstr_get(x_2, 0);
x_25 = lean::cnstr_get(x_2, 1);
x_26 = lean::cnstr_get(x_3, 0);
x_27 = lean::cnstr_get(x_3, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_24);
x_28 = lean::apply_1(x_1, x_24);
x_29 = lean::unbox(x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_30; 
lean::cnstr_set(x_2, 1, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_2);
x_2 = x_25;
x_3 = x_30;
goto _start;
}
else
{
obj* x_32; 
lean::cnstr_set(x_2, 1, x_26);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_2);
lean::cnstr_set(x_32, 1, x_27);
x_2 = x_25;
x_3 = x_32;
goto _start;
}
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint8 x_40; 
x_34 = lean::cnstr_get(x_2, 0);
x_35 = lean::cnstr_get(x_2, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_3, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_3, 1);
lean::inc(x_37);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_38 = x_3;
} else {
 lean::dec_ref(x_3);
 x_38 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_34);
x_39 = lean::apply_1(x_1, x_34);
x_40 = lean::unbox(x_39);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_34);
lean::cnstr_set(x_41, 1, x_37);
if (lean::is_scalar(x_38)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_38;
}
lean::cnstr_set(x_42, 0, x_36);
lean::cnstr_set(x_42, 1, x_41);
x_2 = x_35;
x_3 = x_42;
goto _start;
}
else
{
obj* x_44; obj* x_45; 
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_36);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_37);
x_2 = x_35;
x_3 = x_45;
goto _start;
}
}
}
}
}
obj* l_List_partitionAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_partitionAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_partitionAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_partitionAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_partitionAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_partitionAux___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_List_partition___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_List_partition___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_List_partition___rarg___closed__1;
x_4 = l_List_partitionAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_partition(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_partition___rarg), 2, 0);
return x_2;
}
}
obj* l_List_dropWhile___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::inc(x_1);
x_5 = lean::apply_1(x_1, x_3);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_2;
}
else
{
lean::dec(x_2);
x_2 = x_4;
goto _start;
}
}
}
}
obj* l_List_dropWhile___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_dropWhile___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_dropWhile___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_dropWhile___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_dropWhile(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_dropWhile___rarg), 2, 0);
return x_2;
}
}
obj* l_List_find___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_4);
x_6 = lean::apply_1(x_1, x_4);
x_7 = lean::unbox(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
x_2 = x_5;
goto _start;
}
else
{
obj* x_9; 
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_4);
return x_9;
}
}
}
}
obj* l_List_find___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_find___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_find___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_find___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_find(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_find___rarg), 2, 0);
return x_2;
}
}
uint8 l_List_elem___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_2);
x_7 = lean::apply_2(x_1, x_2, x_5);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8 x_10; 
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_10 = 1;
return x_10;
}
}
}
}
obj* l_List_elem___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_elem___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_elem___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_elem___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_elem(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_elem___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_elem___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_elem___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_notElem___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_List_elem___main___rarg(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_List_notElem(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_notElem___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_notElem___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_notElem___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_eraseDupsAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::inc(x_6);
lean::inc(x_1);
x_8 = l_List_elem___main___rarg(x_1, x_6, x_3);
if (x_8 == 0)
{
lean::cnstr_set(x_2, 1, x_3);
{
obj* _tmp_1 = x_7;
obj* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean::free_heap_obj(x_2);
lean::dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_3);
lean::inc(x_11);
lean::inc(x_1);
x_13 = l_List_elem___main___rarg(x_1, x_11, x_3);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_3);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean::dec(x_11);
x_2 = x_12;
goto _start;
}
}
}
}
}
obj* l_List_eraseDupsAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_eraseDupsAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_eraseDupsAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_eraseDupsAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_eraseDupsAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_eraseDupsAux___rarg), 3, 0);
return x_2;
}
}
obj* l_List_eraseDups___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_eraseDupsAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_eraseDups(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_eraseDups___rarg), 2, 0);
return x_2;
}
}
obj* l_List_spanAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_1);
lean::inc(x_6);
x_8 = lean::apply_1(x_1, x_6);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_1);
x_10 = l_List_reverse___rarg(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_2);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_2, 1);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_2, 0);
lean::dec(x_14);
lean::cnstr_set(x_2, 1, x_3);
{
obj* _tmp_1 = x_7;
obj* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_2);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_3);
x_2 = x_7;
x_3 = x_16;
goto _start;
}
}
}
}
}
obj* l_List_spanAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_spanAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_spanAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_spanAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_spanAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_spanAux___rarg), 3, 0);
return x_2;
}
}
obj* l_List_span___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_spanAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_span(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_span___rarg), 2, 0);
return x_2;
}
}
obj* l_List_lookup___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_2);
x_9 = lean::apply_2(x_1, x_2, x_7);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_8);
return x_12;
}
}
}
}
obj* l_List_lookup___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_lookup___main___rarg), 3, 0);
return x_3;
}
}
obj* l_List_lookup___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_lookup___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_lookup(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_lookup___rarg), 3, 0);
return x_3;
}
}
obj* l_List_filterAux___main___at_List_removeAll___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_2);
lean::inc(x_7);
lean::inc(x_1);
x_9 = l_List_notElem___rarg(x_1, x_7, x_2);
if (x_9 == 0)
{
lean::free_heap_obj(x_3);
lean::dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean::cnstr_set(x_3, 1, x_4);
{
obj* _tmp_2 = x_8;
obj* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_1);
x_14 = l_List_notElem___rarg(x_1, x_12, x_2);
if (x_14 == 0)
{
lean::dec(x_12);
x_3 = x_13;
goto _start;
}
else
{
obj* x_16; 
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_4);
x_3 = x_13;
x_4 = x_16;
goto _start;
}
}
}
}
}
obj* l_List_filterAux___main___at_List_removeAll___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_filterAux___main___at_List_removeAll___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_List_removeAll___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_List_filterAux___main___at_List_removeAll___spec__1___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
obj* l_List_removeAll(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_removeAll___rarg), 3, 0);
return x_2;
}
}
obj* l_List_drop___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_List_drop___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_drop___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_drop___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_drop___main___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_drop___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_drop___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_drop(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_drop___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_drop___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_drop___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_take___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = l_List_take___main___rarg(x_8, x_6);
lean::dec(x_8);
lean::cnstr_set(x_2, 1, x_9);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_1, x_12);
x_14 = l_List_take___main___rarg(x_13, x_11);
lean::dec(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
obj* x_16; 
lean::dec(x_2);
x_16 = lean::box(0);
return x_16;
}
}
}
obj* l_List_take___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_take___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_take___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_take___main___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_take___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_take___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_take(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_take___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_take___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_take___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_foldl___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = lean::apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___rarg), 3, 0);
return x_3;
}
}
obj* l_List_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldl___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_foldl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___rarg), 3, 0);
return x_3;
}
}
obj* l_List_foldr___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_List_foldr___main___rarg(x_1, x_2, x_5);
x_7 = lean::apply_2(x_1, x_4, x_6);
return x_7;
}
}
}
obj* l_List_foldr___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr___main___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_List_foldr___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_foldr___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_foldr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_List_foldr___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_foldr1___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_1);
x_7 = l_List_foldr1___main___rarg(x_1, x_4, lean::box(0));
x_8 = lean::apply_2(x_1, x_6, x_7);
return x_8;
}
}
}
obj* l_List_foldr1___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr1___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldr1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr1___main___rarg(x_1, x_2, lean::box(0));
return x_4;
}
}
obj* l_List_foldr1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr1___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldr1Opt___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = l_List_foldr1___main___rarg(x_1, x_2, lean::box(0));
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
}
obj* l_List_foldr1Opt___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr1Opt___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_foldr1Opt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldr1Opt___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_foldr1Opt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr1Opt___rarg), 2, 0);
return x_2;
}
}
uint8 l_List_foldr___main___at_List_any___spec__1___rarg(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_List_foldr___main___at_List_any___spec__1___rarg(x_1, x_2, x_5);
x_7 = lean::apply_1(x_1, x_4);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
obj* l_List_foldr___main___at_List_any___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr___main___at_List_any___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_List_any___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = 0;
x_4 = l_List_foldr___main___at_List_any___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_List_any(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_any___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_foldr___main___at_List_any___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_foldr___main___at_List_any___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_List_any___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_List_any___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_List_foldr___main___at_List_all___spec__1___rarg(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_List_foldr___main___at_List_all___spec__1___rarg(x_1, x_2, x_5);
x_7 = lean::apply_1(x_1, x_4);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
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
obj* l_List_foldr___main___at_List_all___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldr___main___at_List_all___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_List_all___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = 1;
x_4 = l_List_foldr___main___at_List_all___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_List_all(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_all___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_foldr___main___at_List_all___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_foldr___main___at_List_all___spec__1___rarg(x_1, x_4, x_3);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_List_all___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_List_all___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_List_foldr___main___at_List_or___spec__1(uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::unbox(x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_2, 1);
x_2 = x_5;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
uint8 l_List_or(obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; 
x_2 = 0;
x_3 = l_List_foldr___main___at_List_or___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_List_foldr___main___at_List_or___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_foldr___main___at_List_or___spec__1(x_3, x_2);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_or___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_or(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_List_foldr___main___at_List_and___spec__1(uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::unbox(x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_2, 1);
x_2 = x_6;
goto _start;
}
}
}
}
uint8 l_List_and(obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; 
x_2 = 1;
x_3 = l_List_foldr___main___at_List_and___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_List_foldr___main___at_List_and___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_foldr___main___at_List_and___spec__1(x_3, x_2);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_and___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_and(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_List_zipWith___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
x_11 = lean::apply_2(x_1, x_6, x_9);
x_12 = l_List_zipWith___main___rarg(x_1, x_7, x_10);
lean::cnstr_set(x_3, 1, x_12);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_3);
lean::inc(x_1);
x_15 = lean::apply_2(x_1, x_6, x_13);
x_16 = l_List_zipWith___main___rarg(x_1, x_7, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
obj* l_List_zipWith___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zipWith___main___rarg), 3, 0);
return x_4;
}
}
obj* l_List_zipWith___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_zipWith___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_zipWith(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zipWith___rarg), 3, 0);
return x_4;
}
}
obj* l_List_zip___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_List_zip___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 0);
return x_1;
}
}
obj* l_List_zip___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_List_zip___rarg___closed__1;
x_4 = l_List_zipWith___main___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_zip(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg), 2, 0);
return x_3;
}
}
obj* l_List_unzip___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_List_partition___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_8 = l_List_unzip___main___rarg(x_5);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
lean::cnstr_set(x_1, 1, x_10);
lean::cnstr_set(x_1, 0, x_6);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_8, 1, x_12);
lean::cnstr_set(x_8, 0, x_1);
return x_8;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_8, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_8);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_6);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_21 = l_List_unzip___main___rarg(x_18);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_24 = x_21;
} else {
 lean::dec_ref(x_21);
 x_24 = lean::box(0);
}
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_22);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_23);
if (lean::is_scalar(x_24)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_24;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
}
obj* l_List_unzip___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_unzip___main___rarg), 1, 0);
return x_3;
}
}
obj* l_List_unzip___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_unzip___main___rarg(x_1);
return x_2;
}
}
obj* l_List_unzip(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_unzip___rarg), 1, 0);
return x_3;
}
}
obj* l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
lean::inc(x_1);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_Nat_repeatAux___main___at_List_replicate___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_List_replicate___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_Nat_repeatAux___main___at_List_replicate___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_List_replicate(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_replicate___rarg), 2, 0);
return x_2;
}
}
obj* l_List_rangeAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
lean::inc(x_6);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_List_rangeAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_rangeAux___main(x_1, x_2);
return x_3;
}
}
obj* l_List_range(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_rangeAux___main(x_1, x_2);
return x_3;
}
}
obj* l_List_iota___main(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
x_6 = lean::nat_add(x_5, x_4);
x_7 = l_List_iota___main(x_5);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::box(0);
return x_9;
}
}
}
obj* l_List_iota___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_iota___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_iota(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_iota___main(x_1);
return x_2;
}
}
obj* l_List_iota___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_iota(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_enumFrom___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
lean::dec(x_1);
x_10 = l_List_enumFrom___main___rarg(x_9, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_1, x_14);
lean::dec(x_1);
x_16 = l_List_enumFrom___main___rarg(x_15, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_enumFrom___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_enumFrom___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_enumFrom___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_enumFrom___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_enumFrom(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_enumFrom___rarg), 2, 0);
return x_2;
}
}
obj* l_List_enum___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_List_enumFrom___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_List_enum(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_enum___rarg), 1, 0);
return x_2;
}
}
obj* l_List_getLastOfNonNil___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
return x_4;
}
else
{
x_1 = x_3;
x_2 = lean::box(0);
goto _start;
}
}
}
obj* l_List_getLastOfNonNil___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getLastOfNonNil___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getLastOfNonNil___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLastOfNonNil___main___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_getLastOfNonNil___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLastOfNonNil___main___rarg(x_1, lean::box(0));
return x_3;
}
}
obj* l_List_getLastOfNonNil(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getLastOfNonNil___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getLastOfNonNil___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLastOfNonNil___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_getLast___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = l_List_getLastOfNonNil___main___rarg(x_2, lean::box(0));
return x_3;
}
}
}
obj* l_List_getLast___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getLast___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getLast___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLast___main___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_getLast___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLast___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_getLast(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_getLast___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_List_getLast___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_getLast___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_init___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
lean::inc(x_2);
x_4 = l_List_init___main___rarg(x_2);
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_2, 1);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_2, 0);
lean::dec(x_7);
lean::cnstr_set(x_2, 1, x_4);
lean::cnstr_set(x_2, 0, x_3);
return x_2;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
}
}
}
}
obj* l_List_init___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_init___main___rarg), 1, 0);
return x_2;
}
}
obj* l_List_init___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_init___main___rarg(x_1);
return x_2;
}
}
obj* l_List_init(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_init___rarg), 1, 0);
return x_2;
}
}
obj* l_List_intersperse___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_2, 1);
lean::dec(x_5);
lean::inc(x_3);
lean::inc(x_1);
x_6 = l_List_intersperse___main___rarg(x_1, x_3);
x_7 = !lean::is_exclusive(x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_3, 1);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_3, 0);
lean::dec(x_9);
lean::cnstr_set(x_3, 1, x_6);
lean::cnstr_set(x_3, 0, x_1);
return x_2;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_2, 1, x_10);
return x_2;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_3);
lean::inc(x_1);
x_12 = l_List_intersperse___main___rarg(x_1, x_3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_13 = x_3;
} else {
 lean::dec_ref(x_3);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
obj* l_List_intersperse___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_intersperse___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_intersperse___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_intersperse___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_intersperse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_intersperse___rarg), 2, 0);
return x_2;
}
}
obj* l_List_intercalate___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_List_intersperse___main___rarg(x_1, x_2);
x_4 = l_List_join___main___rarg(x_3);
return x_4;
}
}
obj* l_List_intercalate(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_intercalate___rarg), 2, 0);
return x_2;
}
}
obj* l_List_bind___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_List_map___main___rarg(x_2, x_1);
x_4 = l_List_join___main___rarg(x_3);
return x_4;
}
}
obj* l_List_bind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_bind___rarg), 2, 0);
return x_3;
}
}
obj* l_List_pure___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_List_pure(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_pure___rarg), 1, 0);
return x_2;
}
}
obj* l_List_HasLess(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_List_HasLess___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_HasLess(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_List_hasDecidableLt___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
lean::dec(x_4);
x_6 = 1;
return x_6;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_10);
lean::inc(x_8);
x_12 = lean::apply_2(x_2, x_8, x_10);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; uint8 x_15; 
lean::inc(x_2);
x_14 = lean::apply_2(x_2, x_10, x_8);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_9, x_11);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_19; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_2);
x_19 = 0;
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_2);
x_20 = 1;
return x_20;
}
}
}
}
}
obj* l_List_hasDecidableLt___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecidableLt___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_List_hasDecidableLt___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_List_hasDecidableLt___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_List_hasDecidableLt___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_List_hasDecidableLt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecidableLt___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_List_hasDecidableLt___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_List_hasDecidableLt___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_List_HasLessEq(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_List_HasLessEq___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_HasLessEq(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
lean::dec(x_4);
x_6 = 1;
return x_6;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_10);
lean::inc(x_8);
x_12 = lean::apply_2(x_2, x_8, x_10);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; uint8 x_15; 
lean::inc(x_2);
x_14 = lean::apply_2(x_2, x_10, x_8);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_9, x_11);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_19; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_2);
x_19 = 0;
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_2);
x_20 = 1;
return x_20;
}
}
}
}
}
obj* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8 l_List_hasDecidableLe___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; 
x_5 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_4, x_3);
x_6 = l_Not_Decidable___rarg(x_5);
return x_6;
}
}
obj* l_List_hasDecidableLe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_hasDecidableLe___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_List_hasDecidableLt___main___at_List_hasDecidableLe___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_List_hasDecidableLe___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_List_hasDecidableLe___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_List_isPrefixOf___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = 1;
return x_4;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = 0;
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_1);
x_10 = lean::apply_2(x_1, x_6, x_8);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
uint8 x_12; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
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
obj* l_List_isPrefixOf___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isPrefixOf___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_isPrefixOf___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_isPrefixOf___main___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_isPrefixOf___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_List_isPrefixOf___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_isPrefixOf(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isPrefixOf___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_isPrefixOf___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_isPrefixOf___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_isSuffixOf___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = l_List_reverse___rarg(x_3);
x_6 = l_List_isPrefixOf___main___rarg(x_1, x_4, x_5);
return x_6;
}
}
obj* l_List_isSuffixOf(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isSuffixOf___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_isSuffixOf___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_isSuffixOf___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_isEqv___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_3);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_3);
x_11 = lean::apply_2(x_3, x_7, x_9);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_3);
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
obj* l_List_isEqv___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isEqv___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_isEqv___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_isEqv___main___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_List_isEqv___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_List_isEqv___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_isEqv(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_List_isEqv___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_List_isEqv___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* initialize_init_core(obj*);
obj* initialize_init_data_nat_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_list_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
l_List_HasAppend___closed__1 = _init_l_List_HasAppend___closed__1();
lean::mark_persistent(l_List_HasAppend___closed__1);
l_List_partition___rarg___closed__1 = _init_l_List_partition___rarg___closed__1();
lean::mark_persistent(l_List_partition___rarg___closed__1);
l_List_zip___rarg___closed__1 = _init_l_List_zip___rarg___closed__1();
lean::mark_persistent(l_List_zip___rarg___closed__1);
return w;
}
