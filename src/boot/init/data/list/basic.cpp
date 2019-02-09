// Lean compiler output
// Module: init.data.list.basic
// Imports: init.core init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_list_has__union___rarg(obj*);
obj* l_list_has__insert___rarg(obj*);
obj* l_list_le;
obj* l_list_find__index___main___at_list_index__of___spec__1(obj*);
obj* l_list_foldl___main___rarg(obj*, obj*, obj*);
obj* l_list_bag__inter(obj*);
obj* l_list_unzip___rarg(obj*);
obj* l_list_empty(obj*);
obj* l_list_foldr___main___at_list_any___spec__1___rarg(obj*, obj*);
obj* l_list_remove__all___rarg(obj*, obj*, obj*);
obj* l_list_repeat___rarg(obj*, obj*);
obj* l_list_length__aux(obj*);
obj* l_list_inter___rarg(obj*, obj*, obj*);
obj* l_list_diff___main___rarg(obj*, obj*, obj*);
obj* l_list_assoc(obj*, obj*);
obj* l_list_unzip(obj*, obj*);
obj* l_list_span___main___rarg(obj*, obj*);
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_list_unzip___main(obj*, obj*);
obj* l_list_update__nth___main(obj*);
obj* l_list_drop___main(obj*);
obj* l_list_nth___main___rarg(obj*, obj*);
obj* l_list_reverse__core___rarg(obj*, obj*);
obj* l_list_index__of(obj*);
obj* l_list_drop__while___main___rarg(obj*, obj*);
obj* l_list_intercalate(obj*);
obj* l_list_reverse__core(obj*);
obj* l_list_has__dec__eq(obj*);
obj* l_list_length__aux___rarg(obj*, obj*);
obj* l_list_union(obj*);
obj* l_list_bag__inter___rarg(obj*, obj*, obj*);
obj* l___private_3066977613__to__list__aux___main(obj*);
obj* l_list_bor(obj*);
obj* l_list_has__dec__eq___main___rarg___boxed(obj*, obj*, obj*);
obj* l_list_assoc___main(obj*, obj*);
obj* l_nat_repeat__core___main___at_list_repeat___spec__1(obj*);
obj* l_list_take___main___rarg(obj*, obj*);
obj* l_list_init___rarg(obj*);
obj* l_list_filter__map___main___rarg(obj*, obj*);
uint8 l_list_empty___main___rarg(obj*);
obj* l_list_filter___main___at_list_inter___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_filter___rarg(obj*, obj*);
obj* l_list_assoc___rarg(obj*, obj*, obj*);
obj* l_list_map_u_2082(obj*, obj*, obj*);
uint8 l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_list_union___spec__1(obj*);
obj* l_list_is__suffix__of___rarg(obj*, obj*, obj*);
obj* l_list_is__prefix__of(obj*);
obj* l_list_length(obj*);
obj* l_list_enum(obj*);
obj* l_list_has__append(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_list_intersperse(obj*);
obj* l_list_init___main___rarg(obj*);
obj* l_list_last___main___rarg(obj*, obj*);
uint8 l_list_has__dec__eq___main___rarg(obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_list_remove__nth___rarg(obj*, obj*);
obj* l_list_foldr1__opt___main(obj*);
obj* l_list_unzip___main___rarg___closed__1;
obj* l___private_3066977613__to__list__aux___rarg(obj*, obj*);
obj* l_list_range__core(obj*, obj*);
obj* l_list_tail___rarg(obj*);
obj* l_list_has__inter___rarg(obj*);
obj* l_list_enum___rarg(obj*);
obj* l_list_filter___main___at_list_remove__all___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_has__union(obj*);
obj* l_list_diff(obj*);
obj* l_list_span(obj*, obj*);
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l_list_nth___main(obj*);
obj* l_list_all(obj*);
obj* l_list_partition___rarg(obj*, obj*);
obj* l_list_ret___rarg(obj*);
obj* l_list_filter___main___at_list_inter___spec__1(obj*);
uint8 l_list_has__decidable__lt___rarg(obj*, obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_list_repeat___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_list_assoc___main___rarg(obj*, obj*, obj*);
obj* l_list_is__suffix__of(obj*);
obj* l_list_bag__inter___main(obj*);
obj* l_list_foldr1___main___rarg(obj*, obj*, obj*);
obj* l_list_repeat(obj*);
uint8 l_list_empty___rarg(obj*);
obj* l_list_last(obj*);
obj* l_list_enum__from___rarg(obj*, obj*);
obj* l_list_any(obj*);
obj* l_list_has__decidable__lt___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_find__index___rarg(obj*, obj*);
obj* l_list_head(obj*);
obj* l_list_ilast___main(obj*);
obj* l_list_filter__map___main(obj*, obj*);
obj* l_list_filter___main(obj*, obj*);
obj* l_list_has__dec__eq___rarg___boxed(obj*, obj*, obj*);
obj* l_bin__tree_to__list___rarg(obj*);
obj* l_list_range(obj*);
obj* l_list_init(obj*);
obj* l_list_inhabited(obj*);
obj* l_list_last___rarg(obj*, obj*);
obj* l_list_has__decidable__lt___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main(obj*, obj*);
obj* l_list_erase(obj*);
obj* l_list_take___main(obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_list_any___rarg(obj*, obj*);
obj* l_list_head___rarg(obj*, obj*);
obj* l_list_remove__all(obj*);
obj* l_list_decidable__eq___rarg(obj*);
obj* l_list_insert___rarg(obj*, obj*, obj*);
obj* l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_has__inter(obj*);
uint8 l_list_has__decidable__le___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_list_all___spec__1___rarg(obj*, obj*);
obj* l_list_has__emptyc(obj*);
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_list_drop(obj*);
obj* l_list_tail___main___rarg(obj*);
obj* l_list_zip__with___main(obj*, obj*, obj*);
uint8 l_not_decidable___rarg(obj*);
obj* l_list_remove__nth(obj*);
obj* l_list_length___rarg(obj*);
obj* l_list_foldr1__opt___main___rarg(obj*, obj*);
obj* l_list_enum__from___main(obj*);
obj* l_list_decidable__mem___main___rarg___boxed(obj*, obj*, obj*);
obj* l_list_drop___main___rarg(obj*, obj*);
obj* l_list_foldr___main___at_list_bor___spec__1(obj*);
obj* l_list_intersperse___main(obj*);
obj* l_list_has__insert(obj*);
uint8 l_list_has__dec__eq___rarg(obj*, obj*, obj*);
obj* l_list_foldr1__opt___rarg(obj*, obj*);
obj* l_list_remove__nth___main___rarg(obj*, obj*);
uint8 l_list_has__decidable__lt___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_filter(obj*, obj*);
obj* l_list_ilast___main___rarg(obj*, obj*);
obj* l_list_head___main___rarg(obj*, obj*);
obj* l_list_foldr___main___at_list_band___spec__1(obj*);
obj* l_list_update__nth___main___rarg(obj*, obj*, obj*);
obj* l_list_zip__with___rarg(obj*, obj*, obj*);
obj* l_list_iota(obj*);
obj* l_list_tail(obj*);
obj* l_list_is__prefix__of___main(obj*);
obj* l_list_has__mem(obj*);
obj* l_list_map_u_2082___main___rarg(obj*, obj*, obj*);
obj* l_list_foldl(obj*, obj*);
obj* l_list_is__prefix__of___main___rarg(obj*, obj*, obj*);
obj* l_list_foldr(obj*, obj*);
obj* l_list_foldr___main___rarg(obj*, obj*, obj*);
obj* l_list_partition(obj*, obj*);
obj* l_list_has__decidable__lt(obj*);
obj* l_list_ret(obj*);
obj* l_list_lt;
obj* l_list_map___main(obj*, obj*);
obj* l_list_decidable__mem___rarg___boxed(obj*, obj*, obj*);
obj* l_list_filter___main___at_list_remove__all___spec__1(obj*);
obj* l_list_filter___main___rarg(obj*, obj*);
obj* l_list_last___main(obj*);
obj* l_list_decidable__mem(obj*);
obj* l_list_head___main(obj*);
obj* l_list_diff___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_list_all___spec__1(obj*);
obj* l_list_reverse(obj*);
obj* l_list_span___rarg(obj*, obj*);
obj* l_list_filter__map(obj*, obj*);
obj* l_list_foldr1__opt(obj*);
obj* l_list_unzip___main___rarg(obj*);
obj* l_list_intercalate___rarg(obj*, obj*);
obj* l_list_all___rarg(obj*, obj*);
obj* l_list_foldr___rarg(obj*, obj*, obj*);
obj* l_list_intersperse___main___rarg(obj*, obj*);
obj* l_list_zip(obj*, obj*);
obj* l_list_foldr1(obj*);
obj* l_list_decidable__mem___main(obj*);
obj* l_list_partition___main___rarg(obj*, obj*);
obj* l_list_erase___main(obj*);
obj* l_list_mem;
obj* l_list_find__index___main(obj*, obj*);
obj* l_list_append(obj*);
obj* l_list_diff___main(obj*);
obj* l_list_update__nth___rarg(obj*, obj*, obj*);
obj* l_list_index__of___rarg(obj*, obj*, obj*);
obj* l___private_3066977613__to__list__aux___main___rarg(obj*, obj*);
obj* l_list_has__decidable__le(obj*);
obj* l_list_drop__while(obj*, obj*);
obj* l_list_has__le(obj*, obj*);
obj* l_list_empty___rarg___boxed(obj*);
obj* l_list_ilast___rarg(obj*, obj*);
obj* l_list_has__decidable__le___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_bin__tree_to__list(obj*);
obj* l_list_bind___rarg(obj*, obj*);
obj* l_list_nth___rarg(obj*, obj*);
uint8 l_list_decidable__mem___main___rarg(obj*, obj*, obj*);
obj* l_list_has__dec__eq___main(obj*);
obj* l_list_empty___main___rarg___boxed(obj*);
obj* l_list_take(obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_list_find__index___main___rarg(obj*, obj*);
obj* l_list_ilast(obj*);
obj* l_list_erase___rarg(obj*, obj*, obj*);
obj* l_list_init___main(obj*);
obj* l_list_erase___main___rarg(obj*, obj*, obj*);
obj* l_list_iota___main(obj*);
obj* l_list_range__core___main(obj*, obj*);
obj* l_list_intersperse___rarg(obj*, obj*);
obj* l_list_decidable__eq(obj*);
obj* l_list_union___rarg(obj*, obj*, obj*);
obj* l_list_band(obj*);
obj* l_list_empty___main(obj*);
obj* l_list_join(obj*);
obj* l_list_reverse__core___main(obj*);
obj* l_list_inter(obj*);
obj* l_list_remove__nth___main(obj*);
obj* l_list_map(obj*, obj*);
obj* l_list_lt___main;
obj* l_list_drop__while___rarg(obj*, obj*);
obj* l_list_span___main(obj*, obj*);
obj* l_list_foldr___main___at_list_any___spec__1(obj*);
obj* l_list_zip___rarg(obj*, obj*);
obj* l_list_map___rarg(obj*, obj*);
uint8 l_list_decidable__mem___rarg(obj*, obj*, obj*);
obj* l_list_filter__map___rarg(obj*, obj*);
obj* l_list_foldr1___rarg(obj*, obj*, obj*);
obj* l_list_mem___main;
obj* l_list_foldr___main(obj*, obj*);
obj* l_list_zip__with(obj*, obj*, obj*);
obj* l_list_foldl___rarg(obj*, obj*, obj*);
obj* l___private_3066977613__to__list__aux(obj*);
obj* l_list_foldr1___main(obj*);
obj* l_list_foldr___main___at_list_union___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_length__aux___main(obj*);
obj* l_list_reverse__core___main___rarg(obj*, obj*);
obj* l_list_is__prefix__of___rarg(obj*, obj*, obj*);
obj* l_list_take___rarg(obj*, obj*);
obj* l_list_nth(obj*);
obj* l_list_has__decidable__lt___main(obj*);
obj* l_list_bind(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_list_bag__inter___main___rarg(obj*, obj*, obj*);
obj* l_list_update__nth(obj*);
obj* l_list_has__lt(obj*, obj*);
obj* l_list_join___main(obj*);
obj* l_list_find__index___main___at_list_index__of___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_tail___main(obj*);
obj* l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1(obj*);
obj* l_list_drop__while___main(obj*, obj*);
obj* l_list_drop___rarg(obj*, obj*);
obj* l_list_join___rarg(obj*);
obj* l_list_map_u_2082___main(obj*, obj*, obj*);
obj* l_list_insert(obj*);
obj* l_list_map_u_2082___rarg(obj*, obj*, obj*);
obj* l_list_find__index(obj*, obj*);
obj* l_list_partition___main(obj*, obj*);
obj* l_list_enum__from(obj*);
obj* l_list_inhabited(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_list_has__dec__eq___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 1;
return x_6;
}
else
{
uint8 x_8; 
lean::dec(x_2);
x_8 = 0;
return x_8;
}
}
else
{
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_18; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_18 = 0;
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_25; uint8 x_26; 
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
lean::dec(x_2);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_19);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
uint8 x_31; 
lean::dec(x_21);
lean::dec(x_11);
lean::dec(x_0);
x_31 = 0;
return x_31;
}
else
{
uint8 x_32; 
x_32 = l_list_has__dec__eq___main___rarg(x_0, x_11, x_21);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = 0;
return x_33;
}
else
{
uint8 x_34; 
x_34 = 1;
return x_34;
}
}
}
}
}
}
obj* l_list_has__dec__eq___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__dec__eq___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_has__dec__eq___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_list_has__dec__eq___main___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_list_has__dec__eq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_list_has__dec__eq___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_has__dec__eq(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__dec__eq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_has__dec__eq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_list_has__dec__eq___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_list_decidable__eq___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__dec__eq___rarg___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_decidable__eq(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_decidable__eq___rarg), 1, 0);
return x_2;
}
}
obj* l_list_reverse__core___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_1);
x_0 = x_5;
x_1 = x_8;
goto _start;
}
}
}
obj* l_list_reverse__core___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_reverse__core___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_reverse__core___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_reverse__core___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_reverse__core(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_reverse__core___rarg), 2, 0);
return x_2;
}
}
obj* l_list_reverse___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_list_reverse__core___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_reverse(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_reverse___rarg), 1, 0);
return x_2;
}
}
obj* l_list_append___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_list_reverse___rarg(x_0);
x_3 = l_list_reverse__core___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_list_append(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_append___rarg), 2, 0);
return x_2;
}
}
obj* l_list_has__append(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_append___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_list_mem___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_list_mem() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_list_has__mem(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_list_decidable__mem___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_14; uint8 x_15; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_1, x_7);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
uint8 x_17; 
x_17 = l_list_decidable__mem___main___rarg(x_0, x_1, x_9);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8 x_23; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_23 = 1;
return x_23;
}
}
}
}
obj* l_list_decidable__mem___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_decidable__mem___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_decidable__mem___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_list_decidable__mem___main___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_list_decidable__mem___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_list_decidable__mem___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_decidable__mem(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_decidable__mem___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_decidable__mem___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_list_decidable__mem___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_list_has__emptyc(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
obj* l_list_erase___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_2);
lean::inc(x_5);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_5, x_2);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_list_erase___main___rarg(x_0, x_7, x_2);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
return x_7;
}
}
}
}
obj* l_list_erase___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_erase___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_erase___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_erase___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_erase(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_list_bag__inter___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
lean::dec(x_2);
return x_1;
}
}
else
{
obj* x_6; obj* x_8; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_10 = x_1;
}
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_0);
return x_2;
}
else
{
uint8 x_18; 
lean::inc(x_2);
lean::inc(x_6);
lean::inc(x_0);
x_18 = l_list_decidable__mem___main___rarg(x_0, x_6, x_2);
if (x_18 == 0)
{
lean::dec(x_10);
lean::dec(x_6);
x_1 = x_8;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::inc(x_6);
lean::inc(x_0);
x_24 = l_list_erase___main___rarg(x_0, x_2, x_6);
x_25 = l_list_bag__inter___main___rarg(x_0, x_8, x_24);
if (lean::is_scalar(x_10)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_10;
}
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
obj* l_list_bag__inter___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_bag__inter___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_bag__inter___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_bag__inter___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_bag__inter(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_bag__inter___rarg), 3, 0);
return x_2;
}
}
obj* l_list_diff___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; uint8 x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_0);
x_13 = l_list_decidable__mem___main___rarg(x_0, x_5, x_1);
if (x_13 == 0)
{
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_17; 
lean::inc(x_0);
x_17 = l_list_erase___main___rarg(x_0, x_1, x_5);
x_1 = x_17;
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_list_diff___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_diff___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_diff___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_diff___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_diff(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_diff___rarg), 3, 0);
return x_2;
}
}
obj* l_list_length__aux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_0 = x_3;
x_1 = x_7;
goto _start;
}
}
}
obj* l_list_length__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_length__aux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_length__aux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_length__aux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_length__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_length__aux___rarg), 2, 0);
return x_2;
}
}
obj* l_list_length___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_list_length__aux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_length(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_length___rarg), 1, 0);
return x_2;
}
}
uint8 l_list_empty___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 1;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 0;
return x_4;
}
}
}
obj* l_list_empty___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_empty___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_list_empty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_list_empty___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_list_empty___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_list_empty___main___rarg(x_0);
return x_1;
}
}
obj* l_list_empty(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_empty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_list_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_list_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_list_nth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; uint8 x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_1, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_5);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_1, x_14);
lean::dec(x_14);
lean::dec(x_1);
x_0 = x_7;
x_1 = x_15;
goto _start;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_1);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_5);
return x_21;
}
}
}
}
obj* l_list_nth___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_nth___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_nth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_nth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_nth(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_nth___rarg), 2, 0);
return x_2;
}
}
obj* l_list_head___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_list_head___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_head___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_head___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_head___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_head(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_head___rarg), 2, 0);
return x_2;
}
}
obj* l_list_tail___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
}
obj* l_list_tail___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_tail___main___rarg), 1, 0);
return x_2;
}
}
obj* l_list_tail___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_tail___main___rarg(x_0);
return x_1;
}
}
obj* l_list_tail(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_tail___rarg), 1, 0);
return x_2;
}
}
obj* l_list_map___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = l_list_map___main___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_map___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map_u_2082___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_11 = x_1;
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_17; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_24; obj* x_25; obj* x_26; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_2, 1);
lean::inc(x_20);
lean::dec(x_2);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_7, x_18);
x_25 = l_list_map_u_2082___main___rarg(x_0, x_9, x_20);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
}
obj* l_list_map_u_2082___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map_u_2082___main___rarg), 3, 0);
return x_6;
}
}
obj* l_list_map_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_map_u_2082___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_map_u_2082(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map_u_2082___rarg), 3, 0);
return x_6;
}
}
obj* l_list_join___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_join___main___rarg(x_5);
x_9 = l_list_append___rarg(x_3, x_8);
return x_9;
}
}
}
obj* l_list_join___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_join___main___rarg), 1, 0);
return x_2;
}
}
obj* l_list_join___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_join___main___rarg(x_0);
return x_1;
}
}
obj* l_list_join(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_join___rarg), 1, 0);
return x_2;
}
}
obj* l_list_filter__map___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_9);
lean::dec(x_11);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_list_filter__map___main___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_9;
}
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
}
obj* l_list_filter__map___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter__map___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_filter__map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_filter__map___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_filter__map(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter__map___rarg), 2, 0);
return x_4;
}
}
obj* l_list_filter___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; uint8 x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
lean::inc(x_3);
lean::inc(x_0);
x_10 = lean::apply_1(x_0, x_3);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
x_16 = l_list_filter___main___rarg(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_list_filter___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_filter___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_filter___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_filter(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter___rarg), 2, 0);
return x_4;
}
}
obj* l_list_partition___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_list_partition___main___rarg(x_0, x_7);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
lean::inc(x_5);
x_18 = lean::apply_1(x_0, x_5);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_21; obj* x_22; 
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_5);
lean::cnstr_set(x_21, 1, x_14);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_16;
}
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
if (lean::is_scalar(x_9)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_9;
}
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_12);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_14);
return x_24;
}
}
}
}
obj* l_list_partition___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_partition___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_partition___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_partition___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_partition(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_partition___rarg), 2, 0);
return x_4;
}
}
obj* l_list_drop__while___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; uint8 x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::inc(x_0);
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_5);
lean::dec(x_0);
return x_1;
}
else
{
lean::dec(x_1);
x_1 = x_5;
goto _start;
}
}
}
}
obj* l_list_drop__while___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_drop__while___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_drop__while___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_drop__while___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_drop__while(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_drop__while___rarg), 2, 0);
return x_4;
}
}
obj* l_list_span___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_5);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_1);
return x_18;
}
else
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_1);
x_20 = l_list_span___main___rarg(x_0, x_7);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
}
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_21);
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_23);
return x_27;
}
}
}
}
obj* l_list_span___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_span___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_span___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_span___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_span(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_span___rarg), 2, 0);
return x_4;
}
}
obj* l_list_find__index___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_list_find__index___main___rarg(x_0, x_7);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_14, x_15);
lean::dec(x_15);
lean::dec(x_14);
return x_16;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_0);
x_21 = lean::mk_nat_obj(0u);
return x_21;
}
}
}
}
obj* l_list_find__index___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_find__index___main___rarg), 2, 0);
return x_4;
}
}
obj* l_list_find__index___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_find__index___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_find__index(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_find__index___rarg), 2, 0);
return x_4;
}
}
obj* l_list_find__index___main___at_list_index__of___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_14; uint8 x_15; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_1, x_7);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = l_list_find__index___main___at_list_index__of___spec__1___rarg(x_0, x_1, x_9);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_17, x_18);
lean::dec(x_18);
lean::dec(x_17);
return x_19;
}
else
{
obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_25 = lean::mk_nat_obj(0u);
return x_25;
}
}
}
}
obj* l_list_find__index___main___at_list_index__of___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_find__index___main___at_list_index__of___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_list_index__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_find__index___main___at_list_index__of___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_index__of(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_index__of___rarg), 3, 0);
return x_2;
}
}
obj* l_list_assoc___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_12, x_2);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
lean::dec(x_14);
x_1 = x_9;
goto _start;
}
else
{
obj* x_27; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_14);
return x_27;
}
}
}
}
obj* l_list_assoc___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_assoc___main___rarg), 3, 0);
return x_4;
}
}
obj* l_list_assoc___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_assoc___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_assoc(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_assoc___rarg), 3, 0);
return x_4;
}
}
obj* l_list_filter___main___at_list_remove__all___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_13; obj* x_14; uint8 x_15; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_0);
x_13 = l_list_decidable__mem___main___rarg(x_0, x_5, x_1);
x_14 = lean::box(x_13);
x_15 = l_not_decidable___rarg(x_14);
if (x_15 == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_19; obj* x_20; 
x_19 = l_list_filter___main___at_list_remove__all___spec__1___rarg(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_list_filter___main___at_list_remove__all___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter___main___at_list_remove__all___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_list_remove__all___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_filter___main___at_list_remove__all___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_list_remove__all(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_remove__all___rarg), 3, 0);
return x_2;
}
}
obj* l_list_update__nth___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_1, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_1, x_13);
lean::dec(x_13);
lean::dec(x_1);
x_17 = l_list_update__nth___main___rarg(x_7, x_14, x_2);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
else
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_5);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
}
}
}
obj* l_list_update__nth___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_update__nth___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_update__nth___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_update__nth___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_update__nth(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_update__nth___rarg), 3, 0);
return x_2;
}
}
obj* l_list_remove__nth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_1, x_11);
lean::dec(x_11);
lean::dec(x_1);
x_15 = l_list_remove__nth___main___rarg(x_5, x_12);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
else
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
}
}
obj* l_list_remove__nth___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_remove__nth___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_remove__nth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_remove__nth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_remove__nth(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_remove__nth___rarg), 2, 0);
return x_2;
}
}
obj* l_list_drop___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_6;
goto _start;
}
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l_list_drop___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_drop___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_drop___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_drop___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_drop(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_drop___rarg), 2, 0);
return x_2;
}
}
obj* l_list_take___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_10 = x_1;
}
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = l_list_take___main___rarg(x_12, x_8);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_19 = lean::box(0);
return x_19;
}
}
}
obj* l_list_take___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_take___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_take___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_take___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_take(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_take___rarg), 2, 0);
return x_2;
}
}
obj* l_list_foldl___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = lean::apply_2(x_0, x_1, x_5);
x_1 = x_11;
x_2 = x_7;
goto _start;
}
}
}
obj* l_list_foldl___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldr___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___rarg(x_0, x_1, x_7);
x_12 = lean::apply_2(x_0, x_5, x_11);
return x_12;
}
}
}
obj* l_list_foldr___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr___main___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldr1___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_12; obj* x_13; 
lean::inc(x_0);
x_12 = l_list_foldr1___main___rarg(x_0, x_6, lean::box(0));
x_13 = lean::apply_2(x_0, x_4, x_12);
return x_13;
}
}
}
obj* l_list_foldr1___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr1___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_foldr1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = l_list_foldr1___main___rarg(x_0, x_1, lean::box(0));
return x_4;
}
}
obj* l_list_foldr1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr1___rarg), 3, 0);
return x_2;
}
}
obj* l_list_foldr1__opt___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_list_foldr1___main___rarg(x_0, x_1, lean::box(0));
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
}
obj* l_list_foldr1__opt___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr1__opt___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_foldr1__opt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr1__opt___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_foldr1__opt(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr1__opt___rarg), 2, 0);
return x_2;
}
}
obj* l_list_foldr___main___at_list_any___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; uint8 x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
lean::dec(x_12);
x_1 = x_8;
goto _start;
}
else
{
lean::dec(x_8);
lean::dec(x_0);
return x_12;
}
}
}
}
obj* l_list_foldr___main___at_list_any___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr___main___at_list_any___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_list_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_list_any___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_list_any(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_any___rarg), 2, 0);
return x_2;
}
}
obj* l_list_foldr___main___at_list_all___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; uint8 x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
lean::dec(x_8);
lean::dec(x_0);
return x_12;
}
else
{
lean::dec(x_12);
x_1 = x_8;
goto _start;
}
}
}
}
obj* l_list_foldr___main___at_list_all___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr___main___at_list_all___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_list_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_list_all___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_list_all(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_all___rarg), 2, 0);
return x_2;
}
}
obj* l_list_foldr___main___at_list_bor___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::unbox(x_4);
if (x_9 == 0)
{
lean::dec(x_4);
x_0 = x_6;
goto _start;
}
else
{
lean::dec(x_6);
return x_4;
}
}
}
}
obj* l_list_bor(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_foldr___main___at_list_bor___spec__1(x_0);
return x_1;
}
}
obj* l_list_foldr___main___at_list_band___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 1;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::unbox(x_4);
if (x_9 == 0)
{
lean::dec(x_6);
return x_4;
}
else
{
lean::dec(x_4);
x_0 = x_6;
goto _start;
}
}
}
}
obj* l_list_band(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_foldr___main___at_list_band___spec__1(x_0);
return x_1;
}
}
obj* l_list_zip__with___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_11 = x_1;
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_17; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_24; obj* x_25; obj* x_26; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_2, 1);
lean::inc(x_20);
lean::dec(x_2);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_7, x_18);
x_25 = l_list_zip__with___main___rarg(x_0, x_9, x_20);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
}
obj* l_list_zip__with___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip__with___main___rarg), 3, 0);
return x_6;
}
}
obj* l_list_zip__with___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_zip__with___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_zip__with(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip__with___rarg), 3, 0);
return x_6;
}
}
obj* l_list_zip___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 0);
x_3 = l_list_zip__with___main___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_list_zip___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_list_zip(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg), 2, 0);
return x_4;
}
}
obj* l_list_unzip___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_list_unzip___main___rarg___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_8 = x_0;
}
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_13 = x_4;
}
x_14 = l_list_unzip___main___rarg(x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_15);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_17);
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
}
obj* _init_l_list_unzip___main___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_list_unzip___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_unzip___main___rarg), 1, 0);
return x_4;
}
}
obj* l_list_unzip___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_unzip___main___rarg(x_0);
return x_1;
}
}
obj* l_list_unzip(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_unzip___rarg), 1, 0);
return x_4;
}
}
obj* l_list_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_5; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_list_decidable__mem___main___rarg(x_0, x_1, x_2);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_list_insert(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_insert___rarg), 3, 0);
return x_2;
}
}
obj* l_list_has__insert___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_insert___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__insert(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__insert___rarg), 1, 0);
return x_2;
}
}
obj* l_list_foldr___main___at_list_union___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_list_union___spec__1___rarg(x_0, x_1, x_7);
x_12 = l_list_insert___rarg(x_0, x_5, x_11);
return x_12;
}
}
}
obj* l_list_foldr___main___at_list_union___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldr___main___at_list_union___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_list_union___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___at_list_union___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_list_union(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_union___rarg), 3, 0);
return x_2;
}
}
obj* l_list_has__union___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_union___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__union(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__union___rarg), 1, 0);
return x_2;
}
}
obj* l_list_filter___main___at_list_inter___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_0);
x_13 = l_list_decidable__mem___main___rarg(x_0, x_5, x_1);
if (x_13 == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_list_filter___main___at_list_inter___spec__1___rarg(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_list_filter___main___at_list_inter___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_filter___main___at_list_inter___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_list_inter___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_filter___main___at_list_inter___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_list_inter(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_inter___rarg), 3, 0);
return x_2;
}
}
obj* l_list_has__inter___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_inter___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__inter(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__inter___rarg), 1, 0);
return x_2;
}
}
obj* l_nat_repeat__core___main___at_list_repeat___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_3);
x_2 = x_8;
x_3 = x_12;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_nat_repeat__core___main___at_list_repeat___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___at_list_repeat___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_list_repeat___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::box(0);
lean::inc(x_1);
x_4 = l_nat_repeat__core___main___at_list_repeat___spec__1___rarg(x_0, x_1, x_1, x_2);
return x_4;
}
}
obj* l_list_repeat(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repeat___rarg), 2, 0);
return x_2;
}
}
obj* l_list_range__core___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_1);
x_0 = x_6;
x_1 = x_10;
goto _start;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l_list_range__core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_range__core___main(x_0, x_1);
return x_2;
}
}
obj* l_list_range(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_list_range__core___main(x_0, x_1);
return x_2;
}
}
obj* l_list_iota___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_4);
x_7 = l_list_iota___main(x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
}
}
obj* l_list_iota(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_iota___main(x_0);
return x_1;
}
}
obj* l_list_enum__from___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_5);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
x_16 = l_list_enum__from___main___rarg(x_13, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_enum__from___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_enum__from___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_enum__from___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_enum__from___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_enum__from(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_enum__from___rarg), 2, 0);
return x_2;
}
}
obj* l_list_enum___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_list_enum__from___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_list_enum(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_enum___rarg), 1, 0);
return x_2;
}
}
obj* l_list_last___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
return x_3;
}
else
{
lean::dec(x_3);
x_0 = x_5;
x_1 = x_0;
goto _start;
}
}
}
obj* l_list_last___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_last___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_last___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_list_last___main___rarg(x_0, lean::box(0));
return x_3;
}
}
obj* l_list_last(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_last___rarg), 2, 0);
return x_2;
}
}
obj* l_list_ilast___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
lean::dec(x_0);
return x_3;
}
else
{
obj* x_11; obj* x_13; 
lean::dec(x_3);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_13);
lean::dec(x_0);
return x_11;
}
else
{
lean::dec(x_11);
x_1 = x_13;
goto _start;
}
}
}
}
}
obj* l_list_ilast___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_ilast___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_ilast___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_ilast___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_ilast(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_ilast___rarg), 2, 0);
return x_2;
}
}
obj* l_list_init___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; obj* x_3; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_5 = x_0;
}
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_5);
return x_3;
}
else
{
obj* x_8; obj* x_9; 
x_8 = l_list_init___main___rarg(x_3);
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_5;
}
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
}
obj* l_list_init___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_init___main___rarg), 1, 0);
return x_2;
}
}
obj* l_list_init___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_init___main___rarg(x_0);
return x_1;
}
}
obj* l_list_init(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_init___rarg), 1, 0);
return x_2;
}
}
obj* l_list_intersperse___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_3);
return x_1;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::inc(x_0);
x_12 = l_list_intersperse___main___rarg(x_0, x_5);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_list_intersperse___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_intersperse___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_intersperse___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_intersperse___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_intersperse(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_intersperse___rarg), 2, 0);
return x_2;
}
}
obj* l_list_intercalate___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_list_intersperse___main___rarg(x_0, x_1);
x_3 = l_list_join___main___rarg(x_2);
return x_3;
}
}
obj* l_list_intercalate(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_intercalate___rarg), 2, 0);
return x_2;
}
}
obj* l_list_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_list_map___main___rarg(x_1, x_0);
x_3 = l_list_join___main___rarg(x_2);
return x_3;
}
}
obj* l_list_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_bind___rarg), 2, 0);
return x_4;
}
}
obj* l_list_ret___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_list_ret(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_ret___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_list_lt___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_list_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_list_has__lt(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
uint8 l_list_has__decidable__lt___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = 0;
return x_8;
}
else
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 1;
return x_10;
}
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_21; 
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_0);
x_21 = 0;
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_30; uint8 x_31; 
x_22 = lean::cnstr_get(x_3, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 1);
lean::inc(x_24);
lean::dec(x_3);
lean::inc(x_22);
lean::inc(x_11);
lean::inc(x_1);
x_30 = lean::apply_2(x_1, x_11, x_22);
x_31 = lean::unbox(x_30);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_34; uint8 x_35; 
lean::inc(x_1);
x_34 = lean::apply_2(x_1, x_22, x_11);
x_35 = lean::unbox(x_34);
lean::dec(x_34);
if (x_35 == 0)
{
uint8 x_37; 
x_37 = l_list_has__decidable__lt___main___rarg(x_0, x_1, x_13, x_24);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = 0;
return x_38;
}
else
{
uint8 x_39; 
x_39 = 1;
return x_39;
}
}
else
{
uint8 x_44; 
lean::dec(x_24);
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_0);
x_44 = 0;
return x_44;
}
}
else
{
uint8 x_51; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_0);
x_51 = 1;
return x_51;
}
}
}
}
}
obj* l_list_has__decidable__lt___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__decidable__lt___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_list_has__decidable__lt___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_list_has__decidable__lt___main___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_list_has__decidable__lt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_list_has__decidable__lt___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_list_has__decidable__lt(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__decidable__lt___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_list_has__decidable__lt___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_list_has__decidable__lt___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_list_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_list_has__le(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
uint8 l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = 0;
return x_8;
}
else
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 1;
return x_10;
}
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_21; 
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_0);
x_21 = 0;
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_30; uint8 x_31; 
x_22 = lean::cnstr_get(x_3, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 1);
lean::inc(x_24);
lean::dec(x_3);
lean::inc(x_22);
lean::inc(x_11);
lean::inc(x_1);
x_30 = lean::apply_2(x_1, x_11, x_22);
x_31 = lean::unbox(x_30);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_34; uint8 x_35; 
lean::inc(x_1);
x_34 = lean::apply_2(x_1, x_22, x_11);
x_35 = lean::unbox(x_34);
lean::dec(x_34);
if (x_35 == 0)
{
uint8 x_37; 
x_37 = l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg(x_0, x_1, x_13, x_24);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = 0;
return x_38;
}
else
{
uint8 x_39; 
x_39 = 1;
return x_39;
}
}
else
{
uint8 x_44; 
lean::dec(x_24);
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_0);
x_44 = 0;
return x_44;
}
}
else
{
uint8 x_51; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_0);
x_51 = 1;
return x_51;
}
}
}
}
}
obj* l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8 l_list_has__decidable__le___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; uint8 x_6; 
x_4 = l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg(x_0, x_1, x_3, x_2);
x_5 = lean::box(x_4);
x_6 = l_not_decidable___rarg(x_5);
return x_6;
}
}
obj* l_list_has__decidable__le(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__decidable__le___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_list_has__decidable__lt___main___at_list_has__decidable__le___spec__1___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_list_has__decidable__le___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_list_has__decidable__le___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_list_is__prefix__of___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = 1;
x_7 = lean::box(x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_17; obj* x_18; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_17 = 0;
x_18 = lean::box(x_17);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_25; uint8 x_26; 
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
lean::dec(x_2);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_19);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
uint8 x_31; obj* x_32; 
lean::dec(x_21);
lean::dec(x_10);
lean::dec(x_0);
x_31 = 0;
x_32 = lean::box(x_31);
return x_32;
}
else
{
x_1 = x_10;
x_2 = x_21;
goto _start;
}
}
}
}
}
obj* l_list_is__prefix__of___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_is__prefix__of___main___rarg), 3, 0);
return x_2;
}
}
obj* l_list_is__prefix__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_is__prefix__of___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_is__prefix__of(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_is__prefix__of___rarg), 3, 0);
return x_2;
}
}
obj* l_list_is__suffix__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_list_reverse___rarg(x_1);
x_4 = l_list_reverse___rarg(x_2);
x_5 = l_list_is__prefix__of___main___rarg(x_0, x_3, x_4);
return x_5;
}
}
obj* l_list_is__suffix__of(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_is__suffix__of___rarg), 3, 0);
return x_2;
}
}
obj* l___private_3066977613__to__list__aux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_0);
return x_1;
}
case 1:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
default:
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l___private_3066977613__to__list__aux___main___rarg(x_9, x_1);
x_0 = x_7;
x_1 = x_12;
goto _start;
}
}
}
}
obj* l___private_3066977613__to__list__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3066977613__to__list__aux___main___rarg), 2, 0);
return x_2;
}
}
obj* l___private_3066977613__to__list__aux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3066977613__to__list__aux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l___private_3066977613__to__list__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3066977613__to__list__aux___rarg), 2, 0);
return x_2;
}
}
obj* l_bin__tree_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l___private_3066977613__to__list__aux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_bin__tree_to__list(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bin__tree_to__list___rarg), 1, 0);
return x_2;
}
}
void initialize_init_core();
void initialize_init_data_nat_basic();
static bool _G_initialized = false;
void initialize_init_data_list_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 initialize_init_data_nat_basic();
 l_list_mem___main = _init_l_list_mem___main();
 l_list_mem = _init_l_list_mem();
 l_list_unzip___main___rarg___closed__1 = _init_l_list_unzip___main___rarg___closed__1();
 l_list_lt___main = _init_l_list_lt___main();
 l_list_lt = _init_l_list_lt();
 l_list_le = _init_l_list_le();
}
