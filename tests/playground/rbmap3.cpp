// Lean compiler output
// Module: rbmap3
// Imports: init.core init.io init.data.ordering.default
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/init_module.h"
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
obj* l_rbnode_fold(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj*, obj*, obj*);
obj* l_rbnode_is__red___main(obj*, obj*);
obj* l_rbmap_find___main(obj*, obj*, obj*);
obj* l_rbnode_fold___main(obj*, obj*, obj*);
obj* l_rbmap_rev__fold(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_mk__map__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_rotate__left(obj*, obj*);
obj* l_mk__map(obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj*, obj*, obj*);
obj* l_rbnode_any___main(obj*, obj*);
obj* l_mk__map__aux(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_max___main___rarg(obj*);
obj* l_rbnode_all___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_rbmap;
obj* l_rbmap_insert___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_rbmap_all___main(obj*, obj*, obj*);
obj* l_rbnode_fold___rarg(obj*, obj*, obj*);
obj* l_rbmap_fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main(obj*, obj*, obj*);
obj* l_rbnode_max___rarg(obj*);
obj* l_rbmap_min(obj*, obj*, obj*);
obj* l_rbmap_find__core___rarg(obj*, obj*, obj*);
uint8 l_rbnode_flip(uint8);
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_rbnode_set__black(obj*, obj*);
obj* l_rbnode_ins___main(obj*, obj*, obj*);
obj* l_rbmap_find(obj*, obj*, obj*);
obj* l_rbnode_all(obj*, obj*);
obj* l_rbnode_find(obj*, obj*);
obj* l_rbnode_flip__colors___main___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj*, obj*);
obj* l_rbnode_find__core___main(obj*, obj*, obj*);
obj* l_rbnode_rotate__right___main___rarg(obj*);
obj* l_rbnode_min___main___rarg(obj*);
obj* l_mk__rbmap(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj*, obj*);
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_any___main___rarg(obj*, obj*);
obj* l_rbnode_min(obj*, obj*);
obj* l_rbmap_of__list(obj*, obj*, obj*);
obj* l_rbnode_depth___main(obj*, obj*);
obj* l_rbnode_find__core___rarg(obj*, obj*, obj*);
obj* l_rbmap_min___main___rarg(obj*);
obj* l_rbmap__of___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__4(obj*, obj*, obj*);
uint8 l_rbmap_contains___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr___rarg___closed__1;
obj* l_rbnode_rev__fold(obj*, obj*, obj*);
obj* l_rbnode_rotate__right___main(obj*, obj*);
obj* l_rbnode_depth___main___rarg(obj*, obj*);
obj* l_rbmap_fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_rev__fold___rarg(obj*, obj*, obj*);
obj* l_mk__map__aux___main(obj*, obj*);
obj* l_rbnode_find___main(obj*, obj*);
obj* l_rbmap_insert___main___at_mk__map__aux___main___spec__1(obj*, obj*, uint8);
extern obj* l_list_repr___main___rarg___closed__1;
obj* l_rbnode_rev__fold___main(obj*, obj*, obj*);
obj* l_rbmap_to__list___main___rarg(obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rotate__left___main___rarg(obj*);
obj* l_rbmap_empty___main(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_rbmap_contains(obj*, obj*, obj*);
obj* l_rbmap_empty___main___rarg___boxed(obj*);
obj* l_rbnode_find__core(obj*, obj*, obj*);
obj* l_rbnode_insert___at_mk__map__aux___main___spec__2___boxed(obj*, obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* _lean_main(obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj*, obj*, obj*);
obj* l_rbnode_flip__color___main(obj*, obj*);
uint8 l_rbmap_empty___main___rarg(obj*);
uint8 l_rbnode_flip___main(uint8);
uint8 l_rbnode_is__red___rarg(obj*);
obj* l_rbmap_any___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap__of(obj*, obj*);
obj* l_rbnode_all___main___rarg(obj*, obj*);
obj* l_rbnode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_flip___boxed(obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj*, obj*, obj*);
obj* l_rbmap_insert___main(obj*, obj*, obj*);
obj* l_rbmap_fold(obj*, obj*, obj*, obj*);
extern obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_string_to__nat(obj*);
obj* l_rbnode_rotate__right___rarg(obj*, obj*);
obj* l_rbnode_set__black___rarg(obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj*, obj*, obj*);
obj* l_rbnode_is__red___rarg___boxed(obj*);
extern obj* l_list_repr___main___rarg___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_rbnode_flip__color(obj*, obj*);
obj* l_rbmap_any(obj*, obj*, obj*, obj*);
obj* l_rbnode_is__red(obj*, obj*);
obj* l_rbmap_find__core___main(obj*, obj*, obj*);
obj* l_rbnode_insert___at_mk__map__aux___main___spec__2(obj*, obj*, uint8);
obj* l_rbnode_flip__color___main___rarg(obj*);
obj* l_rbnode_ins___main___at_mk__map__aux___main___spec__3(obj*, uint8, obj*);
extern obj* l_string_join___closed__1;
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj*, obj*);
obj* l_rbnode_any___rarg(obj*, obj*);
obj* l_rbnode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_max___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj*, obj*, obj*);
obj* l_rbmap_from__list(obj*, obj*);
obj* l_rbnode_lower__bound(obj*, obj*, obj*);
obj* l_rbmap_max(obj*, obj*, obj*);
obj* l_rbmap_to__list(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__5(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj*, obj*, obj*);
obj* l_rbmap_insert(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj*, obj*, obj*);
uint8 l_rbmap_empty___rarg(obj*);
obj* l_rbmap_lower__bound___main(obj*, obj*, obj*);
obj* l_rbmap_all___rarg(obj*, obj*);
obj* l_rbnode_find__core___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_flip___main___boxed(obj*);
uint8 l_rbcolor_decidable__eq(uint8, uint8);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj*, obj*);
obj* l_rbmap_has__repr___rarg(obj*, obj*, obj*);
obj* l_rbnode_flip__colors(obj*, obj*);
obj* l_rbnode_rotate__left___main(obj*, obj*);
obj* l_rbnode_depth___rarg(obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_rbnode_flip__colors___rarg(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj*, obj*, obj*);
obj* l_rbnode_flip__color___rarg(obj*);
obj* l_rbnode_fold___main___at_main___spec__2(obj*, obj*);
obj* l_rbmap_from__list___rarg(obj*, obj*, obj*);
obj* l_rbcolor_decidable__eq___boxed(obj*, obj*);
obj* l_rbnode_rotate__right(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_map;
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_rbmap_max___rarg(obj*);
obj* l_rbnode_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___rarg(obj*, obj*, obj*);
obj* l_rbnode_max(obj*, obj*);
obj* l_rbnode_min___main(obj*, obj*);
obj* l_rbmap_depth___rarg(obj*, obj*);
obj* l_rbnode_fold___main___rarg(obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_fixup(obj*, obj*);
obj* l_rbnode_is__red___main___rarg___boxed(obj*);
obj* l_rbnode_set__black___main(obj*, obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj*, obj*, obj*);
obj* l_list_head___main___at_main___spec__1(obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_io_println_x_27(obj*, obj*);
obj* l_rbnode_depth(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins(obj*, obj*, obj*);
obj* l_rbmap_depth(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_all___main(obj*, obj*);
obj* l_rbnode_fixup___rarg(obj*);
obj* l_rbmap_to__list___main(obj*, obj*, obj*);
obj* l_rbmap_of__list___rarg(obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(obj*, obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_rbmap_min___main(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_any(obj*, obj*);
obj* l_rbmap_all___main___rarg(obj*, obj*);
obj* l_rbmap_find___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_flip__colors___main(obj*, obj*);
obj* l_rbnode_ins___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert(obj*, obj*, obj*);
obj* l_rbnode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_min___rarg(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_rbmap_of__list___main___rarg(obj*, obj*);
obj* l_rbmap_lower__bound(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__5___rarg(obj*, obj*, obj*);
obj* l_rbnode_max___main(obj*, obj*);
obj* l_rbnode_max___main___rarg(obj*);
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_rbnode_rotate__left___rarg(obj*, obj*);
obj* l_rbmap_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj*, obj*, obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_rbmap_lower__bound___rarg(obj*, obj*, obj*);
obj* l_rbmap_of__list___main(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_mk__map__aux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_rbmap_all(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj*, obj*);
obj* l_rbmap_any___main___rarg(obj*, obj*);
obj* l_rbmap_empty(obj*, obj*, obj*);
obj* l_rbmap_to__list___rarg(obj*);
obj* l_rbmap_empty___rarg___boxed(obj*);
obj* l_rbnode_lower__bound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_find__core(obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main(obj*, obj*, obj*, obj*);
obj* l_rbmap_fold___main(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_min___rarg(obj*);
obj* l_rbmap_any___rarg(obj*, obj*);
obj* l_rbmap_find__core___main___rarg(obj*, obj*, obj*);
static inline bool is_excl(obj * o) { return lean::is_exclusive(o); }

uint8 l_rbcolor_decidable__eq(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
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
else
{
if (x_1 == 0)
{
uint8 x_4;
x_4 = 0;
return x_4;
}
else
{
uint8 x_5;
x_5 = 1;
return x_5;
}
}
}
}
obj* l_rbcolor_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5;
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_rbcolor_decidable__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_rbnode_depth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3;
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0u);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15;
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_10 = l_rbnode_depth___main___rarg(x_0, x_4);
lean::inc(x_0);
x_12 = l_rbnode_depth___main___rarg(x_0, x_6);
x_13 = lean::apply_2(x_0, x_10, x_12);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_13, x_14);
lean::dec(x_13);
return x_15;
}
}
}
obj* l_rbnode_depth___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_min___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1;
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6;
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_10;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_4);
lean::dec(x_6);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_rbnode_min___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___main___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_min___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_min___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_max___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1;
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6;
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_2);
lean::dec(x_4);
x_0 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___main___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_max___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_max___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16;
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_rbnode_fold___main___rarg(x_0, x_4, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_10;
x_2 = x_16;
goto _start;
}
}
}
obj* l_rbnode_fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16;
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_rbnode_rev__fold___main___rarg(x_0, x_10, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_4;
x_2 = x_16;
goto _start;
}
}
}
obj* l_rbnode_rev__fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_rev__fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4;
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; uint8 x_16;
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_7, x_9);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
lean::dec(x_5);
if (x_16 == 0)
{
lean::dec(x_0);
lean::dec(x_11);
return x_15;
}
else
{
x_1 = x_11;
goto _start;
}
}
else
{
obj* x_22; uint8 x_23;
lean::inc(x_0);
x_22 = l_rbnode_all___main___rarg(x_0, x_5);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
lean::dec(x_0);
lean::dec(x_11);
return x_22;
}
else
{
x_1 = x_11;
goto _start;
}
}
}
}
}
obj* l_rbnode_all___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_all___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4;
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; uint8 x_16;
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_7, x_9);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_18; uint8 x_19;
lean::inc(x_0);
x_18 = l_rbnode_any___main___rarg(x_0, x_5);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_11);
return x_18;
}
}
else
{
lean::dec(x_5);
if (x_16 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_11);
return x_15;
}
}
}
}
}
obj* l_rbnode_any___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_any___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___rarg), 2, 0);
return x_4;
}
}
uint8 l_rbnode_is__red___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1;
x_1 = 0;
return x_1;
}
else
{
uint8 x_2;
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_2 == 0)
{
uint8 x_4;
x_4 = 1;
return x_4;
}
else
{
uint8 x_5;
x_5 = 0;
return x_5;
}
}
}
}
obj* l_rbnode_is__red___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_is__red___main___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_rbnode_is__red___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2;
x_1 = l_rbnode_is__red___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_rbnode_is__red___rarg(obj* x_0) {
_start:
{
uint8 x_1;
x_1 = l_rbnode_is__red___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_is__red(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_is__red___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_rbnode_is__red___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2;
x_1 = l_rbnode_is__red___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
#if 0
static unsigned D = 0;
static unsigned A = 0;
static void incD() {
    D++;
}
static void incA() {
    A++;
}
static void showAD() {
    std::cout << "D: " << D << "A: " << A << "\n";
}
#else
#define incD()
#define incA()
#define showAD()
#define A 0
#define D 0
#endif


obj* l_rbnode_rotate__left___main___rarg(obj* x_0) {
_start:
{
uint8 x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10;
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
return x_0;
}
else
{
uint8 x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24;
x_15 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*4);
if (x_15 == 0)
{
uint8 x_26;
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_26 = l_rbnode_is__red___main___rarg(x_4);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31;
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);

if (is_excl(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_27 = x_0;
 incD();
} else {
    incA();
 lean::dec(x_0);
 x_27 = lean::box(0);
}


x_16 = lean::cnstr_get(x_10, 0);
x_18 = lean::cnstr_get(x_10, 1);
x_20 = lean::cnstr_get(x_10, 2);
x_22 = lean::cnstr_get(x_10, 3);


if (is_excl(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 lean::cnstr_set(x_10, 3, lean::box(0));
 x_24 = x_10;
 incD();
} else {
    incA();
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_10);
 x_24 = lean::box(0);
}

if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_6);
lean::cnstr_set(x_28, 2, x_8);
lean::cnstr_set(x_28, 3, x_16);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_15);
x_29 = x_28;
if (lean::is_scalar(x_24)) {
 x_30 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_30 = x_24;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_18);
lean::cnstr_set(x_30, 2, x_20);
lean::cnstr_set(x_30, 3, x_22);
lean::cnstr_set_scalar(x_30, sizeof(void*)*4, x_3);
x_31 = x_30;
return x_31;
}
else
{
lean::dec(x_4);
lean::dec(x_10);
return x_0;
}
}
else
{
lean::dec(x_10);
return x_0;
}
}
}
}


obj* l_rbnode_rotate__right___main___rarg(obj* x_0) {
_start:
{
uint8 x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10;
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
return x_0;
}
else
{
uint8 x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24;
x_15 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4);
if (x_15 == 0)
{
uint8 x_26;
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
x_26 = l_rbnode_is__red___main___rarg(x_16);
if (x_26 == 0)
{
lean::dec(x_4);
lean::dec(x_16);
return x_0;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39;
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
x_18 = lean::cnstr_get(x_4, 1);
x_20 = lean::cnstr_get(x_4, 2);
x_22 = lean::cnstr_get(x_4, 3);

if (is_excl(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_24 = x_0;
 incD();
} else {
    incA();
 lean::dec(x_0);
 x_24 = lean::box(0);
}

if (is_excl(x_4)) {
    lean::cnstr_release(x_4, 0);
    lean::cnstr_set(x_4, 0, x_22);
    lean::cnstr_set(x_4, 1, x_6);
    lean::cnstr_set(x_4, 2, x_8);
    lean::cnstr_set(x_4, 3, x_10);
    lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_15);
    x_36 = x_4;
    incD();
} else {
    incA();
    int * n = 0;
    *n = 0;
}

x_37 = x_36;

if (lean::is_scalar(x_24)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_24;
}
lean::cnstr_set(x_38, 0, x_16);
lean::cnstr_set(x_38, 1, x_18);
lean::cnstr_set(x_38, 2, x_20);
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_3);
x_39 = x_38;
return x_39;
}
}
else
{
lean::dec(x_4);
return x_0;
}
}
}
}

uint8 l_rbnode_flip___main(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1;
x_1 = 1;
return x_1;
}
else
{
uint8 x_2;
x_2 = 0;
return x_2;
}
}
}

obj* l_rbnode_flip__color___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
uint8 x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_11; obj* x_12; obj* x_13;
x_1 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (is_excl(x_0)) {
 x_11 = l_rbnode_flip___main(x_1);
 lean::cnstr_set_scalar(x_0, sizeof(void*)*4, x_11);
 incD();
 return x_0;
} else {
  lean_unreachable();
}
}
}
}

obj* l_rbnode_flip__colors___main___rarg(obj* x_0) {
_start:
{
uint8 x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_13;
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_13 = l_rbnode_is__red___main___rarg(x_4);
if (x_13 == 0)
{
lean::dec(x_4);
return x_0;
}
else
{
uint8 x_19;
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
x_19 = l_rbnode_is__red___main___rarg(x_10);
if (x_19 == 0)
{
lean::dec(x_10);
lean::dec(x_4);
return x_0;
}
else
{
obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29;
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
if (is_excl(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 incD();
 x_24 = x_0;
} else {
    incA();
 lean::dec(x_0);
 x_24 = lean::box(0);
}
x_25 = l_rbnode_flip___main(x_3);
x_26 = l_rbnode_flip__color___main___rarg(x_4);
x_27 = l_rbnode_flip__color___main___rarg(x_10);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_6);
lean::cnstr_set(x_28, 2, x_8);
lean::cnstr_set(x_28, 3, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_25);
x_29 = x_28;
return x_29;
}
}
}
}
obj* l_rbnode_fixup___rarg(obj* x_0) {
_start:
{
obj* x_3; obj* x_4; obj* x_5;
x_3 = l_rbnode_rotate__left___main___rarg(x_0);
x_4 = l_rbnode_rotate__right___main___rarg(x_3);
x_5 = l_rbnode_flip__colors___main___rarg(x_4);
return x_5;
}
}

obj* l_rbnode_set__black___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
uint8 x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8;
x_1 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_1 == 0)
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13;
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
if (is_excl(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 incD();
 x_10 = x_0;
} else {
    incA();
 lean::dec(x_0);
 x_10 = lean::box(0);
}
x_11 = 1;
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_6);
lean::cnstr_set(x_12, 3, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*4, x_11);
x_13 = x_12;
return x_13;
}
else
{
return x_0;
}
}
}
}
obj* l_rbnode_ins___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 incD();
 x_17 = x_3;
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 incD();
 x_17 = x_3;
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5;
x_4 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_2, x_3, x_1);
x_5 = l_rbnode_set__black___main___rarg(x_4);
return x_5;
}
}
obj* l_rbnode_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___rarg), 4, 0);
return x_6;
}
}
obj* _init_l_rbmap() {
_start:
{
obj* x_0;
x_0 = lean::box(0);
return x_0;
}
}
obj* l_mk__rbmap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
}
obj* l_rbmap_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_depth(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_depth___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___main___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___main___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___rarg), 3, 0);
return x_8;
}
}
uint8 l_rbmap_empty___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1;
x_1 = 1;
return x_1;
}
else
{
uint8 x_3;
lean::dec(x_0);
x_3 = 0;
return x_3;
}
}
}
obj* l_rbmap_empty___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___main___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_rbmap_empty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2;
x_1 = l_rbmap_empty___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_rbmap_empty___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1;
x_1 = 1;
return x_1;
}
else
{
uint8 x_3;
lean::dec(x_0);
x_3 = 0;
return x_3;
}
}
}
obj* l_rbmap_empty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_rbmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2;
x_1 = l_rbmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13;
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_8, x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_0 = x_2;
x_1 = x_13;
goto _start;
}
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_rbmap_to__list___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2;
x_1 = lean::box(0);
x_2 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_to__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbmap_to__list___main___rarg(x_0);
return x_1;
}
}
obj* l_rbmap_to__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_min___main___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2;
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12;
x_3 = lean::cnstr_get(x_1, 0);
if (is_excl(x_1)) {
 x_5 = x_1;
 incD();
} else {
    incA();
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_min___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_min___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2;
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12;
x_3 = lean::cnstr_get(x_1, 0);
if (is_excl(x_1)) {
 x_5 = x_1;
 incD();
} else {
    incA();
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_min(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_max___main___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2;
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12;
x_3 = lean::cnstr_get(x_1, 0);
if (is_excl(x_1)) {
 x_5 = x_1;
 incD();
} else {
    incA();
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_max___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_max___rarg(obj* x_0) {
_start:
{
obj* x_1;
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2;
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12;
x_3 = lean::cnstr_get(x_1, 0);
if (is_excl(x_1)) {
 x_5 = x_1;
 incD();
} else {
    incA();
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_max(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___rarg), 1, 0);
return x_6;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6;
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_string_join___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33;
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_0);
x_19 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_2, x_9);
x_20 = lean::apply_1(x_0, x_12);
x_21 = l_prod_has__repr___rarg___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_list_repr__aux___main___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::apply_1(x_1, x_14);
x_27 = lean::string_append(x_25, x_26);
lean::dec(x_26);
x_29 = l_option_has__repr___rarg___closed__3;
x_30 = lean::string_append(x_27, x_29);
x_31 = lean::string_append(x_24, x_30);
lean::dec(x_30);
x_33 = lean::string_append(x_31, x_19);
lean::dec(x_19);
return x_33;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37;
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_string_join___closed__1;
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_43; obj* x_45; uint8 x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63;
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
lean::dec(x_38);
x_48 = 0;
lean::inc(x_1);
lean::inc(x_0);
x_51 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_48, x_40);
x_52 = lean::apply_1(x_0, x_43);
x_53 = l_prod_has__repr___rarg___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_list_repr__aux___main___rarg___closed__1;
x_57 = lean::string_append(x_54, x_56);
x_58 = lean::apply_1(x_1, x_45);
x_59 = lean::string_append(x_57, x_58);
lean::dec(x_58);
x_61 = l_option_has__repr___rarg___closed__3;
x_62 = lean::string_append(x_59, x_61);
x_63 = lean::string_append(x_62, x_51);
lean::dec(x_51);
return x_63;
}
}
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5;
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_repr___main___rarg___closed__1;
return x_5;
}
else
{
uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12;
x_6 = 1;
x_7 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_6, x_2);
x_8 = l_list_repr___main___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_list_repr___main___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___main___at_rbmap_has__repr___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_rbmap_has__repr___rarg___closed__1() {
_start:
{
obj* x_0;
x_0 = lean::mk_string("rbmap_of ");
return x_0;
}
}
obj* l_rbmap_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6;
x_3 = l_rbmap_to__list___main___rarg(x_2);
x_4 = l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(x_0, x_1, x_3);
x_5 = l_rbmap_has__repr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_rbmap_has__repr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_has__repr___rarg), 3, 0);
return x_6;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5;
x_4 = lean::unbox(x_2);
x_5 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 x_17 = x_3;
 incD();
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5;
x_4 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_2, x_3, x_1);
x_5 = l_rbnode_set__black___main___rarg(x_4);
return x_5;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4;
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4;
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 x_17 = x_3;
 incD();
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5;
x_4 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_2, x_3, x_1);
x_5 = l_rbnode_set__black___main___rarg(x_4);
return x_5;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4;
x_4 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_of__list___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3;
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; obj* x_16;
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbmap_of__list___main___rarg(x_0, x_6);
x_16 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_15, x_9, x_11);
return x_16;
}
}
}
obj* l_rbmap_of__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbmap_of__list___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_of__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___rarg), 2, 0);
return x_6;
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5;
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19;
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25;
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30;
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find__core___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find__core___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7;
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_20; uint8 x_21;
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_2(x_0, x_3, x_10);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_25; uint8 x_26;
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_10, x_3);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30;
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_14);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_12);
return x_30;
}
else
{
lean::dec(x_12);
x_1 = x_0;
x_2 = x_14;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_14);
x_1 = x_0;
x_2 = x_8;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19;
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26;
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31;
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33;
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_lower__bound___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4;
x_3 = lean::box(0);
x_4 = l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_lower__bound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_lower__bound___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbmap_lower__bound___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_lower__bound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7;
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_20; uint8 x_21;
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_2(x_0, x_3, x_10);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_25; uint8 x_26;
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_10, x_3);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30;
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_14);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_12);
return x_30;
}
else
{
lean::dec(x_12);
x_1 = x_0;
x_2 = x_14;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_14);
x_1 = x_0;
x_2 = x_8;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_contains___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_rbmap_contains___spec__1___rarg), 3, 0);
return x_6;
}
}
uint8 l_rbmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4;
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
return x_4;
}
}
obj* l_rbmap_contains(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_contains___rarg___boxed), 3, 0);
return x_6;
}
}
obj* l_rbmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4;
x_3 = l_rbmap_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 x_17 = x_3;
 incD();
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5;
x_4 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_2, x_3, x_1);
x_5 = l_rbnode_set__black___main___rarg(x_4);
return x_5;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_from__list___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4;
x_4 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15;
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap_from__list___spec__4___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_from__list___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5;
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbmap_from__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___rarg), 2, 0);
return x_8;
}
}
obj* l_rbmap_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8;
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___rarg), 2, 0);
return x_8;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; obj* x_6; obj* x_7;
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22;
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
if (is_excl(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 lean::cnstr_set(x_3, 3, lean::box(0));
 x_17 = x_3;
 incD();
} else {
    incA();
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_1, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27;
lean::inc(x_1);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_1);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32;
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_2);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36;
x_33 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_1, x_2, x_15);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
x_36 = l_rbnode_fixup___rarg(x_35);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40;
x_37 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
lean::cnstr_set(x_38, 2, x_13);
lean::cnstr_set(x_38, 3, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_8);
x_39 = x_38;
x_40 = l_rbnode_fixup___rarg(x_39);
return x_40;
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap__of___spec__4___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5;
x_4 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_2, x_3, x_1);
x_5 = l_rbnode_set__black___main___rarg(x_4);
return x_5;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap__of___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4;
x_4 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap__of___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15;
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6;
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap__of___spec__5___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5;
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbmap__of___spec__5___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_rbmap__of___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4;
lean::dec(x_1);
x_4 = l_rbmap_from__list___at_rbmap__of___spec__1___rarg(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* l_rbmap__of(obj* x_0, obj* x_1) {
_start:
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap__of___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_map() {
_start:
{
obj* x_0;
x_0 = lean::box(0);
return x_0;
}
}
obj* l_rbnode_ins___main___at_mk__map__aux___main___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6;
x_3 = 0;
x_4 = lean::box(x_1);
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_2);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_3);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17;
x_7 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
x_8 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
x_12 = lean::cnstr_get(x_2, 2);
x_14 = lean::cnstr_get(x_2, 3);
if (is_excl(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_16 = x_2;
 incD();
} else {
    incA();
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_lt(x_0, x_10);
if (x_17 == 0)
{
uint8 x_18;
x_18 = lean::nat_dec_lt(x_10, x_0);
if (x_18 == 0)
{
obj* x_21; obj* x_22; obj* x_23;
lean::dec(x_10);
lean::dec(x_12);
x_21 = lean::box(x_1);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_16;
}
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_0);
lean::cnstr_set(x_22, 2, x_21);
lean::cnstr_set(x_22, 3, x_14);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_7);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27;
x_24 = l_rbnode_ins___main___at_mk__map__aux___main___spec__3(x_0, x_1, x_14);
if (lean::is_scalar(x_16)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_16;
}
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_10);
lean::cnstr_set(x_25, 2, x_12);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_7);
x_26 = x_25;
x_27 = l_rbnode_fixup___rarg(x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31;
x_28 = l_rbnode_ins___main___at_mk__map__aux___main___spec__3(x_0, x_1, x_8);
if (lean::is_scalar(x_16)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_16;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_10);
lean::cnstr_set(x_29, 2, x_12);
lean::cnstr_set(x_29, 3, x_14);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_7);
x_30 = x_29;
x_31 = l_rbnode_fixup___rarg(x_30);
return x_31;
}
}
}
}
obj* l_rbnode_insert___at_mk__map__aux___main___spec__2(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_4;
x_3 = l_rbnode_ins___main___at_mk__map__aux___main___spec__3(x_1, x_2, x_0);
x_4 = l_rbnode_set__black___main___rarg(x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_mk__map__aux___main___spec__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3;
x_3 = l_rbnode_insert___at_mk__map__aux___main___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_mk__map__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3;
x_3 = lean::unbox(x_0) == 0;
if (x_3 == 0)
{
obj* x_5; uint8 x_9;
unsigned x = lean::unbox(x_0) - 1;
x_5 = lean::box(x);
x_9 = (x % 10) == 0;
if (x_9 == 0)
{
uint8 x_11; obj* x_13;
x_11 = 0;
x_13 = l_rbnode_insert___at_mk__map__aux___main___spec__2(x_1, x_5, x_11);
x_0 = x_5;
x_1 = x_13;
goto _start;
}
else
{
uint8 x_15; obj* x_17;
x_15 = 1;
x_17 = l_rbnode_insert___at_mk__map__aux___main___spec__2(x_1, x_5, x_15);
x_0 = x_5;
x_1 = x_17;
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
obj* l_rbnode_ins___main___at_mk__map__aux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4;
x_3 = lean::unbox(x_1);
x_4 = l_rbnode_ins___main___at_mk__map__aux___main___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l_rbnode_insert___at_mk__map__aux___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4;
x_3 = lean::unbox(x_2);
x_4 = l_rbnode_insert___at_mk__map__aux___main___spec__2(x_0, x_1, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_mk__map__aux___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4;
x_3 = lean::unbox(x_2);
x_4 = l_rbmap_insert___main___at_mk__map__aux___main___spec__1(x_0, x_1, x_3);
return x_4;
}
}
obj* l_mk__map__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2;
x_2 = l_mk__map__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_mk__map(obj* x_0) {
_start:
{
obj* x_1; obj* x_2;
x_1 = lean::box(0);
x_2 = l_mk__map__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_list_head___main___at_main___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1;
x_1 = l_string_join___closed__1;
return x_1;
}
else
{
obj* x_2;
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_rbnode_fold___main___at_main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; uint8 x_12;
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_rbnode_fold___main___at_main___spec__2(x_2, x_1);
x_12 = lean::unbox(x_6);
if (x_12 == 0)
{
lean::dec(x_4);
x_0 = x_8;
x_1 = x_11;
goto _start;
}
else
{
obj* x_15;
x_15 = lean::nat_add(x_11, x_4);
lean::dec(x_4);
lean::dec(x_11);
x_0 = x_8;
x_1 = x_15;
goto _start;
}
}
}
}
obj* _lean_main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; uint32 x_12; obj* x_13; obj* x_14;
x_2 = l_list_head___main___at_main___spec__1(x_0);
x_3 = l_string_to__nat(x_2);
x_4 = l_mk__map(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_rbnode_fold___main___at_main___spec__2(x_4, x_5);
x_7 = l_nat_repr(x_6);
x_8 = l_io_println_x_27(x_7, x_1);
x_9 = lean::cnstr_get(x_8, 1);
if (is_excl(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_11 = x_8;
 incD();
} else {
    incA();
 lean::inc(x_9);
 lean::dec(x_8);
 x_11 = lean::box(0);
}
x_12 = 0;
x_13 = lean::box_uint32(x_12);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_9);
showAD();
return x_14;
}
}
void initialize_init_core();
void initialize_init_io();
void initialize_init_data_ordering_default();
static bool _G_initialized = false;
void initialize_rbmap3() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 initialize_init_io();
 initialize_init_data_ordering_default();
 l_rbmap = _init_l_rbmap();
lean::mark_persistent(l_rbmap);
 l_rbmap_has__repr___rarg___closed__1 = _init_l_rbmap_has__repr___rarg___closed__1();
lean::mark_persistent(l_rbmap_has__repr___rarg___closed__1);
 l_map = _init_l_map();
lean::mark_persistent(l_map);
}
int main(int argc, char ** argv) {
lean::initialize_runtime_module();
initialize_rbmap3();
lean::scoped_task_manager tmanager(lean::hardware_concurrency());
obj* in = lean::box(0);
int i = argc;
while (i > 1) {
 i--;
 obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);
 in = n;
}
obj * r = _lean_main(in, lean::box(0));
int ret = lean::unbox(lean::cnstr_get(r, 0));
lean::dec(r);
return ret;
}
