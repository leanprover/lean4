// Lean compiler output
// Module: init.lean.name
// Imports: init.data.string.basic init.coe init.data.uint init.data.to_string init.lean.format init.data.hashable init.data.rbmap.default
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
obj* l_lean_string__to__name;
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2(obj*);
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1(obj*);
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___boxed(obj*);
obj* l_lean_name_has__append;
uint8 l_lean_name_quick__lt__core(obj*, obj*);
obj* l_lean_name_replace__prefix___boxed(obj*, obj*, obj*);
obj* l_lean_name_decidable__eq;
obj* l_lean_mk__str__name(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3___boxed(obj*);
obj* l___private_init_lean_name_1__hash__aux___main___boxed(obj*, obj*);
obj* l_lean_name_components_x_27(obj*);
obj* l_lean_name__map_find___rarg___boxed(obj*, obj*);
obj* l_lean_name_quick__lt__core___main___boxed(obj*, obj*);
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___boxed(obj*);
obj* l_lean_name__map_insert(obj*);
obj* l_lean_name_to__string(obj*);
obj* l_list_reverse___rarg(obj*);
extern "C" usize lean_name_hash_usize(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_name_has__lt__quick;
obj* l_lean_name_replace__prefix(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1___rarg(obj*, obj*, obj*);
obj* l_lean_name_get__prefix___main___boxed(obj*);
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1(obj*);
obj* l_lean_inhabited;
obj* l_lean_name_quick__lt__core___boxed(obj*, obj*);
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg(obj*, obj*);
obj* l_lean_name_to__string___closed__1;
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_name__map_insert___rarg(obj*, obj*, obj*);
obj* l_lean_name__map_contains___boxed(obj*);
obj* l_lean_name_append___boxed(obj*, obj*);
uint8 l_lean_name_decidable__rel(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_name__map_contains___rarg___boxed(obj*, obj*);
obj* l_lean_name_append(obj*, obj*);
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_name_hashable;
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_name_components(obj*);
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg(obj*, obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4(obj*);
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2___boxed(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_name_update__prefix(obj*, obj*);
obj* l_lean_name_components_x_27___main(obj*);
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg___boxed(obj*, obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___boxed(obj*, obj*);
obj* l_lean_name_dec__eq___boxed(obj*, obj*);
usize l___private_init_lean_name_1__hash__aux(obj*, usize);
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1___boxed(obj*);
obj* l_lean_name__map_insert___boxed(obj*);
obj* l_lean_name_quick__lt___boxed(obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1(obj*);
obj* l_lean_name__map_contains(obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2(obj*);
uint8 l_lean_name__map_contains___rarg(obj*, obj*);
obj* l_lean_name__map_find___rarg(obj*, obj*);
obj* l_lean_mk__name__map(obj*);
obj* l_lean_name_replace__prefix___main___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_mk__num__name(obj*, obj*);
uint8 l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_mk__simple__name(obj*);
obj* l_lean_name_lean_has__to__format(obj*);
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l___private_init_lean_name_1__hash__aux___boxed(obj*, obj*);
obj* l_lean_name_to__string__with__sep___boxed(obj*, obj*);
obj* l_lean_name__map_find(obj*);
obj* l_lean_name_update__prefix___main(obj*, obj*);
obj* l_lean_name_get__prefix(obj*);
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(obj*, obj*, obj*);
usize l___private_init_lean_name_1__hash__aux___main(obj*, usize);
obj* l_lean_name__map;
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg___boxed(obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_name_get__prefix___main(obj*);
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4___boxed(obj*);
obj* l_lean_name_hash___boxed(obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___boxed(obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_append___main___boxed(obj*, obj*);
uint8 l_lean_name_quick__lt__core___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___closed__1;
obj* l_lean_mk__name__map___boxed(obj*);
obj* l_lean_name_get__prefix___boxed(obj*);
obj* l_lean_name_has__to__string;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_lean_name_decidable__rel___boxed(obj*, obj*);
obj* l_lean_name__map_find___boxed(obj*);
obj* _init_l_lean_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_mk__str__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_mk__num__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_lean_mk__simple__name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean_name_mk_string(x_1, x_0);
return x_2;
}
}
obj* _init_l_lean_string__to__name() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_mk__simple__name), 1, 0);
return x_0;
}
}
usize l___private_init_lean_name_1__hash__aux___main(obj* x_0, usize x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
return x_1;
}
default:
{
obj* x_2; usize x_3; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = 0;
x_0 = x_2;
x_1 = x_3;
goto _start;
}
}
}
}
obj* l___private_init_lean_name_1__hash__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_lean_name_1__hash__aux___main(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
usize l___private_init_lean_name_1__hash__aux(obj* x_0, usize x_1) {
_start:
{
usize x_2; 
x_2 = l___private_init_lean_name_1__hash__aux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_name_1__hash__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_lean_name_1__hash__aux(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_name_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean_name_hash_usize(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_lean_name_hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_hash___boxed), 1, 0);
return x_0;
}
}
obj* l_lean_name_get__prefix___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
return x_0;
}
default:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
}
}
obj* l_lean_name_get__prefix___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name_get__prefix___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_name_get__prefix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name_get__prefix___main(x_0);
return x_1;
}
}
obj* l_lean_name_get__prefix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name_get__prefix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_name_update__prefix___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_1);
return x_0;
}
case 1:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean_name_mk_string(x_1, x_3);
return x_6;
}
default:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean_name_mk_numeral(x_1, x_7);
return x_10;
}
}
}
}
obj* l_lean_name_update__prefix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_update__prefix___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_components_x_27___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean_name_mk_string(x_7, x_4);
x_9 = l_lean_name_components_x_27___main(x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
default:
{
obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::box(0);
x_17 = lean_name_mk_numeral(x_16, x_13);
x_18 = l_lean_name_components_x_27___main(x_11);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
}
obj* l_lean_name_components_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name_components_x_27___main(x_0);
return x_1;
}
}
obj* l_lean_name_components(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_name_components_x_27___main(x_0);
x_2 = l_list_reverse___rarg(x_1);
return x_2;
}
}
obj* l_lean_name_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_name_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_lean_name_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_name_append___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::inc(x_0);
return x_0;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_lean_name_append___main(x_0, x_3);
x_9 = lean_name_mk_string(x_8, x_5);
return x_9;
}
default:
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = l_lean_name_append___main(x_0, x_10);
x_16 = lean_name_mk_numeral(x_15, x_12);
return x_16;
}
}
}
}
obj* l_lean_name_append___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_append___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_name_append(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_append___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_append___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_append(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_lean_name_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_append___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_name_replace__prefix___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_3; 
x_3 = lean_name_dec_eq(x_1, x_0);
if (x_3 == 0)
{
return x_0;
}
else
{
lean::inc(x_2);
return x_2;
}
}
case 1:
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
x_11 = l_lean_name_replace__prefix___main(x_5, x_1, x_2);
x_12 = lean_name_mk_string(x_11, x_7);
return x_12;
}
else
{
lean::dec(x_5);
lean::dec(x_7);
lean::inc(x_2);
return x_2;
}
}
default:
{
obj* x_16; obj* x_18; uint8 x_20; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_20 == 0)
{
obj* x_22; obj* x_23; 
x_22 = l_lean_name_replace__prefix___main(x_16, x_1, x_2);
x_23 = lean_name_mk_numeral(x_22, x_18);
return x_23;
}
else
{
lean::dec(x_16);
lean::dec(x_18);
lean::inc(x_2);
return x_2;
}
}
}
}
}
obj* l_lean_name_replace__prefix___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_name_replace__prefix___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_name_replace__prefix(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_name_replace__prefix___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_name_replace__prefix___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_name_replace__prefix(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_lean_name_quick__lt__core___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
x_2 = lean_name_dec_eq(x_1, x_0);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::string_dec_lt(x_6, x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = lean::string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
x_0 = x_5;
x_1 = x_7;
goto _start;
}
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
default:
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
}
}
default:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
case 1:
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
default:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_17 = lean::cnstr_get(x_0, 0);
x_18 = lean::cnstr_get(x_0, 1);
x_19 = lean::cnstr_get(x_1, 0);
x_20 = lean::cnstr_get(x_1, 1);
x_21 = lean::nat_dec_lt(x_18, x_20);
if (x_21 == 0)
{
uint8 x_22; 
x_22 = lean::nat_dec_eq(x_18, x_20);
if (x_22 == 0)
{
uint8 x_23; 
x_23 = 0;
return x_23;
}
else
{
x_0 = x_17;
x_1 = x_19;
goto _start;
}
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
}
}
}
}
}
obj* l_lean_name_quick__lt__core___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_name_quick__lt__core___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_lean_name_quick__lt__core(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_name_quick__lt__core___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_quick__lt__core___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_name_quick__lt__core(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_lean_name_quick__lt(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; 
x_2 = lean_name_hash_usize(x_0);
x_3 = lean_name_hash_usize(x_1);
x_4 = x_2 < x_3;
if (x_4 == 0)
{
uint8 x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_lean_name_quick__lt__core___main(x_0, x_1);
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
obj* l_lean_name_quick__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_name_quick__lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_lean_name_has__lt__quick() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_lean_name_decidable__rel(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_name_quick__lt(x_0, x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_lean_name_decidable__rel___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_name_decidable__rel(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_lean_name_to__string__with__sep___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[anonymous]");
return x_0;
}
}
obj* l_lean_name_to__string__with__sep___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_lean_name_to__string__with__sep___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; uint8 x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean_name_dec_eq(x_3, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = l_lean_name_to__string__with__sep___main(x_0, x_3);
x_11 = lean::string_append(x_10, x_0);
x_12 = lean::string_append(x_11, x_5);
lean::dec(x_5);
return x_12;
}
else
{
lean::dec(x_3);
return x_5;
}
}
default:
{
obj* x_15; obj* x_17; obj* x_20; uint8 x_21; 
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::box(0);
x_21 = lean_name_dec_eq(x_15, x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_lean_name_to__string__with__sep___main(x_0, x_15);
x_23 = lean::string_append(x_22, x_0);
x_24 = l_nat_repr(x_17);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
return x_25;
}
else
{
obj* x_28; 
lean::dec(x_15);
x_28 = l_nat_repr(x_17);
return x_28;
}
}
}
}
}
obj* l_lean_name_to__string__with__sep___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_to__string__with__sep___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_name_to__string__with__sep(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_to__string__with__sep___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_to__string__with__sep___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_to__string__with__sep(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_lean_name_to__string___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".");
return x_0;
}
}
obj* l_lean_name_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_name_to__string___closed__1;
x_2 = l_lean_name_to__string__with__sep___main(x_1, x_0);
return x_2;
}
}
obj* _init_l_lean_name_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_to__string), 1, 0);
return x_0;
}
}
obj* l_lean_name_lean_has__to__format(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_name_to__string___closed__1;
x_2 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_lean_name__map() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_mk__name__map(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_lean_mk__name__map___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_mk__name__map(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_name__map_insert___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_name__map_insert___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_name__map_insert___spec__1___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_name__map_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_name__map_insert___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_name__map_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name__map_insert___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_name__map_insert___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_name__map_insert___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_name__map_insert___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_name__map_insert___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at_lean_name__map_insert___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_name__map_insert___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_insert___main___at_lean_name__map_insert___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_name__map_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name__map_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_lean_name_quick__lt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
uint8 l_lean_name__map_contains___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
x_3 = l_option_is__some___main___rarg(x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_name__map_contains(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name__map_contains___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_name__map_contains___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_name__map_contains___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_name__map_contains___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_name__map_contains___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_name__map_contains___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_name__map_contains___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_name__map_contains___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name__map_contains(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_lean_name__map_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_name__map_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name__map_find___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_name__map_find___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_name__map_find___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_name__map_find___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_name__map_find___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name__map_find___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_name__map_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_name__map_find(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_data_string_basic();
void initialize_init_coe();
void initialize_init_data_uint();
void initialize_init_data_to__string();
void initialize_init_lean_format();
void initialize_init_data_hashable();
void initialize_init_data_rbmap_default();
static bool _G_initialized = false;
void initialize_init_lean_name() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_string_basic();
 initialize_init_coe();
 initialize_init_data_uint();
 initialize_init_data_to__string();
 initialize_init_lean_format();
 initialize_init_data_hashable();
 initialize_init_data_rbmap_default();
 l_lean_inhabited = _init_l_lean_inhabited();
lean::mark_persistent(l_lean_inhabited);
 l_lean_string__to__name = _init_l_lean_string__to__name();
lean::mark_persistent(l_lean_string__to__name);
 l_lean_name_hashable = _init_l_lean_name_hashable();
lean::mark_persistent(l_lean_name_hashable);
 l_lean_name_decidable__eq = _init_l_lean_name_decidable__eq();
lean::mark_persistent(l_lean_name_decidable__eq);
 l_lean_name_has__append = _init_l_lean_name_has__append();
lean::mark_persistent(l_lean_name_has__append);
 l_lean_name_has__lt__quick = _init_l_lean_name_has__lt__quick();
lean::mark_persistent(l_lean_name_has__lt__quick);
 l_lean_name_to__string__with__sep___main___closed__1 = _init_l_lean_name_to__string__with__sep___main___closed__1();
lean::mark_persistent(l_lean_name_to__string__with__sep___main___closed__1);
 l_lean_name_to__string___closed__1 = _init_l_lean_name_to__string___closed__1();
lean::mark_persistent(l_lean_name_to__string___closed__1);
 l_lean_name_has__to__string = _init_l_lean_name_has__to__string();
lean::mark_persistent(l_lean_name_has__to__string);
 l_lean_name__map = _init_l_lean_name__map();
}
