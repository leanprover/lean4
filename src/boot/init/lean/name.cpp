// Lean compiler output
// Module: init.lean.name
// Imports: init.data.string.basic init.coe init.data.uint init.data.to_string init.lean.format init.data.hashable
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
obj* l_lean_name_quick__lt___main___boxed(obj*, obj*);
obj* l_lean_name_has__append;
obj* l_lean_name_replace__prefix___boxed(obj*, obj*, obj*);
obj* l_lean_name_decidable__eq;
obj* l_lean_mk__str__name(obj*, obj*);
obj* l___private_init_lean_name_1__hash__aux___main___boxed(obj*, obj*);
obj* l_lean_name_components_x_27(obj*);
obj* l_lean_name_to__string(obj*);
obj* l_list_reverse___rarg(obj*);
extern "C" usize lean_name_hash_usize(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_name_has__lt__quick;
obj* l_lean_name_replace__prefix(obj*, obj*, obj*);
obj* l_lean_name_get__prefix___main___boxed(obj*);
obj* l_lean_inhabited;
obj* l_lean_name_to__string___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_name_append___boxed(obj*, obj*);
uint8 l_lean_name_decidable__rel(obj*, obj*);
obj* l_lean_name_append(obj*, obj*);
obj* l_lean_name_hashable;
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_name_components(obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_name_update__prefix(obj*, obj*);
obj* l_lean_name_components_x_27___main(obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___boxed(obj*, obj*);
obj* l_lean_name_dec__eq___boxed(obj*, obj*);
obj* l___private_init_lean_name_1__hash__aux(obj*, usize);
obj* l_lean_name_quick__lt___boxed(obj*, obj*);
obj* l_lean_name_replace__prefix___main___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_mk__num__name(obj*, obj*);
obj* l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_mk__simple__name(obj*);
obj* l_lean_name_lean_has__to__format(obj*);
namespace lean {
usize usize_of_nat(obj*);
}
obj* l___private_init_lean_name_1__hash__aux___boxed(obj*, obj*);
obj* l_lean_name_to__string__with__sep___boxed(obj*, obj*);
obj* l_lean_name_update__prefix___main(obj*, obj*);
obj* l_lean_name_get__prefix(obj*);
obj* l___private_init_lean_name_1__hash__aux___main(obj*, usize);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_name_get__prefix___main(obj*);
obj* l_lean_name_hash___boxed(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_name_append___main___boxed(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___closed__1;
obj* l_lean_name_get__prefix___boxed(obj*);
obj* l_lean_name_has__to__string;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_name_decidable__rel___boxed(obj*, obj*);
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
obj* l___private_init_lean_name_1__hash__aux___main(obj* x_0, usize x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::box_size_t(x_1);
return x_2;
}
default:
{
obj* x_3; usize x_4; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = 0;
x_0 = x_3;
x_1 = x_4;
goto _start;
}
}
}
}
obj* l___private_init_lean_name_1__hash__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_lean_name_1__hash__aux___main(x_0, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name_1__hash__aux(obj* x_0, usize x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name_1__hash__aux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_name_1__hash__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_lean_name_1__hash__aux(x_0, x_2);
lean::dec(x_0);
return x_3;
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
obj* l_lean_name_quick__lt___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
x_2 = lean_name_dec_eq(x_1, x_0);
if (x_2 == 0)
{
uint8 x_3; obj* x_4; 
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
else
{
uint8 x_5; obj* x_6; 
x_5 = 0;
x_6 = lean::box(x_5);
return x_6;
}
}
case 1:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_0, 1);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::string_dec_lt(x_8, x_10);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = lean::string_dec_eq(x_8, x_10);
if (x_12 == 0)
{
uint8 x_13; obj* x_14; 
x_13 = 0;
x_14 = lean::box(x_13);
return x_14;
}
else
{
x_0 = x_7;
x_1 = x_9;
goto _start;
}
}
else
{
uint8 x_16; obj* x_17; 
x_16 = 1;
x_17 = lean::box(x_16);
return x_17;
}
}
default:
{
uint8 x_18; obj* x_19; 
x_18 = 0;
x_19 = lean::box(x_18);
return x_19;
}
}
}
default:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_20; obj* x_21; 
x_20 = 0;
x_21 = lean::box(x_20);
return x_21;
}
case 1:
{
uint8 x_22; obj* x_23; 
x_22 = 1;
x_23 = lean::box(x_22);
return x_23;
}
default:
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; 
x_24 = lean::cnstr_get(x_0, 0);
x_25 = lean::cnstr_get(x_0, 1);
x_26 = lean::cnstr_get(x_1, 0);
x_27 = lean::cnstr_get(x_1, 1);
x_28 = lean::nat_dec_lt(x_25, x_27);
if (x_28 == 0)
{
uint8 x_29; 
x_29 = lean::nat_dec_eq(x_25, x_27);
if (x_29 == 0)
{
uint8 x_30; obj* x_31; 
x_30 = 0;
x_31 = lean::box(x_30);
return x_31;
}
else
{
x_0 = x_24;
x_1 = x_26;
goto _start;
}
}
else
{
uint8 x_33; obj* x_34; 
x_33 = 1;
x_34 = lean::box(x_33);
return x_34;
}
}
}
}
}
}
}
obj* l_lean_name_quick__lt___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_quick__lt___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_name_quick__lt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_quick__lt___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_quick__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_quick__lt(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_2; uint8 x_3; 
x_2 = l_lean_name_quick__lt___main(x_0, x_1);
x_3 = lean::unbox(x_2);
if (x_3 == 0)
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
void initialize_init_data_string_basic();
void initialize_init_coe();
void initialize_init_data_uint();
void initialize_init_data_to__string();
void initialize_init_lean_format();
void initialize_init_data_hashable();
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
}
