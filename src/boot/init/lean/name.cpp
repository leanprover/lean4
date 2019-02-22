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
obj* l_lean_name_has__append;
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
obj* l_lean_inhabited;
obj* l_lean_name_to__string___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
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
obj* l_lean_name_dec__eq___boxed(obj*, obj*);
obj* l___private_init_lean_name_1__hash__aux(obj*, usize);
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
obj* l_lean_name_update__prefix___main(obj*, obj*);
obj* l_lean_name_get__prefix(obj*);
obj* l___private_init_lean_name_1__hash__aux___main(obj*, usize);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_name_get__prefix___main(obj*);
obj* l_lean_name_hash___boxed(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___closed__1;
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
obj* x_3; usize x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = 0;
x_0 = x_3;
x_1 = x_6;
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
lean::dec(x_0);
return x_1;
}
}
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
return x_0;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_name_append___main(x_0, x_2);
x_8 = lean_name_mk_string(x_7, x_4);
return x_8;
}
default:
{
obj* x_9; obj* x_11; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_lean_name_append___main(x_0, x_9);
x_15 = lean_name_mk_numeral(x_14, x_11);
return x_15;
}
}
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
obj* _init_l_lean_name_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_append), 2, 0);
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
lean::dec(x_1);
if (x_3 == 0)
{
lean::dec(x_2);
return x_0;
}
else
{
return x_2;
}
}
case 1:
{
obj* x_6; obj* x_8; uint8 x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_10 == 0)
{
obj* x_12; obj* x_13; 
x_12 = l_lean_name_replace__prefix___main(x_6, x_1, x_2);
x_13 = lean_name_mk_string(x_12, x_8);
return x_13;
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_8);
return x_2;
}
}
default:
{
obj* x_17; obj* x_19; uint8 x_21; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_21 == 0)
{
obj* x_23; obj* x_24; 
x_23 = l_lean_name_replace__prefix___main(x_17, x_1, x_2);
x_24 = lean_name_mk_numeral(x_23, x_19);
return x_24;
}
else
{
lean::dec(x_1);
lean::dec(x_17);
lean::dec(x_19);
return x_2;
}
}
}
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
obj* l_lean_name_quick__lt___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
x_2 = lean_name_dec_eq(x_1, x_0);
lean::dec(x_1);
if (x_2 == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
else
{
uint8 x_6; obj* x_7; 
x_6 = 0;
x_7 = lean::box(x_6);
return x_7;
}
}
case 1:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_9; obj* x_10; 
lean::dec(x_0);
x_9 = 0;
x_10 = lean::box(x_9);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_16; obj* x_18; uint8 x_21; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::string_dec_lt(x_13, x_18);
if (x_21 == 0)
{
uint8 x_22; 
x_22 = lean::string_dec_eq(x_13, x_18);
lean::dec(x_18);
lean::dec(x_13);
if (x_22 == 0)
{
uint8 x_27; obj* x_28; 
lean::dec(x_16);
lean::dec(x_11);
x_27 = 0;
x_28 = lean::box(x_27);
return x_28;
}
else
{
x_0 = x_11;
x_1 = x_16;
goto _start;
}
}
else
{
uint8 x_34; obj* x_35; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_13);
x_34 = 1;
x_35 = lean::box(x_34);
return x_35;
}
}
default:
{
uint8 x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_0);
x_38 = 0;
x_39 = lean::box(x_38);
return x_39;
}
}
}
default:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_41; obj* x_42; 
lean::dec(x_0);
x_41 = 0;
x_42 = lean::box(x_41);
return x_42;
}
case 1:
{
uint8 x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_0);
x_45 = 1;
x_46 = lean::box(x_45);
return x_46;
}
default:
{
obj* x_47; obj* x_49; obj* x_52; obj* x_54; uint8 x_57; 
x_47 = lean::cnstr_get(x_0, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 1);
lean::inc(x_49);
lean::dec(x_0);
x_52 = lean::cnstr_get(x_1, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_1, 1);
lean::inc(x_54);
lean::dec(x_1);
x_57 = lean::nat_dec_lt(x_49, x_54);
if (x_57 == 0)
{
uint8 x_58; 
x_58 = lean::nat_dec_eq(x_49, x_54);
lean::dec(x_54);
lean::dec(x_49);
if (x_58 == 0)
{
uint8 x_63; obj* x_64; 
lean::dec(x_47);
lean::dec(x_52);
x_63 = 0;
x_64 = lean::box(x_63);
return x_64;
}
else
{
x_0 = x_47;
x_1 = x_52;
goto _start;
}
}
else
{
uint8 x_70; obj* x_71; 
lean::dec(x_47);
lean::dec(x_49);
lean::dec(x_52);
lean::dec(x_54);
x_70 = 1;
x_71 = lean::box(x_70);
return x_71;
}
}
}
}
}
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
obj* x_3; 
lean::dec(x_0);
x_3 = l_lean_name_to__string__with__sep___main___closed__1;
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_9; uint8 x_10; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::box(0);
x_10 = lean_name_dec_eq(x_4, x_9);
if (x_10 == 0)
{
obj* x_12; obj* x_13; obj* x_15; 
lean::inc(x_0);
x_12 = l_lean_name_to__string__with__sep___main(x_0, x_4);
x_13 = lean::string_append(x_12, x_0);
lean::dec(x_0);
x_15 = lean::string_append(x_13, x_6);
lean::dec(x_6);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_6;
}
}
default:
{
obj* x_19; obj* x_21; obj* x_24; uint8 x_25; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::box(0);
x_25 = lean_name_dec_eq(x_19, x_24);
if (x_25 == 0)
{
obj* x_27; obj* x_28; obj* x_30; obj* x_31; 
lean::inc(x_0);
x_27 = l_lean_name_to__string__with__sep___main(x_0, x_19);
x_28 = lean::string_append(x_27, x_0);
lean::dec(x_0);
x_30 = l_nat_repr(x_21);
x_31 = lean::string_append(x_28, x_30);
lean::dec(x_30);
return x_31;
}
else
{
obj* x_35; 
lean::dec(x_0);
lean::dec(x_19);
x_35 = l_nat_repr(x_21);
return x_35;
}
}
}
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
