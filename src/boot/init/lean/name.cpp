// Lean compiler output
// Module: init.lean.name
// Imports: init.data.string.basic init.coe init.data.uint init.data.to_string init.lean.format init.data.hashable
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s4_lean_s16_mk__simple__name(obj*);
size_t _l_s4_lean_s4_name_s4_hash_s11___closed__1;
obj* _l_s4_lean_s4_name_s9_quick__lt(obj*, obj*);
obj* _l_s4_lean_s4_name_s14_decidable__rel(obj*, obj*);
obj* _l_s4_lean_s4_name_s10_to__string(obj*);
obj* _l_s4_lean_s4_name_s11_get__prefix(obj*);
obj* _l_s4_lean_s4_name_s14_update__prefix(obj*, obj*);
obj* _l_s4_lean_s4_name_s12_has__dec__eq(obj*, obj*);
obj* _l_s4_lean_s4_name_s4_lean_s15_has__to__format(obj*);
obj* _l_s4_lean_s4_name_s4_hash_s11___closed__1_s7___boxed;
obj* _l_s4_lean_s4_name_s8_hashable;
obj* _l_s9___private_1272448207__s9_hash__aux(obj*, size_t);
obj* _l_s4_lean_s4_name_s14_components_x27(obj*);
obj* _l_s4_lean_s4_name_s21_to__string__with__sep(obj*, obj*);
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj*, obj*);
obj* _l_s4_lean_s4_name_s10_to__string_s11___closed__1;
obj* _l_s4_lean_s4_name_s4_hash(obj*);
obj* _l_s4_lean_s13_mk__str__name(obj*, obj*);
obj* _l_s4_lean_s4_name_s14_components_x27_s6___main(obj*);
obj* _l_s9___private_1272448207__s9_hash__aux_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s4_name_s13_decidable__eq;
obj* _l_s4_lean_s4_name_s15_has__to__string;
obj* _l_s4_lean_s4_name_s6_append(obj*, obj*);
obj* _l_s4_lean_s4_name_s11_has__append;
obj* _l_s4_lean_s4_name_s10_components(obj*);
obj* _l_s4_list_s7_reverse_s6___rarg(obj*);
obj* _l_s4_lean_s9_inhabited;
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(obj*, obj*);
obj* _l_s4_lean_s4_name_s11_get__prefix_s6___main(obj*);
obj* _l_s9___private_1272448207__s9_hash__aux_s6___main_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s4_name_s14_has__lt__quick;
obj* _l_s4_lean_s16_string__to__name;
obj* _l_s4_lean_s4_name_s6_append_s6___main(obj*, obj*);
obj* _l_s4_lean_s13_mk__num__name(obj*, obj*);
obj* _l_s4_lean_s4_name_s15_replace__prefix_s6___main(obj*, obj*, obj*);
extern size_t _l_s9_mix__hash_s11___closed__1;
obj* _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(obj*, obj*);
obj* _l_s4_lean_s4_name_s15_replace__prefix(obj*, obj*, obj*);
obj* _l_s9___private_1272448207__s9_hash__aux_s6___main(obj*, size_t);
obj* _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main_s11___closed__1;
obj* _l_s4_lean_s4_name_s14_update__prefix_s6___main(obj*, obj*);
obj* _init__l_s4_lean_s9_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s4_lean_s13_mk__str__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s4_lean_s13_mk__num__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s4_lean_s16_mk__simple__name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_cnstr(0, 0, 0);
;
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s16_string__to__name() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s16_mk__simple__name), 1, 0);
return x_0;
}
}
obj* _l_s9___private_1272448207__s9_hash__aux_s6___main(obj* x_0, size_t x_1) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box_size_t(x_1);
return x_3;
}
case 1:
{
obj* x_4; size_t x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = _l_s9_mix__hash_s11___closed__1;
x_8 = _l_s9___private_1272448207__s9_hash__aux_s6___main(x_4, x_7);
x_0 = x_4;
x_1 = x_7;
goto _start;
}
default:
{
obj* x_9; size_t x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = _l_s9_mix__hash_s11___closed__1;
x_13 = _l_s9___private_1272448207__s9_hash__aux_s6___main(x_9, x_12);
x_0 = x_9;
x_1 = x_12;
goto _start;
}
}
}
}
obj* _l_s9___private_1272448207__s9_hash__aux_s6___main_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = _l_s9___private_1272448207__s9_hash__aux_s6___main(x_0, x_2);
return x_3;
}
}
obj* _l_s9___private_1272448207__s9_hash__aux(obj* x_0, size_t x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s9___private_1272448207__s9_hash__aux_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s9___private_1272448207__s9_hash__aux_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = _l_s9___private_1272448207__s9_hash__aux(x_0, x_2);
return x_3;
}
}
obj* _l_s4_lean_s4_name_s4_hash(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = _l_s4_lean_s4_name_s4_hash_s11___closed__1;
x_2 = _l_s9___private_1272448207__s9_hash__aux_s6___main(x_0, x_1);
return x_2;
}
}
size_t _init__l_s4_lean_s4_name_s4_hash_s11___closed__1() {
_start:
{
obj* x_0; size_t x_1; size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
x_3 = lean::usize_add(x_1, x_1);
x_4 = lean::usize_add(x_3, x_3);
x_5 = lean::usize_add(x_4, x_1);
x_6 = lean::usize_add(x_5, x_5);
x_7 = lean::usize_add(x_6, x_1);
return x_7;
}
}
obj* _init__l_s4_lean_s4_name_s4_hash_s11___closed__1_s7___boxed() {
_start:
{
size_t x_0; obj* x_1; 
x_0 = _l_s4_lean_s4_name_s4_hash_s11___closed__1;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s4_name_s8_hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s4_name_s4_hash), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s4_name_s11_get__prefix_s6___main(obj* x_0) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{

return x_0;
}
case 1:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
default:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
return x_4;
}
}
}
}
obj* _l_s4_lean_s4_name_s11_get__prefix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s4_lean_s4_name_s11_get__prefix_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s4_name_s14_update__prefix_s6___main(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_6; 
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
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
default:
{
obj* x_7; obj* x_9; obj* x_10; 
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
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
}
}
}
obj* _l_s4_lean_s4_name_s14_update__prefix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s14_update__prefix_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s4_name_s14_components_x27_s6___main(obj* x_0) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
x_8 = lean::alloc_cnstr(0, 0, 0);
;
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = _l_s4_lean_s4_name_s14_components_x27_s6___main(x_3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
default:
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_16 = x_0;
}
x_17 = lean::alloc_cnstr(0, 0, 0);
;
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
x_19 = _l_s4_lean_s4_name_s14_components_x27_s6___main(x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* _l_s4_lean_s4_name_s14_components_x27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s4_lean_s4_name_s14_components_x27_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s4_name_s10_components(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s4_name_s14_components_x27_s6___main(x_0);
x_2 = _l_s4_list_s7_reverse_s6___rarg(x_1);
return x_2;
}
}
obj* _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(obj* x_0, obj* x_1) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{

lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::alloc_cnstr(1, 0, 0);
;
return x_4;
}
case 1:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::alloc_cnstr(0, 0, 0);
;
return x_6;
}
default:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::alloc_cnstr(0, 0, 0);
;
return x_8;
}
}
}
case 1:
{
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_17; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_1);
x_17 = lean::alloc_cnstr(0, 0, 0);
;
return x_17;
}
case 1:
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
lean::dec(x_1);
x_23 = lean::string_dec_eq(x_11, x_20);
lean::dec(x_20);
lean::dec(x_11);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; 
lean::dec(x_18);
lean::dec(x_23);
lean::dec(x_9);
x_29 = lean::alloc_cnstr(0, 0, 0);
;
return x_29;
}
else
{
obj* x_31; 
lean::dec(x_23);
x_31 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_9, x_18);
x_0 = x_9;
x_1 = x_18;
goto _start;
}
}
default:
{
obj* x_35; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_1);
x_35 = lean::alloc_cnstr(0, 0, 0);
;
return x_35;
}
}
}
default:
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 1);
lean::inc(x_38);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_44; 
lean::dec(x_1);
lean::dec(x_36);
lean::dec(x_38);
x_44 = lean::alloc_cnstr(0, 0, 0);
;
return x_44;
}
case 1:
{
obj* x_48; 
lean::dec(x_1);
lean::dec(x_36);
lean::dec(x_38);
x_48 = lean::alloc_cnstr(0, 0, 0);
;
return x_48;
}
default:
{
obj* x_49; obj* x_51; obj* x_54; 
x_49 = lean::cnstr_get(x_1, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_1, 1);
lean::inc(x_51);
lean::dec(x_1);
x_54 = lean::nat_dec_eq(x_38, x_51);
lean::dec(x_51);
lean::dec(x_38);
if (lean::obj_tag(x_54) == 0)
{
obj* x_60; 
lean::dec(x_49);
lean::dec(x_36);
lean::dec(x_54);
x_60 = lean::alloc_cnstr(0, 0, 0);
;
return x_60;
}
else
{
obj* x_62; 
lean::dec(x_54);
x_62 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_36, x_49);
x_0 = x_36;
x_1 = x_49;
goto _start;
}
}
}
}
}
}
}
obj* _l_s4_lean_s4_name_s12_has__dec__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s4_name_s13_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s4_name_s12_has__dec__eq), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s4_name_s6_append_s6___main(obj* x_0, obj* x_1) {
_start:
{

switch (lean::obj_tag(x_1)) {
case 0:
{

lean::dec(x_1);
return x_0;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
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
x_8 = _l_s4_lean_s4_name_s6_append_s6___main(x_0, x_3);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
default:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = _l_s4_lean_s4_name_s6_append_s6___main(x_0, x_10);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
}
}
}
obj* _l_s4_lean_s4_name_s6_append(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s6_append_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s4_name_s11_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s4_name_s6_append), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s4_name_s15_replace__prefix_s6___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_1, x_0);
if (lean::obj_tag(x_4) == 0)
{

lean::dec(x_2);
lean::dec(x_4);
return x_0;
}
else
{

lean::dec(x_0);
lean::dec(x_4);
return x_2;
}
}
case 1:
{
obj* x_9; obj* x_11; obj* x_14; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::inc(x_1);
x_14 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_0, x_1);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_14);
x_16 = _l_s4_lean_s4_name_s15_replace__prefix_s6___main(x_9, x_1, x_2);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_11);
return x_17;
}
else
{

lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_14);
lean::dec(x_1);
return x_2;
}
}
default:
{
obj* x_22; obj* x_24; obj* x_27; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::inc(x_1);
x_27 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_0, x_1);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_27);
x_29 = _l_s4_lean_s4_name_s15_replace__prefix_s6___main(x_22, x_1, x_2);
x_30 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_24);
return x_30;
}
else
{

lean::dec(x_27);
lean::dec(x_1);
lean::dec(x_22);
lean::dec(x_24);
return x_2;
}
}
}
}
}
obj* _l_s4_lean_s4_name_s15_replace__prefix(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_lean_s4_name_s15_replace__prefix_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj* x_0, obj* x_1) {
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
unsigned char x_4; obj* x_5; 
lean::dec(x_2);
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
else
{
unsigned char x_7; obj* x_8; 
lean::dec(x_2);
x_7 = 0;
x_8 = lean::box(x_7);
return x_8;
}
}
case 1:
{
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 0:
{
unsigned char x_17; obj* x_18; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_1);
x_17 = 0;
x_18 = lean::box(x_17);
return x_18;
}
case 1:
{
obj* x_19; obj* x_21; obj* x_24; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::string_dec_lt(x_11, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
lean::dec(x_24);
x_26 = lean::string_dec_eq(x_11, x_21);
lean::dec(x_21);
lean::dec(x_11);
if (lean::obj_tag(x_26) == 0)
{
unsigned char x_32; obj* x_33; 
lean::dec(x_19);
lean::dec(x_9);
lean::dec(x_26);
x_32 = 0;
x_33 = lean::box(x_32);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_26);
x_35 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_9, x_19);
x_0 = x_9;
x_1 = x_19;
goto _start;
}
}
else
{
unsigned char x_41; obj* x_42; 
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_9);
lean::dec(x_21);
lean::dec(x_24);
x_41 = 1;
x_42 = lean::box(x_41);
return x_42;
}
}
default:
{
unsigned char x_46; obj* x_47; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_1);
x_46 = 0;
x_47 = lean::box(x_46);
return x_47;
}
}
}
default:
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_0, 1);
lean::inc(x_50);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 0:
{
unsigned char x_56; obj* x_57; 
lean::dec(x_50);
lean::dec(x_1);
lean::dec(x_48);
x_56 = 0;
x_57 = lean::box(x_56);
return x_57;
}
case 1:
{
unsigned char x_61; obj* x_62; 
lean::dec(x_50);
lean::dec(x_1);
lean::dec(x_48);
x_61 = 1;
x_62 = lean::box(x_61);
return x_62;
}
default:
{
obj* x_63; obj* x_65; obj* x_68; 
x_63 = lean::cnstr_get(x_1, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_1, 1);
lean::inc(x_65);
lean::dec(x_1);
x_68 = lean::nat_dec_lt(x_50, x_65);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; 
lean::dec(x_68);
x_70 = lean::nat_dec_eq(x_50, x_65);
lean::dec(x_65);
lean::dec(x_50);
if (lean::obj_tag(x_70) == 0)
{
unsigned char x_76; obj* x_77; 
lean::dec(x_63);
lean::dec(x_70);
lean::dec(x_48);
x_76 = 0;
x_77 = lean::box(x_76);
return x_77;
}
else
{
obj* x_79; 
lean::dec(x_70);
x_79 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_48, x_63);
x_0 = x_48;
x_1 = x_63;
goto _start;
}
}
else
{
unsigned char x_85; obj* x_86; 
lean::dec(x_63);
lean::dec(x_65);
lean::dec(x_68);
lean::dec(x_50);
lean::dec(x_48);
x_85 = 1;
x_86 = lean::box(x_85);
return x_86;
}
}
}
}
}
}
}
obj* _l_s4_lean_s4_name_s9_quick__lt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s4_name_s14_has__lt__quick() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s4_lean_s4_name_s14_decidable__rel(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(obj* x_0, obj* x_1) {
_start:
{

switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main_s11___closed__1;
lean::inc(x_4);
return x_4;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_6);
x_13 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_6, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_13);
lean::inc(x_0);
x_16 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(x_0, x_6);
x_17 = lean::string_append(x_16, x_0);
lean::dec(x_0);
x_19 = lean::string_append(x_17, x_8);
lean::dec(x_8);
return x_19;
}
else
{

lean::dec(x_6);
lean::dec(x_13);
lean::dec(x_0);
return x_8;
}
}
default:
{
obj* x_24; obj* x_26; obj* x_29; obj* x_31; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
x_29 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_24);
x_31 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_24, x_29);
if (lean::obj_tag(x_31) == 0)
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_31);
lean::inc(x_0);
x_34 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(x_0, x_24);
x_35 = lean::string_append(x_34, x_0);
lean::dec(x_0);
x_37 = _l_s3_nat_s4_repr(x_26);
x_38 = lean::string_append(x_35, x_37);
lean::dec(x_37);
return x_38;
}
else
{
obj* x_43; 
lean::dec(x_0);
lean::dec(x_31);
lean::dec(x_24);
x_43 = _l_s3_nat_s4_repr(x_26);
return x_43;
}
}
}
}
}
obj* _init__l_s4_lean_s4_name_s21_to__string__with__sep_s6___main_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[anonymous]");
return x_0;
}
}
obj* _l_s4_lean_s4_name_s21_to__string__with__sep(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s4_name_s10_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = _l_s4_lean_s4_name_s10_to__string_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(x_1, x_0);
return x_3;
}
}
obj* _init__l_s4_lean_s4_name_s10_to__string_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".");
return x_0;
}
}
obj* _init__l_s4_lean_s4_name_s15_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s4_name_s10_to__string), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s4_name_s4_lean_s15_has__to__format(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = _l_s4_lean_s4_name_s10_to__string_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main(x_1, x_0);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
void _l_initialize__l_s4_init_s3_coe();
void _l_initialize__l_s4_init_s4_data_s4_uint();
void _l_initialize__l_s4_init_s4_data_s10_to__string();
void _l_initialize__l_s4_init_s4_lean_s6_format();
void _l_initialize__l_s4_init_s4_data_s8_hashable();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s4_name() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_initialize__l_s4_init_s3_coe();
 _l_initialize__l_s4_init_s4_data_s4_uint();
 _l_initialize__l_s4_init_s4_data_s10_to__string();
 _l_initialize__l_s4_init_s4_lean_s6_format();
 _l_initialize__l_s4_init_s4_data_s8_hashable();
 _l_s4_lean_s9_inhabited = _init__l_s4_lean_s9_inhabited();
 _l_s4_lean_s16_string__to__name = _init__l_s4_lean_s16_string__to__name();
 _l_s4_lean_s4_name_s4_hash_s11___closed__1 = _init__l_s4_lean_s4_name_s4_hash_s11___closed__1();
 _l_s4_lean_s4_name_s4_hash_s11___closed__1_s7___boxed = _init__l_s4_lean_s4_name_s4_hash_s11___closed__1_s7___boxed();
 _l_s4_lean_s4_name_s8_hashable = _init__l_s4_lean_s4_name_s8_hashable();
 _l_s4_lean_s4_name_s13_decidable__eq = _init__l_s4_lean_s4_name_s13_decidable__eq();
 _l_s4_lean_s4_name_s11_has__append = _init__l_s4_lean_s4_name_s11_has__append();
 _l_s4_lean_s4_name_s14_has__lt__quick = _init__l_s4_lean_s4_name_s14_has__lt__quick();
 _l_s4_lean_s4_name_s21_to__string__with__sep_s6___main_s11___closed__1 = _init__l_s4_lean_s4_name_s21_to__string__with__sep_s6___main_s11___closed__1();
 _l_s4_lean_s4_name_s10_to__string_s11___closed__1 = _init__l_s4_lean_s4_name_s10_to__string_s11___closed__1();
 _l_s4_lean_s4_name_s15_has__to__string = _init__l_s4_lean_s4_name_s15_has__to__string();
}
