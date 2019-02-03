// Lean compiler output
// Module: init.lean.kvmap
// Imports: init.lean.name init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s4_lean_s5_kvmap_s8_contains_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s8_get__nat(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s9_set__bool_s7___boxed(obj*, obj*, obj*);
unsigned char _l_s6_option_s8_is__some_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s5_kvmap_s10_find__core(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s4_find(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s8_set__nat(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s10_find__core_s6___main(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s4_find_s6___main(obj*, obj*);
unsigned char _l_s4_lean_s5_kvmap_s8_contains(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s6_insert_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s6_insert(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s11_get__string(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s12_insert__core(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s9_get__bool(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s11_set__string(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s9_set__bool(obj*, obj*, unsigned char);
obj* _l_s4_lean_s5_kvmap_s9_get__name(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s9_set__name(obj*, obj*, obj*);
obj* _l_s4_lean_s5_kvmap_s10_find__core_s6___main(obj* x_0, obj* x_1) {
_start:
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_1);
x_16 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_10, x_1);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
lean::dec(x_12);
lean::dec(x_16);
x_19 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_7, x_1);
x_0 = x_7;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_7);
lean::dec(x_16);
lean::dec(x_1);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_12);
return x_23;
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s10_find__core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s5_kvmap_s4_find_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s5_kvmap_s4_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; 
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
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::inc(x_1);
lean::inc(x_10);
x_14 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_10, x_1);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_10);
lean::dec(x_14);
x_17 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_7, x_1, x_2);
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
obj* x_22; obj* x_23; 
lean::dec(x_14);
lean::dec(x_5);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_2);
if (lean::is_scalar(x_9)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_9;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_7);
return x_23;
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s12_insert__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s5_kvmap_s6_insert_s6___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s5_kvmap_s6_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s5_kvmap_s8_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; unsigned char x_3; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
x_3 = _l_s6_option_s8_is__some_s6___main_s6___rarg(x_2);
return x_3;
}
}
obj* _l_s4_lean_s5_kvmap_s8_contains_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = _l_s4_lean_s5_kvmap_s8_contains(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _l_s4_lean_s5_kvmap_s11_get__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
case 1:
{
obj* x_14; 
lean::dec(x_5);
lean::dec(x_7);
x_14 = lean::alloc_cnstr(0, 0, 0);
;
return x_14;
}
case 2:
{
obj* x_17; 
lean::dec(x_5);
lean::dec(x_7);
x_17 = lean::alloc_cnstr(0, 0, 0);
;
return x_17;
}
default:
{
obj* x_20; 
lean::dec(x_5);
lean::dec(x_7);
x_20 = lean::alloc_cnstr(0, 0, 0);
;
return x_20;
}
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s8_get__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_10; 
lean::dec(x_5);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 0, 0);
;
return x_10;
}
case 1:
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
case 2:
{
obj* x_17; 
lean::dec(x_5);
lean::dec(x_7);
x_17 = lean::alloc_cnstr(0, 0, 0);
;
return x_17;
}
default:
{
obj* x_20; 
lean::dec(x_5);
lean::dec(x_7);
x_20 = lean::alloc_cnstr(0, 0, 0);
;
return x_20;
}
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s9_get__bool(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_10; 
lean::dec(x_5);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 0, 0);
;
return x_10;
}
case 1:
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 0, 0);
;
return x_13;
}
case 2:
{
unsigned char x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get_scalar<unsigned char>(x_5, 0);
lean::dec(x_5);
x_16 = lean::box(x_14);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
default:
{
obj* x_20; 
lean::dec(x_5);
lean::dec(x_7);
x_20 = lean::alloc_cnstr(0, 0, 0);
;
return x_20;
}
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s9_get__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_lean_s5_kvmap_s10_find__core_s6___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_10; 
lean::dec(x_5);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 0, 0);
;
return x_10;
}
case 1:
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 0, 0);
;
return x_13;
}
case 2:
{
obj* x_16; 
lean::dec(x_5);
lean::dec(x_7);
x_16 = lean::alloc_cnstr(0, 0, 0);
;
return x_16;
}
default:
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
}
}
}
}
obj* _l_s4_lean_s5_kvmap_s11_set__string(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s5_kvmap_s8_set__nat(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s5_kvmap_s9_set__bool(obj* x_0, obj* x_1, unsigned char x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_cnstr(2, 0, 1);
;
lean::cnstr_set_scalar(x_3, 0, x_2);
x_4 = x_3;
x_5 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_4);
return x_5;
}
}
obj* _l_s4_lean_s5_kvmap_s9_set__bool_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s4_lean_s5_kvmap_s9_set__bool(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s5_kvmap_s9_set__name(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = _l_s4_lean_s5_kvmap_s12_insert__core_s6___main(x_0, x_1, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_lean_s4_name();
void _l_initialize__l_s4_init_s4_data_s6_option_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s5_kvmap() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s4_name();
 _l_initialize__l_s4_init_s4_data_s6_option_s5_basic();
}
