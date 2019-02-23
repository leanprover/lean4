// Lean compiler output
// Module: init.lean.kvmap
// Imports: init.lean.name init.data.option.basic
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
obj* l_lean_kvmap_set__bool___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_set__name___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_get__nat___boxed(obj*, obj*);
obj* l_lean_kvmap_insert___main___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core(obj*, obj*, obj*);
uint8 l_lean_kvmap_contains(obj*, obj*);
obj* l_lean_kvmap_find___main___boxed(obj*, obj*);
obj* l_lean_kvmap_set__string___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_set__nat___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_get__bool(obj*, obj*);
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
obj* l_lean_kvmap_find___boxed(obj*, obj*);
obj* l_lean_kvmap_set__nat(obj*, obj*, obj*);
obj* l_lean_kvmap_find__core(obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_kvmap_get__bool___boxed(obj*, obj*);
obj* l_lean_kvmap_find__core___boxed(obj*, obj*);
obj* l_lean_kvmap_find__core___main___boxed(obj*, obj*);
obj* l_lean_kvmap_get__name___boxed(obj*, obj*);
obj* l_lean_kvmap_contains___boxed(obj*, obj*);
obj* l_lean_kvmap_insert(obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_find___main(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_kvmap_insert__core___main___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_find(obj*, obj*);
obj* l_lean_kvmap_get__name(obj*, obj*);
obj* l_lean_kvmap_insert___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
obj* l_lean_kvmap_find__core___main(obj*, obj*);
obj* l_lean_kvmap_get__string(obj*, obj*);
obj* l_lean_kvmap_get__string___boxed(obj*, obj*);
obj* l_lean_kvmap_get__nat(obj*, obj*);
obj* l_lean_kvmap_insert___main(obj*, obj*, obj*);
obj* l_lean_kvmap_find__core___main(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean_name_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_0 = x_4;
goto _start;
}
else
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
}
}
}
obj* l_lean_kvmap_find__core___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_find__core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_kvmap_find__core___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_kvmap_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_kvmap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_insert__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; uint8 x_14; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean_name_dec_eq(x_12, x_1);
if (x_14 == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_12);
x_16 = l_lean_kvmap_insert__core___main(x_9, x_1, x_2);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_21; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_18 = x_7;
} else {
 lean::dec(x_7);
 x_18 = lean::box(0);
}
lean::inc(x_2);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_2);
if (lean::is_scalar(x_11)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_11;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_9);
return x_21;
}
}
}
}
obj* l_lean_kvmap_insert__core___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert__core___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert__core___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert__core___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert__core(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert__core___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert__core___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_kvmap_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_insert(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_lean_kvmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
x_3 = l_option_is__some___main___rarg(x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_kvmap_contains(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_kvmap_get__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_lean_kvmap_get__string___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_get__string(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_get__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 1:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_lean_kvmap_get__nat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_get__nat(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_get__bool(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 2:
{
uint8 x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get_scalar<uint8>(x_4, 0);
lean::dec(x_4);
x_9 = lean::box(x_7);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_lean_kvmap_get__bool___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_get__bool(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_get__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_find__core___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 3:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_lean_kvmap_get__name___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_kvmap_get__name(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_kvmap_set__string(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
x_5 = l_lean_kvmap_insert__core___main(x_0, x_1, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_kvmap_set__string___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_set__string(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_set__nat(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
x_5 = l_lean_kvmap_insert__core___main(x_0, x_1, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_kvmap_set__nat___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_set__nat(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_kvmap_set__bool(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_cnstr(2, 0, 1);
lean::cnstr_set_scalar(x_3, 0, x_2);
x_4 = x_3;
x_5 = l_lean_kvmap_insert__core___main(x_0, x_1, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_kvmap_set__bool___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_lean_kvmap_set__bool(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_kvmap_set__name(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
x_5 = l_lean_kvmap_insert__core___main(x_0, x_1, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_kvmap_set__name___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_kvmap_set__name(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
void initialize_init_lean_name();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_lean_kvmap() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_name();
 initialize_init_data_option_basic();
}
