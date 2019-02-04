// Lean compiler output
// Module: init.lean.level
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
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_level__to__format_result_succ(obj*);
obj* l_lean_level__to__format_result_to__format___main(obj*, unsigned char);
obj* l_lean_level__to__format_result__list_to__format(obj*);
obj* l_lean_level_instantiate___main(obj*, obj*);
obj* l_lean_has__repr___lambda__1(obj*);
obj* l_lean_level_to__nat___main___closed__2;
obj* l_lean_level__to__format_paren__if__false(obj*, unsigned char);
obj* l_lean_level__to__format_result_to__format(obj*, unsigned char);
obj* l_lean_level__to__format_result_imax(obj*, obj*);
obj* l_lean_level__to__format_result_max___main(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_level_instantiate(obj*, obj*);
obj* l_lean_level__to__format_level_to__result(obj*);
obj* l_lean_level__to__format_result_to__format___boxed(obj*, obj*);
obj* l_lean_level_to__nat(obj*);
obj* l_lean_level__to__format_level_to__result___main___closed__1;
obj* l_lean_level_to__nat___main___closed__4;
obj* l_lean_level__to__format_paren__if__false___main(obj*, unsigned char);
obj* l_lean_level__to__format_level_to__result___main(obj*);
obj* l_lean_level__to__format_result_to__format___main___closed__3;
obj* l_nat_max(obj*, obj*);
extern obj* l_lean_format_paren___closed__3;
obj* l_lean_level__to__format_result_max(obj*, obj*);
obj* l_lean_level_to__nat___main___lambda__1(obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_level__to__format_result_succ___main(obj*);
obj* l_lean_level__to__format_result_to__format___main___closed__2;
obj* l_lean_level__to__format_paren__if__false___boxed(obj*, obj*);
obj* l_lean_to__fmt___at_lean_level__to__format_level_to__result___main___spec__1(obj*);
obj* l_lean_nat_imax(obj*, obj*);
obj* l_lean_level__to__format_level_to__format(obj*);
obj* l_lean_level_to__nat___main(obj*);
obj* l_lean_level__to__format_result_imax___main(obj*, obj*);
obj* l_lean_level_has__param(obj*);
obj* l_lean_to__fmt___at_lean_level__to__format_result_to__format___main___spec__1(obj*);
obj* l_lean_level_has__param___main(obj*);
obj* l_lean_level__to__format_paren__if__false___main___boxed(obj*, obj*);
obj* l_lean_level_of__nat___main(obj*);
obj* l_lean_level__is__inhabited;
obj* l_lean_level_of__nat(obj*);
obj* l_nat_repr(obj*);
obj* l_lean_level_to__offset___main(obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
extern obj* l_lean_format_paren___closed__1;
obj* l_lean_level__to__format_result__list_to__format___main(obj*);
obj* l_lean_level__to__format_level__has__to__string;
extern obj* l_lean_format_paren___closed__2;
obj* l_lean_level_to__nat___main___closed__1;
obj* l_lean_level__to__format_level__has__to__format;
obj* l_lean_format_group___main(obj*);
obj* l_lean_level_to__offset(obj*);
obj* l_lean_level_to__nat___main___closed__3;
obj* l_lean_level_has__mvar___main(obj*);
obj* l_lean_level__to__format_result_to__format___main___closed__1;
obj* l_lean_level_has__mvar(obj*);
obj* l_lean_level__to__format_result_to__format___main___boxed(obj*, obj*);
obj* _init_l_lean_level__is__inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* l_lean_level_has__param___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
unsigned char x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
case 1:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_0 = x_4;
goto _start;
}
case 2:
{
obj* x_8; obj* x_10; obj* x_13; unsigned char x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_level_has__param___main(x_8);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
lean::dec(x_13);
x_0 = x_10;
goto _start;
}
else
{
lean::dec(x_10);
x_0 = x_8;
goto _start;
}
}
case 3:
{
obj* x_18; obj* x_20; obj* x_23; unsigned char x_24; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_23 = l_lean_level_has__param___main(x_18);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
lean::dec(x_23);
x_0 = x_20;
goto _start;
}
else
{
lean::dec(x_20);
x_0 = x_18;
goto _start;
}
}
case 4:
{
unsigned char x_29; obj* x_30; 
lean::dec(x_0);
x_29 = 1;
x_30 = lean::box(x_29);
return x_30;
}
default:
{
unsigned char x_32; obj* x_33; 
lean::dec(x_0);
x_32 = 0;
x_33 = lean::box(x_32);
return x_33;
}
}
}
}
obj* l_lean_level_has__param(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level_has__param___main(x_0);
return x_1;
}
}
obj* l_lean_level_has__mvar___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
unsigned char x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
case 1:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_lean_level_has__param___main(x_4);
return x_7;
}
case 2:
{
obj* x_8; obj* x_10; obj* x_13; unsigned char x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_level_has__param___main(x_8);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_13);
x_16 = l_lean_level_has__param___main(x_10);
return x_16;
}
else
{
lean::dec(x_10);
return x_13;
}
}
case 3:
{
obj* x_18; obj* x_20; obj* x_23; unsigned char x_24; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_23 = l_lean_level_has__param___main(x_18);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
obj* x_26; 
lean::dec(x_23);
x_26 = l_lean_level_has__param___main(x_20);
return x_26;
}
else
{
lean::dec(x_20);
return x_23;
}
}
case 4:
{
unsigned char x_29; obj* x_30; 
lean::dec(x_0);
x_29 = 0;
x_30 = lean::box(x_29);
return x_30;
}
default:
{
unsigned char x_32; obj* x_33; 
lean::dec(x_0);
x_32 = 1;
x_33 = lean::box(x_32);
return x_33;
}
}
}
}
obj* l_lean_level_has__mvar(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level_has__mvar___main(x_0);
return x_1;
}
}
obj* l_lean_level_of__nat___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
x_9 = l_lean_level_of__nat___main(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
obj* x_13; 
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(0, 0, 0);
;
return x_13;
}
}
}
obj* l_lean_level_of__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level_of__nat___main(x_0);
return x_1;
}
}
obj* l_lean_nat_imax(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_3);
x_6 = l_nat_max(x_0, x_1);
return x_6;
}
else
{
obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
}
}
obj* l_lean_level_to__nat___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_level_to__nat___main___closed__1;
lean::inc(x_2);
return x_2;
}
case 1:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_lean_level_to__nat___main(x_4);
x_8 = l_lean_level_to__nat___main___closed__2;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_7);
return x_10;
}
case 2:
{
obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_19; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_lean_level_to__nat___main(x_11);
x_17 = l_lean_level_to__nat___main___closed__3;
lean::inc(x_17);
x_19 = l_option_map___rarg(x_17, x_16);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; 
lean::dec(x_13);
lean::dec(x_19);
x_22 = lean::alloc_cnstr(0, 0, 0);
;
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_19, 0);
lean::inc(x_23);
lean::dec(x_19);
x_26 = l_lean_level_to__nat___main(x_13);
x_27 = l_option_map___rarg(x_23, x_26);
return x_27;
}
}
case 3:
{
obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_36; 
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_lean_level_to__nat___main(x_28);
x_34 = l_lean_level_to__nat___main___closed__4;
lean::inc(x_34);
x_36 = l_option_map___rarg(x_34, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; 
lean::dec(x_30);
lean::dec(x_36);
x_39 = lean::alloc_cnstr(0, 0, 0);
;
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
lean::dec(x_36);
x_43 = l_lean_level_to__nat___main(x_30);
x_44 = l_option_map___rarg(x_40, x_43);
return x_44;
}
}
case 4:
{
obj* x_46; 
lean::dec(x_0);
x_46 = lean::alloc_cnstr(0, 0, 0);
;
return x_46;
}
default:
{
obj* x_48; 
lean::dec(x_0);
x_48 = lean::alloc_cnstr(0, 0, 0);
;
return x_48;
}
}
}
}
obj* _init_l_lean_level_to__nat___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_level_to__nat___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_level_to__nat___main___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_level_to__nat___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_max), 2, 0);
return x_0;
}
}
obj* _init_l_lean_level_to__nat___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_nat_imax), 2, 0);
return x_0;
}
}
obj* l_lean_level_to__nat___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::nat_add(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_level_to__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level_to__nat___main(x_0);
return x_1;
}
}
obj* l_lean_level_to__offset___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
case 1:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_level_to__offset___main(x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_9, x_12);
lean::dec(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_7);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
case 2:
{
obj* x_17; obj* x_18; 
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
case 3:
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_0);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
case 4:
{
obj* x_21; obj* x_22; 
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
default:
{
obj* x_23; obj* x_24; 
x_23 = lean::mk_nat_obj(0u);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_lean_level_to__offset(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level_to__offset___main(x_0);
return x_1;
}
}
obj* l_lean_level_instantiate___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_0);
return x_1;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
x_6 = l_lean_level_instantiate___main(x_0, x_3);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
case 2:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_12 = x_1;
}
lean::inc(x_0);
x_14 = l_lean_level_instantiate___main(x_0, x_8);
x_15 = l_lean_level_instantiate___main(x_0, x_10);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
case 3:
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 1);
lean::inc(x_19);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_21 = x_1;
}
lean::inc(x_0);
x_23 = l_lean_level_instantiate___main(x_0, x_17);
x_24 = l_lean_level_instantiate___main(x_0, x_19);
if (lean::is_scalar(x_21)) {
 x_25 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_25 = x_21;
}
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
case 4:
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
x_28 = lean::apply_1(x_0, x_26);
if (lean::obj_tag(x_28) == 0)
{
lean::dec(x_28);
return x_1;
}
else
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
return x_31;
}
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_lean_level_instantiate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_level_instantiate___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_result_succ___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
}
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_3, x_6);
lean::dec(x_6);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_5;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
case 2:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_15 = x_0;
}
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_13, x_16);
lean::dec(x_16);
lean::dec(x_13);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(2, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_17);
return x_20;
}
case 3:
{
obj* x_21; obj* x_22; 
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
default:
{
obj* x_23; obj* x_24; 
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_lean_level__to__format_result_succ(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level__to__format_result_succ___main(x_0);
return x_1;
}
}
obj* l_lean_level__to__format_result_max___main(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
switch (lean::obj_tag(x_1)) {
case 0:
{
unsigned char x_4; 
x_4 = 0;
x_2 = x_4;
goto lbl_3;
}
case 1:
{
unsigned char x_5; 
x_5 = 0;
x_2 = x_5;
goto lbl_3;
}
case 2:
{
unsigned char x_6; 
x_6 = 0;
x_2 = x_6;
goto lbl_3;
}
case 3:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_9 = x_1;
}
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(3, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
default:
{
unsigned char x_12; 
x_12 = 0;
x_2 = x_12;
goto lbl_3;
}
}
lbl_3:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::alloc_cnstr(0, 0, 0);
;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
}
obj* l_lean_level__to__format_result_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_level__to__format_result_max___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_result_imax___main(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
switch (lean::obj_tag(x_1)) {
case 0:
{
unsigned char x_4; 
x_4 = 0;
x_2 = x_4;
goto lbl_3;
}
case 1:
{
unsigned char x_5; 
x_5 = 0;
x_2 = x_5;
goto lbl_3;
}
case 2:
{
unsigned char x_6; 
x_6 = 0;
x_2 = x_6;
goto lbl_3;
}
case 3:
{
unsigned char x_7; 
x_7 = 0;
x_2 = x_7;
goto lbl_3;
}
default:
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
}
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
lbl_3:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::alloc_cnstr(0, 0, 0);
;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
}
obj* l_lean_level__to__format_result_imax(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_level__to__format_result_imax___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_paren__if__false___main(obj* x_0, unsigned char x_1) {
_start:
{
if (x_1 == 0)
{
unsigned char x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = 0;
x_3 = l_lean_format_paren___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_2);
x_6 = x_5;
x_7 = l_lean_format_paren___closed__2;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_2);
x_10 = x_9;
x_11 = l_lean_format_paren___closed__3;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_10);
x_14 = l_lean_format_group___main(x_13);
return x_14;
}
else
{
return x_0;
}
}
}
obj* l_lean_level__to__format_paren__if__false___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_lean_level__to__format_paren__if__false___main(x_0, x_2);
return x_3;
}
}
obj* l_lean_level__to__format_paren__if__false(obj* x_0, unsigned char x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_level__to__format_paren__if__false___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_paren__if__false___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_lean_level__to__format_paren__if__false(x_0, x_2);
return x_3;
}
}
obj* l_lean_level__to__format_result_to__format___main(obj* x_0, unsigned char x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
return x_2;
}
case 1:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_nat_repr(x_5);
x_9 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
case 2:
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::mk_nat_obj(0u);
x_16 = lean::nat_dec_eq(x_12, x_15);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_20; unsigned char x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_12, x_19);
lean::dec(x_12);
x_22 = 0;
x_23 = l_lean_level__to__format_result_to__format___main(x_10, x_22);
x_24 = l_lean_level__to__format_result_to__format___main___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_22);
x_27 = x_26;
x_28 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_31 = l_lean_to__fmt___at_lean_level__to__format_result_to__format___main___spec__1(x_28);
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_22);
x_33 = x_32;
x_34 = l_lean_level__to__format_paren__if__false___main(x_33, x_1);
return x_34;
}
else
{
lean::dec(x_12);
lean::dec(x_16);
x_0 = x_10;
goto _start;
}
}
case 3:
{
obj* x_38; obj* x_41; unsigned char x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = l_lean_level__to__format_result__list_to__format___main(x_38);
x_42 = 0;
x_43 = l_lean_level__to__format_result_to__format___main___closed__2;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_41);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_42);
x_46 = x_45;
x_47 = l_lean_format_group___main(x_46);
x_48 = l_lean_level__to__format_paren__if__false___main(x_47, x_1);
return x_48;
}
default:
{
obj* x_49; obj* x_52; unsigned char x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
lean::dec(x_0);
x_52 = l_lean_level__to__format_result__list_to__format___main(x_49);
x_53 = 0;
x_54 = l_lean_level__to__format_result_to__format___main___closed__3;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_53);
x_57 = x_56;
x_58 = l_lean_format_group___main(x_57);
x_59 = l_lean_level__to__format_paren__if__false___main(x_58, x_1);
return x_59;
}
}
}
}
obj* _init_l_lean_level__to__format_result_to__format___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("+");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_level__to__format_result_to__format___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_level__to__format_result_to__format___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("imax");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_to__fmt___at_lean_level__to__format_result_to__format___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_result__list_to__format___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
else
{
obj* x_3; obj* x_5; unsigned char x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = 0;
x_9 = l_lean_level__to__format_result_to__format___main(x_3, x_8);
x_10 = lean::alloc_cnstr(1, 0, 0);
;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_8);
x_12 = x_11;
x_13 = l_lean_level__to__format_result__list_to__format___main(x_5);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_8);
x_15 = x_14;
return x_15;
}
}
}
obj* l_lean_level__to__format_result_to__format___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_lean_level__to__format_result_to__format___main(x_0, x_2);
return x_3;
}
}
obj* l_lean_level__to__format_result_to__format(obj* x_0, unsigned char x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_level__to__format_result_to__format___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_level__to__format_result_to__format___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_lean_level__to__format_result_to__format(x_0, x_2);
return x_3;
}
}
obj* l_lean_level__to__format_result__list_to__format(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level__to__format_result__list_to__format___main(x_0);
return x_1;
}
}
obj* l_lean_level__to__format_level_to__result___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_level__to__format_level_to__result___main___closed__1;
lean::inc(x_2);
return x_2;
}
case 1:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_lean_level__to__format_level_to__result___main(x_4);
x_8 = l_lean_level__to__format_result_succ___main(x_7);
return x_8;
}
case 2:
{
obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
x_14 = l_lean_level__to__format_level_to__result___main(x_9);
x_15 = l_lean_level__to__format_level_to__result___main(x_11);
x_16 = l_lean_level__to__format_result_max___main(x_14, x_15);
return x_16;
}
case 3:
{
obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_level__to__format_level_to__result___main(x_17);
x_23 = l_lean_level__to__format_level_to__result___main(x_19);
x_24 = l_lean_level__to__format_result_imax___main(x_22, x_23);
return x_24;
}
case 4:
{
obj* x_25; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = l_lean_to__fmt___at_lean_level__to__format_level_to__result___main___spec__1(x_25);
x_29 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
default:
{
obj* x_30; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_lean_to__fmt___at_lean_level__to__format_level_to__result___main___spec__1(x_30);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
obj* _init_l_lean_level__to__format_level_to__result___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_to__fmt___at_lean_level__to__format_level_to__result___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = l_lean_name_to__string___closed__1;
lean::inc(x_1);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_level__to__format_level_to__result(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_level__to__format_level_to__result___main(x_0);
return x_1;
}
}
obj* l_lean_level__to__format_level_to__format(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_2; obj* x_3; 
x_1 = l_lean_level__to__format_level_to__result___main(x_0);
x_2 = 1;
x_3 = l_lean_level__to__format_result_to__format___main(x_1, x_2);
return x_3;
}
}
obj* _init_l_lean_level__to__format_level__has__to__format() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_level__to__format_level_to__format), 1, 0);
return x_0;
}
}
obj* _init_l_lean_level__to__format_level__has__to__string() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_has__repr___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_level__to__format_level_to__format), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
void initialize_init_lean_name();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_lean_level() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_name();
 initialize_init_data_option_basic();
 l_lean_level__is__inhabited = _init_l_lean_level__is__inhabited();
 l_lean_level_to__nat___main___closed__1 = _init_l_lean_level_to__nat___main___closed__1();
 l_lean_level_to__nat___main___closed__2 = _init_l_lean_level_to__nat___main___closed__2();
 l_lean_level_to__nat___main___closed__3 = _init_l_lean_level_to__nat___main___closed__3();
 l_lean_level_to__nat___main___closed__4 = _init_l_lean_level_to__nat___main___closed__4();
 l_lean_level__to__format_result_to__format___main___closed__1 = _init_l_lean_level__to__format_result_to__format___main___closed__1();
 l_lean_level__to__format_result_to__format___main___closed__2 = _init_l_lean_level__to__format_result_to__format___main___closed__2();
 l_lean_level__to__format_result_to__format___main___closed__3 = _init_l_lean_level__to__format_result_to__format___main___closed__3();
 l_lean_level__to__format_level_to__result___main___closed__1 = _init_l_lean_level__to__format_level_to__result___main___closed__1();
 l_lean_level__to__format_level__has__to__format = _init_l_lean_level__to__format_level__has__to__format();
 l_lean_level__to__format_level__has__to__string = _init_l_lean_level__to__format_level__has__to__string();
}
