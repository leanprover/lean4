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
obj* l_lean_string__to__name;
obj* l___private_1272448207__hash__aux___boxed(obj*, obj*);
obj* l_lean_name_has__append;
obj* l_lean_name_decidable__eq;
obj* l_lean_mk__str__name(obj*, obj*);
obj* l_lean_name_components_x_27(obj*);
obj* l_lean_name_to__string(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_name_has__lt__quick;
obj* l_lean_name_replace__prefix(obj*, obj*, obj*);
obj* l_lean_name_has__dec__eq___main(obj*, obj*);
obj* l___private_1272448207__hash__aux___main(obj*, size_t);
obj* l_lean_inhabited;
obj* l_lean_name_to__string___closed__1;
obj* l_lean_name_decidable__rel(obj*, obj*);
obj* l_lean_name_append(obj*, obj*);
obj* l_lean_name_hashable;
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_name_components(obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_name_update__prefix(obj*, obj*);
obj* l_lean_name_components_x_27___main(obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep(obj*, obj*);
obj* l_lean_name_has__dec__eq(obj*, obj*);
obj* l_lean_mk__num__name(obj*, obj*);
obj* l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_mk__simple__name(obj*);
obj* l_lean_name_lean_has__to__format(obj*);
obj* l___private_1272448207__hash__aux(obj*, size_t);
obj* l_lean_name_update__prefix___main(obj*, obj*);
obj* l_lean_name_get__prefix(obj*);
obj* l___private_1272448207__hash__aux___main___boxed(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_name_get__prefix___main(obj*);
obj* l_lean_name_hash___boxed(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main___closed__1;
obj* l_lean_name_has__to__string;
extern size_t l_mix__hash___closed__1;
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_mk__num__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_lean_mk__simple__name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::name_mk_string(x_1, x_0);
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
obj* l___private_1272448207__hash__aux___main(obj* x_0, size_t x_1) {
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
obj* x_4; size_t x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_mix__hash___closed__1;
x_0 = x_4;
x_1 = x_7;
goto _start;
}
default:
{
obj* x_9; size_t x_12; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_mix__hash___closed__1;
x_0 = x_9;
x_1 = x_12;
goto _start;
}
}
}
}
obj* l___private_1272448207__hash__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_1272448207__hash__aux___main(x_0, x_2);
return x_3;
}
}
obj* l___private_1272448207__hash__aux(obj* x_0, size_t x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_1272448207__hash__aux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_1272448207__hash__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_1272448207__hash__aux(x_0, x_2);
return x_3;
}
}
obj* l_lean_name_hash___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = lean::name_hash_usize(x_0);
x_2 = lean::box_size_t(x_1);
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
x_6 = lean::name_mk_string(x_1, x_3);
return x_6;
}
default:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::name_mk_numeral(x_1, x_7);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::box(0);
x_9 = lean::name_mk_string(x_8, x_5);
x_10 = l_lean_name_components_x_27___main(x_3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
default:
{
obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = lean::name_mk_numeral(x_17, x_14);
x_19 = l_lean_name_components_x_27___main(x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
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
obj* l_lean_name_has__dec__eq___main(obj* x_0, obj* x_1) {
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
x_4 = lean::box(1);
return x_4;
}
case 1:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::box(0);
return x_6;
}
default:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::box(0);
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
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::box(0);
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
lean::dec(x_9);
lean::dec(x_18);
lean::dec(x_23);
x_29 = lean::box(0);
return x_29;
}
else
{
lean::dec(x_23);
x_0 = x_9;
x_1 = x_18;
goto _start;
}
}
default:
{
obj* x_35; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_35 = lean::box(0);
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
x_44 = lean::box(0);
return x_44;
}
case 1:
{
obj* x_48; 
lean::dec(x_1);
lean::dec(x_36);
lean::dec(x_38);
x_48 = lean::box(0);
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
x_60 = lean::box(0);
return x_60;
}
else
{
lean::dec(x_54);
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
obj* l_lean_name_has__dec__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_has__dec__eq___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_name_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_has__dec__eq), 2, 0);
return x_0;
}
}
obj* l_lean_name_append___main(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_lean_name_append___main(x_0, x_3);
x_9 = lean::name_mk_string(x_8, x_5);
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
x_16 = lean::name_mk_numeral(x_15, x_12);
return x_16;
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
obj* x_4; 
lean::inc(x_0);
x_4 = l_lean_name_has__dec__eq___main(x_1, x_0);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_0;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
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
x_14 = l_lean_name_has__dec__eq___main(x_0, x_1);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_14);
x_16 = l_lean_name_replace__prefix___main(x_9, x_1, x_2);
x_17 = lean::name_mk_string(x_16, x_11);
return x_17;
}
else
{
lean::dec(x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_11);
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
x_27 = l_lean_name_has__dec__eq___main(x_0, x_1);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_27);
x_29 = l_lean_name_replace__prefix___main(x_22, x_1, x_2);
x_30 = lean::name_mk_numeral(x_29, x_24);
return x_30;
}
else
{
lean::dec(x_24);
lean::dec(x_27);
lean::dec(x_1);
lean::dec(x_22);
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
obj* x_2; 
x_2 = l_lean_name_has__dec__eq___main(x_1, x_0);
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
lean::dec(x_26);
lean::dec(x_19);
lean::dec(x_9);
x_32 = 0;
x_33 = lean::box(x_32);
return x_33;
}
else
{
lean::dec(x_26);
x_0 = x_9;
x_1 = x_19;
goto _start;
}
}
else
{
unsigned char x_41; obj* x_42; 
lean::dec(x_19);
lean::dec(x_11);
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
lean::dec(x_1);
lean::dec(x_48);
lean::dec(x_50);
x_56 = 0;
x_57 = lean::box(x_56);
return x_57;
}
case 1:
{
unsigned char x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_48);
lean::dec(x_50);
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
lean::dec(x_48);
lean::dec(x_70);
lean::dec(x_63);
x_76 = 0;
x_77 = lean::box(x_76);
return x_77;
}
else
{
lean::dec(x_70);
x_0 = x_48;
x_1 = x_63;
goto _start;
}
}
else
{
unsigned char x_85; obj* x_86; 
lean::dec(x_48);
lean::dec(x_50);
lean::dec(x_65);
lean::dec(x_63);
lean::dec(x_68);
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
obj* l_lean_name_decidable__rel(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_quick__lt___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_to__string__with__sep___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_name_to__string__with__sep___main___closed__1;
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
x_11 = lean::box(0);
lean::inc(x_6);
x_13 = l_lean_name_has__dec__eq___main(x_6, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_13);
lean::inc(x_0);
x_16 = l_lean_name_to__string__with__sep___main(x_0, x_6);
x_17 = lean::string_append(x_16, x_0);
lean::dec(x_0);
x_19 = lean::string_append(x_17, x_8);
lean::dec(x_8);
return x_19;
}
else
{
lean::dec(x_13);
lean::dec(x_6);
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
x_29 = lean::box(0);
lean::inc(x_24);
x_31 = l_lean_name_has__dec__eq___main(x_24, x_29);
if (lean::obj_tag(x_31) == 0)
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_31);
lean::inc(x_0);
x_34 = l_lean_name_to__string__with__sep___main(x_0, x_24);
x_35 = lean::string_append(x_34, x_0);
lean::dec(x_0);
x_37 = l_nat_repr(x_26);
x_38 = lean::string_append(x_35, x_37);
lean::dec(x_37);
return x_38;
}
else
{
obj* x_43; 
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_24);
x_43 = l_nat_repr(x_26);
return x_43;
}
}
}
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
obj* l_lean_name_to__string__with__sep(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_to__string__with__sep___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_name_to__string___closed__1;
lean::inc(x_1);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_0);
return x_3;
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
obj* x_1; obj* x_3; obj* x_4; 
x_1 = l_lean_name_to__string___closed__1;
lean::inc(x_1);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
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
 l_lean_string__to__name = _init_l_lean_string__to__name();
 l_lean_name_hashable = _init_l_lean_name_hashable();
 l_lean_name_decidable__eq = _init_l_lean_name_decidable__eq();
 l_lean_name_has__append = _init_l_lean_name_has__append();
 l_lean_name_has__lt__quick = _init_l_lean_name_has__lt__quick();
 l_lean_name_to__string__with__sep___main___closed__1 = _init_l_lean_name_to__string__with__sep___main___closed__1();
 l_lean_name_to__string___closed__1 = _init_l_lean_name_to__string___closed__1();
 l_lean_name_has__to__string = _init_l_lean_name_has__to__string();
}
