// Lean compiler output
// Module: init.lean.message
// Imports: init.data.to_string init.lean.position
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_message_to__string___closed__5;
obj* l_lean_message__log_append(obj*, obj*);
unsigned char l_list_foldr___main___at_lean_message__log_has__errors___spec__1(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_message__log_to__list(obj*);
obj* l_lean_message_has__to__string;
obj* l_list_append___main___rarg(obj*, obj*);
obj* l_lean_message__log_has__append;
obj* l_lean_message__log_empty;
obj* l_lean_message__log_add(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_message_to__string(obj*);
obj* l_lean_message_to__string___closed__4;
obj* l_lean_message_to__string___closed__3;
obj* l_list_foldr___main___at_lean_message__log_has__errors___spec__1___boxed(obj*);
obj* l_lean_message_to__string___closed__2;
obj* l_nat_repr(obj*);
obj* l_lean_message_to__string___closed__1;
obj* l_lean_message__log_has__errors(obj*);
obj* l_lean_message_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; unsigned char x_21; obj* x_22; obj* x_24; unsigned char x_25; obj* x_26; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = l_lean_message_to__string___closed__1;
x_4 = lean::string_append(x_1, x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = l_nat_repr(x_7);
x_10 = lean::string_append(x_4, x_9);
lean::dec(x_9);
x_12 = lean::string_append(x_10, x_3);
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
x_16 = l_nat_repr(x_13);
x_17 = lean::string_append(x_12, x_16);
lean::dec(x_16);
x_19 = l_lean_message_to__string___closed__2;
x_20 = lean::string_append(x_17, x_19);
x_21 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*5);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
x_24 = l_string_join___closed__1;
x_25 = lean::string_dec_eq(x_22, x_24);
x_26 = lean::cnstr_get(x_0, 4);
lean::inc(x_26);
lean::dec(x_0);
switch (x_21) {
case 0:
{
obj* x_29; 
x_29 = lean::string_append(x_20, x_24);
if (x_25 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_30 = l_lean_message_to__string___closed__3;
x_31 = lean::string_append(x_22, x_30);
x_32 = lean::string_append(x_29, x_31);
lean::dec(x_31);
x_34 = lean::string_append(x_32, x_26);
lean::dec(x_26);
return x_34;
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_22);
x_37 = lean::string_append(x_29, x_24);
x_38 = lean::string_append(x_37, x_26);
lean::dec(x_26);
return x_38;
}
}
case 1:
{
obj* x_40; obj* x_41; 
x_40 = l_lean_message_to__string___closed__4;
x_41 = lean::string_append(x_20, x_40);
if (x_25 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; 
x_42 = l_lean_message_to__string___closed__3;
x_43 = lean::string_append(x_22, x_42);
x_44 = lean::string_append(x_41, x_43);
lean::dec(x_43);
x_46 = lean::string_append(x_44, x_26);
lean::dec(x_26);
return x_46;
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_22);
x_49 = lean::string_append(x_41, x_24);
x_50 = lean::string_append(x_49, x_26);
lean::dec(x_26);
return x_50;
}
}
default:
{
obj* x_52; obj* x_53; 
x_52 = l_lean_message_to__string___closed__5;
x_53 = lean::string_append(x_20, x_52);
if (x_25 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; 
x_54 = l_lean_message_to__string___closed__3;
x_55 = lean::string_append(x_22, x_54);
x_56 = lean::string_append(x_53, x_55);
lean::dec(x_55);
x_58 = lean::string_append(x_56, x_26);
lean::dec(x_26);
return x_58;
}
else
{
obj* x_61; obj* x_62; 
lean::dec(x_22);
x_61 = lean::string_append(x_53, x_24);
x_62 = lean::string_append(x_61, x_26);
lean::dec(x_26);
return x_62;
}
}
}
}
}
obj* _init_l_lean_message_to__string___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init_l_lean_message_to__string___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(": ");
return x_0;
}
}
obj* _init_l_lean_message_to__string___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":\n");
return x_0;
}
}
obj* _init_l_lean_message_to__string___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("warning: ");
return x_0;
}
}
obj* _init_l_lean_message_to__string___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("error: ");
return x_0;
}
}
obj* _init_l_lean_message_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_message_to__string), 1, 0);
return x_0;
}
}
obj* _init_l_lean_message__log_empty() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_message__log_add(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_message__log_append(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_append___main___rarg(x_1, x_0);
return x_2;
}
}
obj* _init_l_lean_message__log_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_message__log_append), 2, 0);
return x_0;
}
}
obj* l_lean_message__log_has__errors(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char l_list_foldr___main___at_lean_message__log_has__errors___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
unsigned char x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_5; unsigned char x_8; unsigned char x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_5);
x_9 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*5);
lean::dec(x_3);
switch (x_9) {
case 0:
{
x_0 = x_5;
goto _start;
}
case 1:
{
x_0 = x_5;
goto _start;
}
default:
{
unsigned char x_11; 
x_11 = 1;
return x_11;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_message__log_has__errors___spec__1___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_lean_message__log_to__list(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_reverse___rarg(x_0);
return x_1;
}
}
void initialize_init_data_to__string();
void initialize_init_lean_position();
static bool _G_initialized = false;
void initialize_init_lean_message() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_to__string();
 initialize_init_lean_position();
 l_lean_message_to__string___closed__1 = _init_l_lean_message_to__string___closed__1();
 l_lean_message_to__string___closed__2 = _init_l_lean_message_to__string___closed__2();
 l_lean_message_to__string___closed__3 = _init_l_lean_message_to__string___closed__3();
 l_lean_message_to__string___closed__4 = _init_l_lean_message_to__string___closed__4();
 l_lean_message_to__string___closed__5 = _init_l_lean_message_to__string___closed__5();
 l_lean_message_has__to__string = _init_l_lean_message_has__to__string();
 l_lean_message__log_empty = _init_l_lean_message__log_empty();
 l_lean_message__log_has__append = _init_l_lean_message__log_has__append();
}
