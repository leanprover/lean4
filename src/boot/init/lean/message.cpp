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
#endif
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1_s7___boxed(obj*);
obj* _l_s4_lean_s7_message_s15_has__to__string;
obj* _l_s4_lean_s7_message_s10_to__string_s11___closed__5;
obj* _l_s4_lean_s7_message_s10_to__string(obj*);
obj* _l_s4_lean_s12_message__log_s8_to__list(obj*);
unsigned char _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1(obj*);
obj* _l_s4_lean_s12_message__log_s11_has__append;
obj* _l_s4_lean_s12_message__log_s11_has__errors(obj*);
obj* _l_s4_lean_s12_message__log_s3_add(obj*, obj*);
obj* _l_s4_lean_s7_message_s10_to__string_s11___closed__4;
obj* _l_s4_list_s7_reverse_s6___rarg(obj*);
extern obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s4_lean_s12_message__log_s6_append(obj*, obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_list_s6_append_s6___main_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s7_message_s10_to__string_s11___closed__3;
obj* _l_s4_lean_s7_message_s10_to__string_s11___closed__1;
obj* _l_s4_lean_s7_message_s10_to__string_s11___closed__2;
obj* _l_s4_lean_s12_message__log_s5_empty;
obj* _l_s4_lean_s7_message_s10_to__string(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; unsigned char x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = _l_s4_lean_s7_message_s10_to__string_s11___closed__1;
x_4 = lean::string_append(x_1, x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = _l_s3_nat_s4_repr(x_7);
x_10 = lean::string_append(x_4, x_9);
lean::dec(x_9);
x_12 = lean::string_append(x_10, x_3);
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
x_16 = _l_s3_nat_s4_repr(x_13);
x_17 = lean::string_append(x_12, x_16);
lean::dec(x_16);
x_19 = _l_s4_lean_s7_message_s10_to__string_s11___closed__2;
x_20 = lean::string_append(x_17, x_19);
x_21 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*5);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
x_24 = _l_s6_string_s4_join_s11___closed__1;
x_25 = lean::string_dec_eq(x_22, x_24);
x_26 = lean::cnstr_get(x_0, 4);
lean::inc(x_26);
lean::dec(x_0);
switch (x_21) {
case 0:
{
obj* x_29; 
x_29 = lean::string_append(x_20, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_36; 
lean::dec(x_24);
lean::dec(x_25);
x_32 = _l_s4_lean_s7_message_s10_to__string_s11___closed__3;
x_33 = lean::string_append(x_22, x_32);
x_34 = lean::string_append(x_29, x_33);
lean::dec(x_33);
x_36 = lean::string_append(x_34, x_26);
lean::dec(x_26);
return x_36;
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_22);
lean::dec(x_25);
x_40 = lean::string_append(x_29, x_24);
x_41 = lean::string_append(x_40, x_26);
lean::dec(x_26);
return x_41;
}
}
case 1:
{
obj* x_43; obj* x_44; 
x_43 = _l_s4_lean_s7_message_s10_to__string_s11___closed__4;
x_44 = lean::string_append(x_20, x_43);
if (lean::obj_tag(x_25) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_24);
lean::dec(x_25);
x_47 = _l_s4_lean_s7_message_s10_to__string_s11___closed__3;
x_48 = lean::string_append(x_22, x_47);
x_49 = lean::string_append(x_44, x_48);
lean::dec(x_48);
x_51 = lean::string_append(x_49, x_26);
lean::dec(x_26);
return x_51;
}
else
{
obj* x_55; obj* x_56; 
lean::dec(x_22);
lean::dec(x_25);
x_55 = lean::string_append(x_44, x_24);
x_56 = lean::string_append(x_55, x_26);
lean::dec(x_26);
return x_56;
}
}
default:
{
obj* x_58; obj* x_59; 
x_58 = _l_s4_lean_s7_message_s10_to__string_s11___closed__5;
x_59 = lean::string_append(x_20, x_58);
if (lean::obj_tag(x_25) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_24);
lean::dec(x_25);
x_62 = _l_s4_lean_s7_message_s10_to__string_s11___closed__3;
x_63 = lean::string_append(x_22, x_62);
x_64 = lean::string_append(x_59, x_63);
lean::dec(x_63);
x_66 = lean::string_append(x_64, x_26);
lean::dec(x_26);
return x_66;
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_22);
lean::dec(x_25);
x_70 = lean::string_append(x_59, x_24);
x_71 = lean::string_append(x_70, x_26);
lean::dec(x_26);
return x_71;
}
}
}
}
}
obj* _init__l_s4_lean_s7_message_s10_to__string_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init__l_s4_lean_s7_message_s10_to__string_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(": ");
return x_0;
}
}
obj* _init__l_s4_lean_s7_message_s10_to__string_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(":\n");
return x_0;
}
}
obj* _init__l_s4_lean_s7_message_s10_to__string_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("warning: ");
return x_0;
}
}
obj* _init__l_s4_lean_s7_message_s10_to__string_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("error: ");
return x_0;
}
}
obj* _init__l_s4_lean_s7_message_s15_has__to__string() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s7_message_s10_to__string), 1, 0);
return x_0;
}
}
obj* _init__l_s4_lean_s12_message__log_s5_empty() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s4_lean_s12_message__log_s3_add(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s4_lean_s12_message__log_s6_append(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s4_list_s6_append_s6___main_s6___rarg(x_1, x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s12_message__log_s11_has__append() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s12_message__log_s6_append), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s12_message__log_s11_has__errors(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1(obj* x_0) {
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
x_8 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1(x_5);
x_9 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*5);
lean::dec(x_3);
switch (x_9) {
case 0:
{

return x_8;
}
case 1:
{

return x_8;
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
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s12_message__log_s11_has__errors_s9___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _l_s4_lean_s12_message__log_s8_to__list(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_list_s7_reverse_s6___rarg(x_0);
return x_1;
}
}
void _l_initialize__l_s4_init_s4_data_s10_to__string();
void _l_initialize__l_s4_init_s4_lean_s8_position();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s7_message() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s10_to__string();
 _l_initialize__l_s4_init_s4_lean_s8_position();
 _l_s4_lean_s7_message_s10_to__string_s11___closed__1 = _init__l_s4_lean_s7_message_s10_to__string_s11___closed__1();
 _l_s4_lean_s7_message_s10_to__string_s11___closed__2 = _init__l_s4_lean_s7_message_s10_to__string_s11___closed__2();
 _l_s4_lean_s7_message_s10_to__string_s11___closed__3 = _init__l_s4_lean_s7_message_s10_to__string_s11___closed__3();
 _l_s4_lean_s7_message_s10_to__string_s11___closed__4 = _init__l_s4_lean_s7_message_s10_to__string_s11___closed__4();
 _l_s4_lean_s7_message_s10_to__string_s11___closed__5 = _init__l_s4_lean_s7_message_s10_to__string_s11___closed__5();
 _l_s4_lean_s7_message_s15_has__to__string = _init__l_s4_lean_s7_message_s15_has__to__string();
 _l_s4_lean_s12_message__log_s5_empty = _init__l_s4_lean_s12_message__log_s5_empty();
 _l_s4_lean_s12_message__log_s11_has__append = _init__l_s4_lean_s12_message__log_s11_has__append();
}
