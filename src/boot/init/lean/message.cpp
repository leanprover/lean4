// Lean compiler output
// Module: init.lean.message
// Imports: init.data.to_string init.lean.position
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
obj* l_lean_message__log_has__errors___boxed(obj*);
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_message_to__string___closed__5;
obj* l_lean_message__log_append(obj*, obj*);
uint8 l_list_foldr___main___at_lean_message__log_has__errors___spec__1(uint8, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_message__log_to__list(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_message_has__to__string;
obj* l_lean_message__log_has__append;
obj* l_lean_message__log_empty;
obj* l_lean_message__log_add(obj*, obj*);
obj* l_lean_message_to__string(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_message_to__string___closed__4;
obj* l_lean_message_to__string___closed__3;
obj* l_list_foldr___main___at_lean_message__log_has__errors___spec__1___boxed(obj*, obj*);
obj* l_lean_message_to__string___closed__2;
obj* l_nat_repr(obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_message_to__string___closed__1;
uint8 l_lean_message__log_has__errors(obj*);
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
obj* l_lean_message_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_24; uint8 x_25; 
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
x_21 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
x_24 = l_string_iterator_extract___main___closed__1;
x_25 = lean::string_dec_eq(x_22, x_24);
switch (x_21) {
case 0:
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_0, 4);
lean::inc(x_26);
lean::dec(x_0);
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
obj* x_40; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_0, 4);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l_lean_message_to__string___closed__4;
x_44 = lean::string_append(x_20, x_43);
if (x_25 == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_49; 
x_45 = l_lean_message_to__string___closed__3;
x_46 = lean::string_append(x_22, x_45);
x_47 = lean::string_append(x_44, x_46);
lean::dec(x_46);
x_49 = lean::string_append(x_47, x_40);
lean::dec(x_40);
return x_49;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_22);
x_52 = lean::string_append(x_44, x_24);
x_53 = lean::string_append(x_52, x_40);
lean::dec(x_40);
return x_53;
}
}
default:
{
obj* x_55; obj* x_58; obj* x_59; 
x_55 = lean::cnstr_get(x_0, 4);
lean::inc(x_55);
lean::dec(x_0);
x_58 = l_lean_message_to__string___closed__5;
x_59 = lean::string_append(x_20, x_58);
if (x_25 == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_64; 
x_60 = l_lean_message_to__string___closed__3;
x_61 = lean::string_append(x_22, x_60);
x_62 = lean::string_append(x_59, x_61);
lean::dec(x_61);
x_64 = lean::string_append(x_62, x_55);
lean::dec(x_55);
return x_64;
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_22);
x_67 = lean::string_append(x_59, x_24);
x_68 = lean::string_append(x_67, x_55);
lean::dec(x_55);
return x_68;
}
}
}
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
x_2 = l_list_append___rarg(x_1, x_0);
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
uint8 l_list_foldr___main___at_lean_message__log_has__errors___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_0, x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
switch (x_5) {
case 2:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
default:
{
return x_4;
}
}
}
}
}
uint8 l_lean_message__log_has__errors(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; 
x_1 = 0;
x_2 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_list_foldr___main___at_lean_message__log_has__errors___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_list_foldr___main___at_lean_message__log_has__errors___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_message__log_has__errors___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_message__log_has__errors(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
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
lean::mark_persistent(l_lean_message_to__string___closed__1);
 l_lean_message_to__string___closed__2 = _init_l_lean_message_to__string___closed__2();
lean::mark_persistent(l_lean_message_to__string___closed__2);
 l_lean_message_to__string___closed__3 = _init_l_lean_message_to__string___closed__3();
lean::mark_persistent(l_lean_message_to__string___closed__3);
 l_lean_message_to__string___closed__4 = _init_l_lean_message_to__string___closed__4();
lean::mark_persistent(l_lean_message_to__string___closed__4);
 l_lean_message_to__string___closed__5 = _init_l_lean_message_to__string___closed__5();
lean::mark_persistent(l_lean_message_to__string___closed__5);
 l_lean_message_has__to__string = _init_l_lean_message_has__to__string();
lean::mark_persistent(l_lean_message_has__to__string);
 l_lean_message__log_empty = _init_l_lean_message__log_empty();
lean::mark_persistent(l_lean_message__log_empty);
 l_lean_message__log_has__append = _init_l_lean_message__log_has__append();
lean::mark_persistent(l_lean_message__log_has__append);
}
