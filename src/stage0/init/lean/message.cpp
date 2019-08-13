// Lean compiler output
// Module: init.lean.message
// Imports: init.data.tostring init.lean.position
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
obj* l_Lean_mkErrorStringWithPos(obj*, obj*, obj*, obj*);
obj* l_Lean_MessageLog_empty;
obj* l_Lean_Message_toString___closed__2;
obj* l_Lean_Message_toString___closed__1;
obj* l_Lean_mkErrorStringWithPos___closed__1;
obj* l_Lean_Message_Inhabited___closed__2;
obj* l_Lean_MessageLog_append(obj*, obj*);
extern obj* l_EState_Result_toString___rarg___closed__2;
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_MessageLog_toList(obj*);
obj* l_Lean_Message_toString___closed__3;
obj* l_Lean_Message_HasToString;
obj* l_Lean_Message_Inhabited;
obj* l_Nat_repr(obj*);
obj* l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1___boxed(obj*, obj*);
uint8 l_Lean_MessageLog_hasErrors(obj*);
uint8 l_Lean_MessageLog_isEmpty(obj*);
obj* l_Lean_Message_toString___closed__4;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_append___rarg(obj*, obj*);
uint8 l_List_isEmpty___rarg(obj*);
extern obj* l_Lean_Format_flatten___main___closed__1;
obj* l_Lean_Message_HasToString___closed__1;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_mkErrorStringWithPos___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_MessageLog_HasAppend___closed__1;
obj* l_Lean_MessageLog_add(obj*, obj*);
obj* l_Lean_Message_toString(obj*);
obj* l_Lean_MessageLog_HasAppend;
obj* l_Lean_MessageLog_isEmpty___boxed(obj*);
obj* l_Lean_MessageLog_hasErrors___boxed(obj*);
obj* l_Lean_MessageLog_Inhabited;
uint8 l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Message_Inhabited___closed__1;
obj* l_Lean_Message_toString___closed__5;
obj* _init_l_Lean_mkErrorStringWithPos___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(":");
return x_1;
}
}
obj* l_Lean_mkErrorStringWithPos(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_Lean_mkErrorStringWithPos___closed__1;
x_6 = lean::string_append(x_1, x_5);
x_7 = l_Nat_repr(x_2);
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
x_9 = lean::string_append(x_8, x_5);
x_10 = l_Nat_repr(x_3);
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
x_12 = l_Lean_Format_flatten___main___closed__1;
x_13 = lean::string_append(x_11, x_12);
x_14 = lean::string_append(x_13, x_4);
return x_14;
}
}
obj* l_Lean_mkErrorStringWithPos___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* _init_l_Lean_Message_toString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(":\n");
return x_1;
}
}
obj* _init_l_Lean_Message_toString___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::string_append(x_1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Message_toString___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("warning: ");
return x_1;
}
}
obj* _init_l_Lean_Message_toString___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Message_toString___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Message_toString___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_EState_Result_toString___rarg___closed__2;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Message_toString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
x_8 = l_String_splitAux___main___closed__1;
x_9 = lean::string_dec_eq(x_7, x_8);
switch (x_6) {
case 0:
{
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
lean::dec(x_1);
x_11 = l_Lean_Message_toString___closed__1;
x_12 = lean::string_append(x_7, x_11);
x_13 = lean::string_append(x_8, x_12);
lean::dec(x_12);
x_14 = lean::string_append(x_13, x_10);
lean::dec(x_10);
x_15 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_14);
lean::dec(x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_7);
x_16 = lean::cnstr_get(x_1, 4);
lean::inc(x_16);
lean::dec(x_1);
x_17 = l_Lean_Message_toString___closed__2;
x_18 = lean::string_append(x_17, x_16);
lean::dec(x_16);
x_19 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_18);
lean::dec(x_18);
return x_19;
}
}
case 1:
{
if (x_9 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_1, 4);
lean::inc(x_20);
lean::dec(x_1);
x_21 = l_Lean_Message_toString___closed__1;
x_22 = lean::string_append(x_7, x_21);
x_23 = l_Lean_Message_toString___closed__3;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_25 = lean::string_append(x_24, x_20);
lean::dec(x_20);
x_26 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_25);
lean::dec(x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_7);
x_27 = lean::cnstr_get(x_1, 4);
lean::inc(x_27);
lean::dec(x_1);
x_28 = l_Lean_Message_toString___closed__4;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_30 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_29);
lean::dec(x_29);
return x_30;
}
}
default: 
{
if (x_9 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_1, 4);
lean::inc(x_31);
lean::dec(x_1);
x_32 = l_Lean_Message_toString___closed__1;
x_33 = lean::string_append(x_7, x_32);
x_34 = l_EState_Result_toString___rarg___closed__2;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_36 = lean::string_append(x_35, x_31);
lean::dec(x_31);
x_37 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_36);
lean::dec(x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_7);
x_38 = lean::cnstr_get(x_1, 4);
lean::inc(x_38);
lean::dec(x_1);
x_39 = l_Lean_Message_toString___closed__5;
x_40 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_41 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_40);
lean::dec(x_40);
return x_41;
}
}
}
}
}
obj* _init_l_Lean_Message_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Message_Inhabited___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Message_Inhabited___closed__1;
x_4 = 2;
x_5 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_1);
lean::cnstr_set(x_5, 3, x_2);
lean::cnstr_set(x_5, 4, x_2);
lean::cnstr_set_scalar(x_5, sizeof(void*)*5, x_4);
return x_5;
}
}
obj* _init_l_Lean_Message_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Message_Inhabited___closed__2;
return x_1;
}
}
obj* _init_l_Lean_Message_HasToString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Message_toString), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Message_HasToString() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Message_HasToString___closed__1;
return x_1;
}
}
obj* _init_l_Lean_MessageLog_empty() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
uint8 l_Lean_MessageLog_isEmpty(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_List_isEmpty___rarg(x_1);
return x_2;
}
}
obj* l_Lean_MessageLog_isEmpty___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_MessageLog_isEmpty(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_MessageLog_Inhabited() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_MessageLog_add(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_MessageLog_append(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_append___rarg(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_MessageLog_HasAppend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_MessageLog_append), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_MessageLog_HasAppend() {
_start:
{
obj* x_1; 
x_1 = l_Lean_MessageLog_HasAppend___closed__1;
return x_1;
}
}
uint8 l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; uint8 x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_1, x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*5);
x_7 = lean::box(x_6);
if (lean::obj_tag(x_7) == 2)
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
else
{
lean::dec(x_7);
return x_5;
}
}
}
}
uint8 l_Lean_MessageLog_hasErrors(obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; 
x_2 = 0;
x_3 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_3, x_2);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_MessageLog_hasErrors___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_MessageLog_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_reverse___rarg(x_1);
return x_2;
}
}
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_lean_position(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_message(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_position(w);
if (io_result_is_error(w)) return w;
l_Lean_mkErrorStringWithPos___closed__1 = _init_l_Lean_mkErrorStringWithPos___closed__1();
lean::mark_persistent(l_Lean_mkErrorStringWithPos___closed__1);
l_Lean_Message_toString___closed__1 = _init_l_Lean_Message_toString___closed__1();
lean::mark_persistent(l_Lean_Message_toString___closed__1);
l_Lean_Message_toString___closed__2 = _init_l_Lean_Message_toString___closed__2();
lean::mark_persistent(l_Lean_Message_toString___closed__2);
l_Lean_Message_toString___closed__3 = _init_l_Lean_Message_toString___closed__3();
lean::mark_persistent(l_Lean_Message_toString___closed__3);
l_Lean_Message_toString___closed__4 = _init_l_Lean_Message_toString___closed__4();
lean::mark_persistent(l_Lean_Message_toString___closed__4);
l_Lean_Message_toString___closed__5 = _init_l_Lean_Message_toString___closed__5();
lean::mark_persistent(l_Lean_Message_toString___closed__5);
l_Lean_Message_Inhabited___closed__1 = _init_l_Lean_Message_Inhabited___closed__1();
lean::mark_persistent(l_Lean_Message_Inhabited___closed__1);
l_Lean_Message_Inhabited___closed__2 = _init_l_Lean_Message_Inhabited___closed__2();
lean::mark_persistent(l_Lean_Message_Inhabited___closed__2);
l_Lean_Message_Inhabited = _init_l_Lean_Message_Inhabited();
lean::mark_persistent(l_Lean_Message_Inhabited);
l_Lean_Message_HasToString___closed__1 = _init_l_Lean_Message_HasToString___closed__1();
lean::mark_persistent(l_Lean_Message_HasToString___closed__1);
l_Lean_Message_HasToString = _init_l_Lean_Message_HasToString();
lean::mark_persistent(l_Lean_Message_HasToString);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean::mark_persistent(l_Lean_MessageLog_empty);
l_Lean_MessageLog_Inhabited = _init_l_Lean_MessageLog_Inhabited();
lean::mark_persistent(l_Lean_MessageLog_Inhabited);
l_Lean_MessageLog_HasAppend___closed__1 = _init_l_Lean_MessageLog_HasAppend___closed__1();
lean::mark_persistent(l_Lean_MessageLog_HasAppend___closed__1);
l_Lean_MessageLog_HasAppend = _init_l_Lean_MessageLog_HasAppend();
lean::mark_persistent(l_Lean_MessageLog_HasAppend);
return w;
}
