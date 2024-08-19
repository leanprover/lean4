// Lean compiler output
// Module: Lean.Data.Xml.Basic
// Imports: Lean.Data.RBMap Init.Data.ToString.Macro
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringAttributes___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2;
static lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1;
static lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringAttributes(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringContent;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2;
static lean_object* l_Lean_Xml_instToStringContent___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_instInhabitedContent;
static lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Xml_instInhabitedContent___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_instToStringElement___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringElement;
static lean_object* l_Lean_Xml_instToStringAttributes___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=\"", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(x_1, x_3);
x_8 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1;
x_9 = lean_string_append(x_8, x_4);
x_10 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_5);
x_13 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_7, x_14);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Xml_instToStringAttributes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringAttributes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_instToStringAttributes___closed__1;
x_3 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_instToStringAttributes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_instToStringAttributes(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_instInhabitedContent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_instToStringAttributes___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_instInhabitedContent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Xml_instInhabitedContent___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_string_append(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("</", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1;
x_6 = lean_string_append(x_5, x_2);
x_7 = l_Lean_Xml_instToStringAttributes___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_array_size(x_4);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1(x_9, x_10, x_4);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
x_15 = l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1(x_7, x_3);
lean_dec(x_3);
x_16 = lean_string_append(x_8, x_15);
lean_dec(x_15);
x_17 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2;
x_18 = lean_string_append(x_16, x_17);
if (x_14 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
x_19 = lean_string_append(x_18, x_7);
x_20 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_2);
lean_dec(x_2);
x_23 = lean_string_append(x_22, x_17);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_12, x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
x_25 = lean_string_append(x_18, x_7);
x_26 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_2);
lean_dec(x_2);
x_29 = lean_string_append(x_28, x_17);
return x_29;
}
else
{
size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_31 = l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2(x_11, x_10, x_30, x_7);
lean_dec(x_11);
x_32 = lean_string_append(x_18, x_31);
lean_dec(x_31);
x_33 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_2);
lean_dec(x_2);
x_36 = lean_string_append(x_35, x_17);
return x_36;
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<!--", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-->", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Xml_instToStringElement___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_instToStringElement() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Xml_instToStringElement___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_instToStringContent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_instToStringContent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Xml_instToStringContent___closed__1;
return x_1;
}
}
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Xml_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1 = _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__1);
l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2 = _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__2);
l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3 = _init_l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Xml_instToStringAttributes___spec__1___closed__3);
l_Lean_Xml_instToStringAttributes___closed__1 = _init_l_Lean_Xml_instToStringAttributes___closed__1();
lean_mark_persistent(l_Lean_Xml_instToStringAttributes___closed__1);
l_Lean_Xml_instInhabitedContent___closed__1 = _init_l_Lean_Xml_instInhabitedContent___closed__1();
lean_mark_persistent(l_Lean_Xml_instInhabitedContent___closed__1);
l_Lean_Xml_instInhabitedContent = _init_l_Lean_Xml_instInhabitedContent();
lean_mark_persistent(l_Lean_Xml_instInhabitedContent);
l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1 = _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1();
lean_mark_persistent(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__1);
l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2 = _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2();
lean_mark_persistent(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__2);
l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3 = _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3();
lean_mark_persistent(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_eToString___closed__3);
l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1 = _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1();
lean_mark_persistent(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__1);
l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2 = _init_l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2();
lean_mark_persistent(l___private_Lean_Data_Xml_Basic_0__Lean_Xml_cToString___closed__2);
l_Lean_Xml_instToStringElement___closed__1 = _init_l_Lean_Xml_instToStringElement___closed__1();
lean_mark_persistent(l_Lean_Xml_instToStringElement___closed__1);
l_Lean_Xml_instToStringElement = _init_l_Lean_Xml_instToStringElement();
lean_mark_persistent(l_Lean_Xml_instToStringElement);
l_Lean_Xml_instToStringContent___closed__1 = _init_l_Lean_Xml_instToStringContent___closed__1();
lean_mark_persistent(l_Lean_Xml_instToStringContent___closed__1);
l_Lean_Xml_instToStringContent = _init_l_Lean_Xml_instToStringContent();
lean_mark_persistent(l_Lean_Xml_instToStringContent);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
