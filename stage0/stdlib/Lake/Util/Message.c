// Lean compiler output
// Module: Lake.Util.Message
// Imports: Lean.Message Lean.Exception Lean.Parser.Basic
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
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
static lean_object* l_Lake_mkMessageStringCore___closed__1;
static lean_object* l_Lake_mkMessageStringCore___lambda__2___closed__1;
static lean_object* l_Lake_mkMessageStringCore___lambda__3___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_mkMessageLogString___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkParserErrorMessage___closed__1;
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
static lean_object* l_Lake_mkMessageStringCore___lambda__3___closed__2;
static lean_object* l_Lake_mkMessageStringCore___lambda__3___closed__4;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_mkMessageStringCore___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_mkMessageStringCore___lambda__3___closed__3;
static lean_object* _init_l_Lake_mkParserErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_FileMap_toPosition(x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_Error_toString(x_3);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = 1;
x_13 = 2;
x_14 = 0;
x_15 = l_Lake_mkParserErrorMessage___closed__1;
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkParserErrorMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Exception_getRef(x_2);
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_5, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_5, x_6);
lean_dec(x_5);
x_9 = l_Lean_Exception_toMessageData(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_11 = l_Lean_FileMap_toPosition(x_4, x_10);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = 2;
x_14 = l_Lake_mkParserErrorMessage___closed__1;
x_15 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 2, x_6);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = l_Lean_FileMap_toPosition(x_4, x_17);
lean_dec(x_17);
lean_ctor_set(x_8, 0, x_18);
x_19 = 2;
x_20 = l_Lake_mkParserErrorMessage___closed__1;
x_21 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_8);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 2, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_FileMap_toPosition(x_4, x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = 2;
x_26 = l_Lake_mkParserErrorMessage___closed__1;
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_9);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_6);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_4);
x_29 = l_Lean_FileMap_toPosition(x_4, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = 2;
x_32 = l_Lake_mkParserErrorMessage___closed__1;
x_33 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_9);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 2, x_6);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = l_Lean_FileMap_toPosition(x_4, x_35);
lean_dec(x_35);
lean_ctor_set(x_8, 0, x_36);
x_37 = 2;
x_38 = l_Lake_mkParserErrorMessage___closed__1;
x_39 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_8);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_9);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 1, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 2, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
lean_dec(x_8);
x_41 = l_Lean_FileMap_toPosition(x_4, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = 2;
x_44 = l_Lake_mkParserErrorMessage___closed__1;
x_45 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_9);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 2, x_6);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_FileMap_toPosition(x_5, x_6);
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Lake_mkParserErrorMessage___closed__1;
x_11 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lake_mkMessageNoPos(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_mkMessageStringCore___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_mkMessageStringCore___lambda__2___closed__1;
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_string_utf8_prev(x_1, x_4);
lean_dec(x_4);
x_8 = lean_string_utf8_get(x_1, x_7);
lean_dec(x_7);
x_9 = 10;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lake_mkMessageStringCore___lambda__2___closed__2;
x_12 = lean_string_append(x_1, x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_3, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_2(x_3, x_1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_17 = l_Lake_mkMessageStringCore___lambda__2___closed__2;
x_18 = lean_string_append(x_1, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_3, x_18, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_mkMessageStringCore___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error: ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_mkMessageStringCore___lambda__3___closed__1;
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lake_mkMessageStringCore___lambda__3___closed__2;
x_12 = l_Lean_mkErrorStringWithPos(x_3, x_4, x_11, x_5);
x_13 = lean_string_append(x_12, x_6);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_8, x_13, x_14);
return x_15;
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lake_mkMessageStringCore___lambda__3___closed__3;
x_17 = l_Lean_mkErrorStringWithPos(x_3, x_4, x_16, x_5);
x_18 = lean_string_append(x_17, x_6);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_8, x_18, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lake_mkMessageStringCore___lambda__3___closed__4;
x_22 = l_Lean_mkErrorStringWithPos(x_3, x_4, x_21, x_5);
x_23 = lean_string_append(x_22, x_6);
lean_dec(x_6);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_8, x_23, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_mkParserErrorMessage___closed__1;
x_9 = lean_string_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_mkMessageStringCore___closed__1;
x_11 = lean_string_append(x_3, x_10);
x_12 = lean_string_append(x_11, x_4);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = l_Lake_mkMessageStringCore___lambda__3(x_1, x_7, x_2, x_5, x_6, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = l_Lake_mkMessageStringCore___lambda__3(x_1, x_7, x_2, x_5, x_6, x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkMessageStringCore___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkMessageStringCore___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_mkMessageStringCore___lambda__3(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lake_mkMessageStringCore(x_8, x_2, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = l_Lean_MessageData_toString(x_5, x_4);
if (x_2 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lake_mkMessageStringCore(x_10, x_11, x_12, x_8, x_13, x_9, x_3);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lake_mkMessageStringCore(x_18, x_19, x_20, x_15, x_21, x_17, x_3);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lake_mkMessageStringCore(x_31, x_32, x_33, x_29, x_34, x_30, x_3);
lean_dec(x_32);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lake_mkMessageStringCore(x_39, x_40, x_41, x_36, x_42, x_38, x_3);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
return x_6;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_mkMessageString(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_mkMessageLogString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = 0;
x_8 = 1;
x_9 = l_Lake_mkMessageString(x_5, x_7, x_8, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_append(x_1, x_10);
lean_dec(x_10);
x_1 = x_12;
x_2 = x_6;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_MessageLog_toList(x_1);
x_4 = l_Lake_mkParserErrorMessage___closed__1;
x_5 = l_List_foldlM___at_Lake_mkMessageLogString___spec__1(x_4, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkMessageLogString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkParserErrorMessage___closed__1 = _init_l_Lake_mkParserErrorMessage___closed__1();
lean_mark_persistent(l_Lake_mkParserErrorMessage___closed__1);
l_Lake_mkMessageStringCore___lambda__2___closed__1 = _init_l_Lake_mkMessageStringCore___lambda__2___closed__1();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__2___closed__1);
l_Lake_mkMessageStringCore___lambda__2___closed__2 = _init_l_Lake_mkMessageStringCore___lambda__2___closed__2();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__2___closed__2);
l_Lake_mkMessageStringCore___lambda__3___closed__1 = _init_l_Lake_mkMessageStringCore___lambda__3___closed__1();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__3___closed__1);
l_Lake_mkMessageStringCore___lambda__3___closed__2 = _init_l_Lake_mkMessageStringCore___lambda__3___closed__2();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__3___closed__2);
l_Lake_mkMessageStringCore___lambda__3___closed__3 = _init_l_Lake_mkMessageStringCore___lambda__3___closed__3();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__3___closed__3);
l_Lake_mkMessageStringCore___lambda__3___closed__4 = _init_l_Lake_mkMessageStringCore___lambda__3___closed__4();
lean_mark_persistent(l_Lake_mkMessageStringCore___lambda__3___closed__4);
l_Lake_mkMessageStringCore___closed__1 = _init_l_Lake_mkMessageStringCore___closed__1();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
