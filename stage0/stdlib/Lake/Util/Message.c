// Lean compiler output
// Module: Lake.Util.Message
// Imports: public import Lean.Parser.Basic
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
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
static lean_object* l_Lake_mkMessageStringCore___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
static lean_object* l_Lake_mkMessageStringCore___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_mkMessageStringCore___closed__2;
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_mkParserErrorMessage___closed__0;
static lean_object* l_Lake_mkMessageStringCore___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_mkMessageStringCore___closed__4;
static lean_object* _init_l_Lake_mkParserErrorMessage___closed__0() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_FileMap_toPosition(x_5, x_6);
x_8 = lean_box(0);
x_9 = 1;
x_10 = 2;
x_11 = 0;
x_12 = l_Lake_mkParserErrorMessage___closed__0;
x_13 = l_Lean_Parser_Error_toString(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkParserErrorMessage(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; lean_object* x_25; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Exception_getRef(x_2);
x_6 = 0;
x_25 = l_Lean_Syntax_getPos_x3f(x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(0u);
x_14 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec_ref(x_25);
x_14 = x_27;
goto block_24;
}
block_13:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 2;
x_10 = l_Lake_mkParserErrorMessage___closed__0;
x_11 = l_Lean_Exception_toMessageData(x_2);
x_12 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 2, x_6);
return x_12;
}
block_24:
{
lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_4);
x_15 = l_Lean_FileMap_toPosition(x_4, x_14);
lean_dec(x_14);
x_16 = l_Lean_Syntax_getTailPos_x3f(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_4);
x_17 = lean_box(0);
x_7 = x_15;
x_8 = x_17;
goto block_13;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_FileMap_toPosition(x_4, x_19);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_20);
x_7 = x_15;
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_FileMap_toPosition(x_4, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_7 = x_15;
x_8 = x_23;
goto block_13;
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
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_FileMap_toPosition(x_5, x_6);
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Lake_mkParserErrorMessage___closed__0;
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
x_5 = l_Lake_mkMessageNoPos(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_mkMessageStringCore___closed__4() {
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
lean_object* x_8; lean_object* x_12; uint8_t x_13; uint8_t x_15; lean_object* x_16; uint32_t x_17; lean_object* x_21; lean_object* x_34; lean_object* x_48; uint8_t x_49; 
x_48 = l_Lake_mkParserErrorMessage___closed__0;
x_49 = lean_string_dec_eq(x_3, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l_Lake_mkMessageStringCore___closed__4;
x_51 = lean_string_append(x_3, x_50);
x_52 = lean_string_append(x_51, x_4);
lean_dec_ref(x_4);
x_34 = x_52;
goto block_47;
}
else
{
lean_dec_ref(x_3);
x_34 = x_4;
goto block_47;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lake_mkMessageStringCore___closed__0;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
block_14:
{
if (x_13 == 0)
{
return x_12;
}
else
{
x_8 = x_12;
goto block_11;
}
}
block_20:
{
uint32_t x_18; uint8_t x_19; 
x_18 = 10;
x_19 = lean_uint32_dec_eq(x_17, x_18);
if (x_19 == 0)
{
x_8 = x_16;
goto block_11;
}
else
{
x_12 = x_16;
x_13 = x_15;
goto block_14;
}
}
block_33:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_string_utf8_byte_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_21);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
x_26 = l_String_Slice_Pos_prev_x3f(x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint32_t x_27; 
lean_dec_ref(x_25);
x_27 = 65;
x_15 = x_24;
x_16 = x_21;
x_17 = x_27;
goto block_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_String_Slice_Pos_get_x3f(x_25, x_28);
lean_dec(x_28);
lean_dec_ref(x_25);
if (lean_obj_tag(x_29) == 0)
{
uint32_t x_30; 
x_30 = 65;
x_15 = x_24;
x_16 = x_21;
x_17 = x_30;
goto block_20;
}
else
{
lean_object* x_31; uint32_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_15 = x_24;
x_16 = x_21;
x_17 = x_32;
goto block_20;
}
}
}
else
{
x_12 = x_21;
x_13 = x_24;
goto block_14;
}
}
block_47:
{
switch (x_1) {
case 0:
{
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_21 = x_34;
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lake_mkMessageStringCore___closed__1;
x_36 = lean_box(0);
x_37 = l_Lean_mkErrorStringWithPos(x_2, x_5, x_35, x_6, x_36, x_36);
x_38 = lean_string_append(x_37, x_34);
lean_dec_ref(x_34);
x_21 = x_38;
goto block_33;
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lake_mkMessageStringCore___closed__2;
x_40 = lean_box(0);
x_41 = l_Lean_mkErrorStringWithPos(x_2, x_5, x_39, x_6, x_40, x_40);
x_42 = lean_string_append(x_41, x_34);
lean_dec_ref(x_34);
x_21 = x_42;
goto block_33;
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lake_mkMessageStringCore___closed__3;
x_44 = lean_box(0);
x_45 = l_Lean_mkErrorStringWithPos(x_2, x_5, x_43, x_6, x_44, x_44);
x_46 = lean_string_append(x_45, x_34);
lean_dec_ref(x_34);
x_21 = x_46;
goto block_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox(x_7);
x_10 = l_Lake_mkMessageStringCore(x_8, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_5; 
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
x_5 = x_14;
goto block_13;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_5 = x_15;
goto block_13;
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_9 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = l_Lean_MessageData_toString(x_10);
x_12 = l_Lake_mkMessageStringCore(x_8, x_6, x_9, x_11, x_7, x_5, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_mkMessageString(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = 0;
x_7 = 1;
x_8 = l_Lake_mkMessageString(x_4, x_6, x_7);
x_9 = lean_string_append(x_1, x_8);
lean_dec_ref(x_8);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkParserErrorMessage___closed__0;
x_4 = l_Lean_MessageLog_toList(x_1);
x_5 = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mkMessageLogString(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkParserErrorMessage___closed__0 = _init_l_Lake_mkParserErrorMessage___closed__0();
lean_mark_persistent(l_Lake_mkParserErrorMessage___closed__0);
l_Lake_mkMessageStringCore___closed__0 = _init_l_Lake_mkMessageStringCore___closed__0();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__0);
l_Lake_mkMessageStringCore___closed__1 = _init_l_Lake_mkMessageStringCore___closed__1();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__1);
l_Lake_mkMessageStringCore___closed__2 = _init_l_Lake_mkMessageStringCore___closed__2();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__2);
l_Lake_mkMessageStringCore___closed__3 = _init_l_Lake_mkMessageStringCore___closed__3();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__3);
l_Lake_mkMessageStringCore___closed__4 = _init_l_Lake_mkMessageStringCore___closed__4();
lean_mark_persistent(l_Lake_mkMessageStringCore___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
