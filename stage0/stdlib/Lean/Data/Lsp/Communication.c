// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: Init.System.IO Lean.Data.JsonRpc
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__12;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__49;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__57;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__10;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__30;
static lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
lean_object* l_String_toNat_x3f(lean_object*);
static lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
static lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__8;
lean_object* l_String_quote(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__50;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__39;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__20;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
static lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__11;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__48;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__19;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__15;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__24;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__25;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__7;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__14;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__42;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__38;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__53;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__45;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__58;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__35;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__21;
static lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
static lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__4;
static lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
static lean_object* l_IO_FS_Stream_readLspMessage___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__40;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__52;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__3;
static lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__55;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__43;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__5;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__36;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__29;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__16;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__26;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__18;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__59;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__37;
static uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__44;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__2;
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__41;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__23;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__56;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__34;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__27;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__46;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__22;
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__32;
lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__17;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__60;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__33;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__31;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__47;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__51;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__61;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__28;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__54;
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
x_3 = lean_string_dec_eq(x_1, x_2);
x_4 = l_instDecidableNot___redArg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_1);
lean_inc(x_8);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_inc(x_8);
x_10 = l_Substring_prevn(x_9, x_6, x_8);
lean_dec(x_9);
x_11 = lean_string_utf8_extract(x_1, x_10, x_8);
lean_dec(x_8);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
x_16 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_extract(x_1, x_7, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_String_splitOnAux(x_17, x_15, x_7, x_7, x_7, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_21);
x_24 = l_String_intercalate(x_15, x_21);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 1, x_24);
lean_ctor_set(x_21, 0, x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_1);
x_31 = lean_box(0);
return x_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seq_num", 7, 7);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
lean_inc(x_5);
x_7 = l_Lean_Json_getObjVal_x3f(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
x_11 = l_Lean_Json_getObjVal_x3f(x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid header field: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 ", 175, 175);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Stream was closed", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_apply_1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_12 = lean_string_dec_eq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
lean_inc(x_6);
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
x_16 = l_String_quote(x_6);
lean_dec(x_6);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(120u);
x_19 = lean_format_pretty(x_17, x_18, x_9, x_9);
x_20 = lean_string_append(x_15, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; 
lean_dec(x_6);
x_22 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_4);
lean_dec(x_6);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_7);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_dec(x_23);
return x_24;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
}
else
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_1);
x_33 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_string_utf8_byte_size(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_40 = lean_string_dec_eq(x_34, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_34);
x_41 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_34);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
lean_inc(x_34);
x_42 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_34);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
x_44 = l_String_quote(x_34);
lean_dec(x_34);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_unsigned_to_nat(120u);
x_47 = lean_format_pretty(x_45, x_46, x_37, x_37);
x_48 = lean_string_append(x_43, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_35);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_34);
x_51 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_35);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_dec(x_53);
return x_54;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_34);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_35);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_34);
lean_dec(x_1);
x_62 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_35);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
return x_4;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_4);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_dec_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_8 = lean_string_append(x_1, x_7);
x_9 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_string_append(x_10, x_7);
x_12 = lean_string_append(x_11, x_6);
x_13 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_8, x_14);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
x_8 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_9 = lean_string_append(x_8, x_5);
x_10 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
x_13 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_7, x_14);
lean_dec(x_14);
x_16 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
x_22 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_23 = lean_string_append(x_22, x_19);
x_24 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_20);
x_27 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_21, x_28);
lean_dec(x_28);
x_30 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_29, x_3);
x_31 = 93;
x_32 = lean_string_push(x_30, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No Content-Length field in header: ", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length header field value '", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a Nat", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
x_7 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_9 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_5);
lean_dec(x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = l_String_toNat_x3f(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_16 = lean_string_append(x_15, x_13);
lean_dec(x_13);
x_17 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_18 = lean_string_append(x_16, x_17);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_19; 
lean_free_object(x_7);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = l_String_toNat_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_23 = lean_string_append(x_22, x_20);
lean_dec(x_20);
x_24 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
else
{
lean_object* x_27; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_30 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
x_31 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_30, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_33 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_28);
lean_dec(x_28);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
x_39 = l_String_toNat_x3f(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_41 = lean_string_append(x_40, x_37);
lean_dec(x_37);
x_42 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_43 = lean_string_append(x_41, x_42);
if (lean_is_scalar(x_38)) {
 x_44 = lean_alloc_ctor(18, 1, 0);
} else {
 x_44 = x_38;
 lean_ctor_set_tag(x_44, 18);
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
lean_dec(x_37);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_29);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readLspMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot read LSP message: ", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_IO_FS_Stream_readMessage(x_1, x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_15;
x_4 = x_16;
goto block_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_3 = x_17;
x_4 = x_18;
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_IO_FS_Stream_readLspMessage___closed__0;
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspRequestAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot read LSP request: ", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot read LSP notification: ", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_readLspResponseAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot read LSP response: ", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jsonrpc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2.0", 3, 3);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__2;
x_2 = l_IO_FS_Stream_writeLspMessage___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n\r\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("method", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__14;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__15;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__18;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__19;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__22;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__23;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__24;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__26;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__27;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__30;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__31;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__32;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__34;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__35;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__36;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__38;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__39;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__40;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__42;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__43;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__44;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__46;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__47;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__48;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__50;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__51;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__52;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__54;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__55;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__56;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__58;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__59;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__60;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_Stream_writeLspMessage___closed__3;
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_IO_FS_Stream_writeLspMessage___closed__6;
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
lean_ctor_set_tag(x_22, 3);
x_26 = x_22;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_26 = x_40;
goto block_37;
}
}
case 1:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
lean_ctor_set_tag(x_22, 2);
x_26 = x_22;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_22, 0);
lean_inc(x_42);
lean_dec(x_22);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_26 = x_43;
goto block_37;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_box(0);
x_26 = x_44;
goto block_37;
}
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_35 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_34, x_24);
x_36 = l_List_appendTR___redArg(x_33, x_35);
x_5 = x_36;
goto block_21;
}
}
case 1:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_49);
lean_ctor_set(x_2, 0, x_48);
x_50 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_51 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_50, x_47);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_5 = x_52;
goto block_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_55 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_59 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_58, x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_5 = x_60;
goto block_21;
}
}
case 2:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_63 = x_2;
} else {
 lean_dec_ref(x_2);
 x_63 = lean_box(0);
}
x_64 = l_IO_FS_Stream_writeLspMessage___closed__6;
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
lean_ctor_set_tag(x_61, 3);
x_65 = x_61;
goto block_72;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_65 = x_75;
goto block_72;
}
}
case 1:
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_61);
if (x_76 == 0)
{
lean_ctor_set_tag(x_61, 2);
x_65 = x_61;
goto block_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_61, 0);
lean_inc(x_77);
lean_dec(x_61);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_65 = x_78;
goto block_72;
}
}
default: 
{
lean_object* x_79; 
x_79 = lean_box(0);
x_65 = x_79;
goto block_72;
}
}
block_72:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_5 = x_71;
goto block_21;
}
}
default: 
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_103; lean_object* x_104; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 2);
lean_inc(x_83);
lean_dec(x_2);
x_103 = l_IO_FS_Stream_writeLspMessage___closed__6;
switch (lean_obj_tag(x_80)) {
case 0:
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_80);
if (x_121 == 0)
{
lean_ctor_set_tag(x_80, 3);
x_104 = x_80;
goto block_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_80, 0);
lean_inc(x_122);
lean_dec(x_80);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_104 = x_123;
goto block_120;
}
}
case 1:
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_80);
if (x_124 == 0)
{
lean_ctor_set_tag(x_80, 2);
x_104 = x_80;
goto block_120;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_80, 0);
lean_inc(x_125);
lean_dec(x_80);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_104 = x_126;
goto block_120;
}
}
default: 
{
lean_object* x_127; 
x_127 = lean_box(0);
x_104 = x_127;
goto block_120;
}
}
block_102:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_IO_FS_Stream_writeLspMessage___closed__10;
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_82);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_IO_FS_Stream_writeLspMessage___closed__11;
x_96 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_95, x_83);
lean_dec(x_83);
x_97 = l_List_appendTR___redArg(x_94, x_96);
x_98 = l_Lean_Json_mkObj(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_100);
x_5 = x_101;
goto block_21;
}
block_120:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_IO_FS_Stream_writeLspMessage___closed__12;
x_107 = l_IO_FS_Stream_writeLspMessage___closed__13;
switch (x_81) {
case 0:
{
lean_object* x_108; 
x_108 = l_IO_FS_Stream_writeLspMessage___closed__17;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_108;
goto block_102;
}
case 1:
{
lean_object* x_109; 
x_109 = l_IO_FS_Stream_writeLspMessage___closed__21;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_109;
goto block_102;
}
case 2:
{
lean_object* x_110; 
x_110 = l_IO_FS_Stream_writeLspMessage___closed__25;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_110;
goto block_102;
}
case 3:
{
lean_object* x_111; 
x_111 = l_IO_FS_Stream_writeLspMessage___closed__29;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_111;
goto block_102;
}
case 4:
{
lean_object* x_112; 
x_112 = l_IO_FS_Stream_writeLspMessage___closed__33;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_112;
goto block_102;
}
case 5:
{
lean_object* x_113; 
x_113 = l_IO_FS_Stream_writeLspMessage___closed__37;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_113;
goto block_102;
}
case 6:
{
lean_object* x_114; 
x_114 = l_IO_FS_Stream_writeLspMessage___closed__41;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_114;
goto block_102;
}
case 7:
{
lean_object* x_115; 
x_115 = l_IO_FS_Stream_writeLspMessage___closed__45;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_115;
goto block_102;
}
case 8:
{
lean_object* x_116; 
x_116 = l_IO_FS_Stream_writeLspMessage___closed__49;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_116;
goto block_102;
}
case 9:
{
lean_object* x_117; 
x_117 = l_IO_FS_Stream_writeLspMessage___closed__53;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_117;
goto block_102;
}
case 10:
{
lean_object* x_118; 
x_118 = l_IO_FS_Stream_writeLspMessage___closed__57;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_118;
goto block_102;
}
default: 
{
lean_object* x_119; 
x_119 = l_IO_FS_Stream_writeLspMessage___closed__61;
x_84 = x_107;
x_85 = x_105;
x_86 = x_106;
x_87 = x_119;
goto block_102;
}
}
}
}
}
block_21:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_Lean_Json_mkObj(x_8);
x_10 = l_Lean_Json_compress(x_9);
x_11 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_12 = lean_string_utf8_byte_size(x_10);
x_13 = l_Nat_reprFast(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_IO_FS_Stream_writeLspMessage___closed__5;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = lean_apply_2(x_7, x_17, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_1(x_6, x_19);
return x_20;
}
else
{
lean_dec(x_6);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_8 = x_3;
} else {
 lean_dec_ref(x_3);
 x_8 = lean_box(0);
}
x_13 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_13);
x_14 = lean_box(0);
x_9 = x_14;
goto block_12;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
x_9 = x_13;
goto block_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_9 = x_17;
goto block_12;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
if (lean_is_scalar(x_8)) {
 x_10 = lean_alloc_ctor(0, 3, 0);
} else {
 x_10 = x_8;
}
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_10, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 2, 0);
} else {
 x_9 = x_7;
 lean_ctor_set_tag(x_9, 1);
}
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_2, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_6);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_7);
x_8 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_IO_FS_Stream_writeLspMessage(x_2, x_12, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 2, x_6);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_8);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_9);
x_13 = l_IO_FS_Stream_writeLspMessage(x_1, x_12, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
x_10 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_apply_1(x_1, x_16);
lean_ctor_set(x_8, 0, x_17);
x_10 = x_8;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_apply_1(x_1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_10 = x_20;
goto block_13;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(3, 3, 1);
} else {
 x_11 = x_9;
 lean_ctor_set_tag(x_11, 3);
}
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_6);
x_12 = l_IO_FS_Stream_writeLspMessage(x_2, x_11, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3();
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4);
l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0 = _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0();
lean_mark_persistent(l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0);
l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1 = _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1);
l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2 = _init_l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2();
lean_mark_persistent(l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2);
l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0 = _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0();
lean_mark_persistent(l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0);
l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1 = _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1);
l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2 = _init_l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3);
l_IO_FS_Stream_readLspMessage___closed__0 = _init_l_IO_FS_Stream_readLspMessage___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readLspMessage___closed__0);
l_IO_FS_Stream_readLspRequestAs___redArg___closed__0 = _init_l_IO_FS_Stream_readLspRequestAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readLspRequestAs___redArg___closed__0);
l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0 = _init_l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0);
l_IO_FS_Stream_readLspResponseAs___redArg___closed__0 = _init_l_IO_FS_Stream_readLspResponseAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readLspResponseAs___redArg___closed__0);
l_IO_FS_Stream_writeLspMessage___closed__0 = _init_l_IO_FS_Stream_writeLspMessage___closed__0();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__0);
l_IO_FS_Stream_writeLspMessage___closed__1 = _init_l_IO_FS_Stream_writeLspMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__1);
l_IO_FS_Stream_writeLspMessage___closed__2 = _init_l_IO_FS_Stream_writeLspMessage___closed__2();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__2);
l_IO_FS_Stream_writeLspMessage___closed__3 = _init_l_IO_FS_Stream_writeLspMessage___closed__3();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__3);
l_IO_FS_Stream_writeLspMessage___closed__4 = _init_l_IO_FS_Stream_writeLspMessage___closed__4();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__4);
l_IO_FS_Stream_writeLspMessage___closed__5 = _init_l_IO_FS_Stream_writeLspMessage___closed__5();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__5);
l_IO_FS_Stream_writeLspMessage___closed__6 = _init_l_IO_FS_Stream_writeLspMessage___closed__6();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__6);
l_IO_FS_Stream_writeLspMessage___closed__7 = _init_l_IO_FS_Stream_writeLspMessage___closed__7();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__7);
l_IO_FS_Stream_writeLspMessage___closed__8 = _init_l_IO_FS_Stream_writeLspMessage___closed__8();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__8);
l_IO_FS_Stream_writeLspMessage___closed__9 = _init_l_IO_FS_Stream_writeLspMessage___closed__9();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__9);
l_IO_FS_Stream_writeLspMessage___closed__10 = _init_l_IO_FS_Stream_writeLspMessage___closed__10();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__10);
l_IO_FS_Stream_writeLspMessage___closed__11 = _init_l_IO_FS_Stream_writeLspMessage___closed__11();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__11);
l_IO_FS_Stream_writeLspMessage___closed__12 = _init_l_IO_FS_Stream_writeLspMessage___closed__12();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__12);
l_IO_FS_Stream_writeLspMessage___closed__13 = _init_l_IO_FS_Stream_writeLspMessage___closed__13();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__13);
l_IO_FS_Stream_writeLspMessage___closed__14 = _init_l_IO_FS_Stream_writeLspMessage___closed__14();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__14);
l_IO_FS_Stream_writeLspMessage___closed__15 = _init_l_IO_FS_Stream_writeLspMessage___closed__15();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__15);
l_IO_FS_Stream_writeLspMessage___closed__16 = _init_l_IO_FS_Stream_writeLspMessage___closed__16();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__16);
l_IO_FS_Stream_writeLspMessage___closed__17 = _init_l_IO_FS_Stream_writeLspMessage___closed__17();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__17);
l_IO_FS_Stream_writeLspMessage___closed__18 = _init_l_IO_FS_Stream_writeLspMessage___closed__18();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__18);
l_IO_FS_Stream_writeLspMessage___closed__19 = _init_l_IO_FS_Stream_writeLspMessage___closed__19();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__19);
l_IO_FS_Stream_writeLspMessage___closed__20 = _init_l_IO_FS_Stream_writeLspMessage___closed__20();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__20);
l_IO_FS_Stream_writeLspMessage___closed__21 = _init_l_IO_FS_Stream_writeLspMessage___closed__21();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__21);
l_IO_FS_Stream_writeLspMessage___closed__22 = _init_l_IO_FS_Stream_writeLspMessage___closed__22();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__22);
l_IO_FS_Stream_writeLspMessage___closed__23 = _init_l_IO_FS_Stream_writeLspMessage___closed__23();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__23);
l_IO_FS_Stream_writeLspMessage___closed__24 = _init_l_IO_FS_Stream_writeLspMessage___closed__24();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__24);
l_IO_FS_Stream_writeLspMessage___closed__25 = _init_l_IO_FS_Stream_writeLspMessage___closed__25();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__25);
l_IO_FS_Stream_writeLspMessage___closed__26 = _init_l_IO_FS_Stream_writeLspMessage___closed__26();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__26);
l_IO_FS_Stream_writeLspMessage___closed__27 = _init_l_IO_FS_Stream_writeLspMessage___closed__27();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__27);
l_IO_FS_Stream_writeLspMessage___closed__28 = _init_l_IO_FS_Stream_writeLspMessage___closed__28();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__28);
l_IO_FS_Stream_writeLspMessage___closed__29 = _init_l_IO_FS_Stream_writeLspMessage___closed__29();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__29);
l_IO_FS_Stream_writeLspMessage___closed__30 = _init_l_IO_FS_Stream_writeLspMessage___closed__30();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__30);
l_IO_FS_Stream_writeLspMessage___closed__31 = _init_l_IO_FS_Stream_writeLspMessage___closed__31();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__31);
l_IO_FS_Stream_writeLspMessage___closed__32 = _init_l_IO_FS_Stream_writeLspMessage___closed__32();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__32);
l_IO_FS_Stream_writeLspMessage___closed__33 = _init_l_IO_FS_Stream_writeLspMessage___closed__33();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__33);
l_IO_FS_Stream_writeLspMessage___closed__34 = _init_l_IO_FS_Stream_writeLspMessage___closed__34();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__34);
l_IO_FS_Stream_writeLspMessage___closed__35 = _init_l_IO_FS_Stream_writeLspMessage___closed__35();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__35);
l_IO_FS_Stream_writeLspMessage___closed__36 = _init_l_IO_FS_Stream_writeLspMessage___closed__36();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__36);
l_IO_FS_Stream_writeLspMessage___closed__37 = _init_l_IO_FS_Stream_writeLspMessage___closed__37();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__37);
l_IO_FS_Stream_writeLspMessage___closed__38 = _init_l_IO_FS_Stream_writeLspMessage___closed__38();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__38);
l_IO_FS_Stream_writeLspMessage___closed__39 = _init_l_IO_FS_Stream_writeLspMessage___closed__39();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__39);
l_IO_FS_Stream_writeLspMessage___closed__40 = _init_l_IO_FS_Stream_writeLspMessage___closed__40();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__40);
l_IO_FS_Stream_writeLspMessage___closed__41 = _init_l_IO_FS_Stream_writeLspMessage___closed__41();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__41);
l_IO_FS_Stream_writeLspMessage___closed__42 = _init_l_IO_FS_Stream_writeLspMessage___closed__42();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__42);
l_IO_FS_Stream_writeLspMessage___closed__43 = _init_l_IO_FS_Stream_writeLspMessage___closed__43();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__43);
l_IO_FS_Stream_writeLspMessage___closed__44 = _init_l_IO_FS_Stream_writeLspMessage___closed__44();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__44);
l_IO_FS_Stream_writeLspMessage___closed__45 = _init_l_IO_FS_Stream_writeLspMessage___closed__45();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__45);
l_IO_FS_Stream_writeLspMessage___closed__46 = _init_l_IO_FS_Stream_writeLspMessage___closed__46();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__46);
l_IO_FS_Stream_writeLspMessage___closed__47 = _init_l_IO_FS_Stream_writeLspMessage___closed__47();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__47);
l_IO_FS_Stream_writeLspMessage___closed__48 = _init_l_IO_FS_Stream_writeLspMessage___closed__48();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__48);
l_IO_FS_Stream_writeLspMessage___closed__49 = _init_l_IO_FS_Stream_writeLspMessage___closed__49();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__49);
l_IO_FS_Stream_writeLspMessage___closed__50 = _init_l_IO_FS_Stream_writeLspMessage___closed__50();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__50);
l_IO_FS_Stream_writeLspMessage___closed__51 = _init_l_IO_FS_Stream_writeLspMessage___closed__51();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__51);
l_IO_FS_Stream_writeLspMessage___closed__52 = _init_l_IO_FS_Stream_writeLspMessage___closed__52();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__52);
l_IO_FS_Stream_writeLspMessage___closed__53 = _init_l_IO_FS_Stream_writeLspMessage___closed__53();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__53);
l_IO_FS_Stream_writeLspMessage___closed__54 = _init_l_IO_FS_Stream_writeLspMessage___closed__54();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__54);
l_IO_FS_Stream_writeLspMessage___closed__55 = _init_l_IO_FS_Stream_writeLspMessage___closed__55();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__55);
l_IO_FS_Stream_writeLspMessage___closed__56 = _init_l_IO_FS_Stream_writeLspMessage___closed__56();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__56);
l_IO_FS_Stream_writeLspMessage___closed__57 = _init_l_IO_FS_Stream_writeLspMessage___closed__57();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__57);
l_IO_FS_Stream_writeLspMessage___closed__58 = _init_l_IO_FS_Stream_writeLspMessage___closed__58();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__58);
l_IO_FS_Stream_writeLspMessage___closed__59 = _init_l_IO_FS_Stream_writeLspMessage___closed__59();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__59);
l_IO_FS_Stream_writeLspMessage___closed__60 = _init_l_IO_FS_Stream_writeLspMessage___closed__60();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__60);
l_IO_FS_Stream_writeLspMessage___closed__61 = _init_l_IO_FS_Stream_writeLspMessage___closed__61();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__61);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
