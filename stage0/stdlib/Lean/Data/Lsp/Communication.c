// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: public import Lean.Data.JsonRpc import Init.Data.String.TakeDrop import Init.Data.String.Search
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
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__12;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__49;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__57;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__10;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__30;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
static lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__8;
lean_object* l_String_quote(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__50;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__39;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__20;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
static lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__11;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__48;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__19;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__15;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__24;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__25;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__7;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__14;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__42;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__38;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__53;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__45;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__58;
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__35;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__21;
static lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__4;
static lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
static lean_object* l_IO_FS_Stream_readLspMessage___closed__0;
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__40;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__52;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__3;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__55;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__43;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__36;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__29;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__16;
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__0;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
static lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__1;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__26;
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__18;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__59;
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__37;
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__44;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__2;
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__41;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3;
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__23;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__56;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__34;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__27;
static uint8_t l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__46;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__22;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4;
lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__32;
lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__17;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object*);
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__33;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__31;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__47;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__51;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__28;
static lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1;
lean_object* l_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__54;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4;
x_3 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_28; 
lean_dec(x_14);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_nat_sub(x_31, x_30);
x_33 = lean_nat_dec_eq(x_29, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_inc(x_29);
lean_ctor_set_tag(x_13, 1);
lean_inc(x_29);
x_19 = x_13;
x_20 = x_29;
x_21 = x_29;
goto block_24;
}
else
{
lean_object* x_34; 
lean_free_object(x_13);
x_34 = lean_box(3);
lean_inc(x_29);
x_19 = x_34;
x_20 = x_29;
x_21 = x_29;
goto block_24;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_nat_sub(x_37, x_36);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
lean_inc(x_35);
x_19 = x_40;
x_20 = x_35;
x_21 = x_35;
goto block_24;
}
else
{
lean_object* x_41; 
x_41 = lean_box(3);
lean_inc(x_35);
x_19 = x_41;
x_20 = x_35;
x_21 = x_35;
goto block_24;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_string_utf8_next_fast(x_2, x_43);
lean_dec(x_43);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_44);
x_15 = x_13;
goto block_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_string_utf8_next_fast(x_2, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_15 = x_47;
goto block_18;
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_13, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 3);
lean_inc(x_51);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_52 = x_13;
} else {
 lean_dec_ref(x_13);
 x_52 = lean_box(0);
}
x_53 = lean_nat_dec_lt(x_50, x_4);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_lt(x_54, x_51);
lean_dec(x_51);
if (x_55 == 0)
{
lean_dec(x_14);
goto block_27;
}
else
{
lean_object* x_56; 
x_56 = lean_box(3);
x_15 = x_56;
goto block_18;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_60 = lean_string_get_byte_fast(x_2, x_50);
x_61 = lean_nat_add(x_58, x_51);
x_62 = lean_string_get_byte_fast(x_57, x_61);
x_63 = lean_uint8_dec_eq(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_68; 
x_64 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_51, x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_51, x_69);
lean_dec(x_51);
x_71 = lean_array_fget_borrowed(x_49, x_70);
lean_dec(x_70);
x_72 = lean_nat_dec_eq(x_71, x_64);
if (x_72 == 0)
{
lean_object* x_73; 
lean_inc(x_71);
lean_dec(x_52);
x_73 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_73, 0, x_48);
lean_ctor_set(x_73, 1, x_49);
lean_ctor_set(x_73, 2, x_50);
lean_ctor_set(x_73, 3, x_71);
x_15 = x_73;
goto block_18;
}
else
{
lean_object* x_74; 
lean_inc(x_50);
x_74 = l_String_Slice_pos_x3f(x_1, x_50);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_nat_add(x_50, x_69);
lean_dec(x_50);
x_76 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_75);
x_65 = x_76;
goto block_67;
}
else
{
lean_object* x_77; 
lean_dec(x_50);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec_ref(x_74);
x_65 = x_77;
goto block_67;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_52);
lean_dec(x_51);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_50, x_78);
lean_dec(x_50);
x_80 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_79);
x_81 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_81, 0, x_48);
lean_ctor_set(x_81, 1, x_49);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_64);
x_15 = x_81;
goto block_18;
}
block_67:
{
lean_object* x_66; 
if (lean_is_scalar(x_52)) {
 x_66 = lean_alloc_ctor(2, 4, 0);
} else {
 x_66 = x_52;
}
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_49);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_64);
x_15 = x_66;
goto block_18;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_14);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_50, x_82);
lean_dec(x_50);
x_84 = lean_nat_add(x_51, x_82);
lean_dec(x_51);
x_85 = lean_nat_sub(x_59, x_58);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_85);
if (lean_is_scalar(x_52)) {
 x_87 = lean_alloc_ctor(2, 4, 0);
} else {
 x_87 = x_52;
}
lean_ctor_set(x_87, 0, x_48);
lean_ctor_set(x_87, 1, x_49);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_87);
x_5 = x_88;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
x_90 = lean_nat_sub(x_83, x_85);
lean_dec(x_85);
x_91 = l_String_Slice_pos_x21(x_1, x_90);
lean_dec(x_90);
x_92 = l_String_Slice_pos_x21(x_1, x_83);
x_93 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_52)) {
 x_94 = lean_alloc_ctor(2, 4, 0);
} else {
 x_94 = x_52;
}
lean_ctor_set(x_94, 0, x_48);
lean_ctor_set(x_94, 1, x_49);
lean_ctor_set(x_94, 2, x_83);
lean_ctor_set(x_94, 3, x_93);
x_19 = x_94;
x_20 = x_91;
x_21 = x_92;
goto block_24;
}
}
}
}
default: 
{
lean_dec(x_14);
goto block_27;
}
}
block_18:
{
lean_object* x_16; 
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_5 = x_16;
goto _start;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_1);
x_22 = l_String_Slice_slice_x21(x_1, x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_19);
x_7 = x_23;
x_8 = x_22;
goto block_11;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_3);
x_26 = lean_box(1);
x_7 = x_26;
x_8 = x_25;
goto block_11;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
block_11:
{
lean_object* x_9; 
x_9 = lean_array_push(x_6, x_8);
x_5 = x_7;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
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
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_Pos_prevn(x_7, x_6, x_4);
lean_dec_ref(x_7);
lean_inc(x_8);
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
x_10 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
x_11 = l_String_Slice_beq(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_8);
x_14 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(x_13);
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
lean_inc(x_8);
x_16 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_13, x_1, x_8, x_8, x_14, x_15);
lean_dec(x_8);
x_17 = lean_array_to_list(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_17);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
x_26 = l_String_Slice_intercalate(x_25, x_19);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_19);
x_32 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
else
{
lean_object* x_35; 
lean_dec_ref(x_1);
x_35 = lean_box(0);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_2, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
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
uint8_t x_3; 
lean_dec_ref(x_2);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0;
lean_inc(x_4);
x_6 = l_Lean_Json_getObjVal_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_6);
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
x_8 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
x_9 = l_Lean_Json_getObjVal_x3f(x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_9);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_9);
x_11 = 1;
return x_11;
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
x_2 = lean_mk_io_user_error(x_1);
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
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_11 = lean_string_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_1);
lean_inc(x_6);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
x_15 = l_String_quote(x_6);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Std_Format_defWidth;
x_18 = l_Std_Format_pretty(x_16, x_17, x_8, x_8);
x_19 = lean_string_append(x_14, x_18);
lean_dec_ref(x_18);
x_20 = lean_mk_io_user_error(x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
else
{
lean_object* x_21; 
lean_dec(x_6);
x_21 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_4);
lean_dec(x_6);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec_ref(x_12);
x_23 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_dec(x_22);
return x_23;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_31 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_37 = lean_string_dec_eq(x_32, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_inc(x_32);
x_38 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_32);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec_ref(x_1);
lean_inc(x_32);
x_39 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_32);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0;
x_41 = l_String_quote(x_32);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Std_Format_defWidth;
x_44 = l_Std_Format_pretty(x_42, x_43, x_34, x_34);
x_45 = lean_string_append(x_40, x_44);
lean_dec_ref(x_44);
x_46 = lean_mk_io_user_error(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
x_48 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec_ref(x_38);
x_51 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_dec(x_50);
return x_51;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_32);
lean_dec_ref(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
lean_dec_ref(x_1);
x_58 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_4);
if (x_60 == 0)
{
return x_4;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_8 = lean_string_append(x_1, x_7);
x_9 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_string_append(x_10, x_7);
x_12 = lean_string_append(x_11, x_6);
x_13 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_8, x_14);
lean_dec_ref(x_14);
x_1 = x_15;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0;
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
x_7 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
x_8 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_9 = lean_string_append(x_8, x_5);
x_10 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
x_13 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_7, x_14);
lean_dec_ref(x_14);
x_16 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1;
x_22 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1;
x_23 = lean_string_append(x_22, x_19);
x_24 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_20);
x_27 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_21, x_28);
lean_dec_ref(x_28);
x_30 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_29, x_3);
x_31 = 93;
x_32 = lean_string_push(x_30, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
x_7 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_9 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_5);
lean_dec(x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = lean_mk_io_user_error(x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_12);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_String_Slice_toNat_x3f(x_15);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_18 = lean_string_append(x_17, x_12);
lean_dec(x_12);
x_19 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_mk_io_user_error(x_20);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec_ref(x_16);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0;
x_25 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_27 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_23);
lean_dec(x_23);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_mk_io_user_error(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec_ref(x_25);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_string_utf8_byte_size(x_31);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_String_Slice_toNat_x3f(x_34);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_37 = lean_string_append(x_36, x_31);
lean_dec(x_31);
x_38 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_mk_io_user_error(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec_ref(x_35);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
return x_3;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_IO_FS_Stream_readMessage(x_1, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_3 = x_14;
x_4 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec_ref(x_11);
x_3 = x_15;
x_4 = lean_box(0);
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_IO_FS_Stream_readLspMessage___closed__0;
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = lean_mk_io_user_error(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readLspMessage(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_IO_FS_Stream_readUTF8(x_1, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_3 = x_14;
x_4 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec_ref(x_11);
x_3 = x_15;
x_4 = lean_box(0);
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_IO_FS_Stream_readLspMessage___closed__0;
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = lean_mk_io_user_error(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readLspMessageAsString(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_14, x_2, x_3);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec_ref(x_13);
x_5 = x_17;
x_6 = lean_box(0);
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspRequestAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_mk_io_user_error(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_14, x_2, x_3);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec_ref(x_13);
x_5 = x_17;
x_6 = lean_box(0);
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_mk_io_user_error(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_14, x_2, x_3);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec_ref(x_13);
x_5 = x_17;
x_6 = lean_box(0);
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_FS_Stream_readLspResponseAs___redArg___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_mk_io_user_error(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_writeSerializedLspMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeSerializedLspMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n\r\n", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_IO_FS_Stream_writeSerializedLspMessage___closed__0;
x_7 = lean_string_utf8_byte_size(x_2);
x_8 = l_Nat_reprFast(x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_IO_FS_Stream_writeSerializedLspMessage___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = lean_apply_2(x_5, x_12, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_apply_1(x_4, lean_box(0));
return x_14;
}
else
{
lean_dec_ref(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeSerializedLspMessage(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Json_Structured_toJson(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("method", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__12;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__13;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__16;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__17;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__20;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__21;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__24;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__25;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__28;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__29;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__32;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__33;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__34;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__36;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__37;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__38;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__40;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__41;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__42;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__44;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__45;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__46;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__48;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__49;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__50;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__52;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__53;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__54;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__56;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__57;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__58;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_Stream_writeLspMessage___closed__3;
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = l_IO_FS_Stream_writeLspMessage___closed__4;
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_ctor_set_tag(x_11, 3);
x_15 = x_11;
goto block_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_15 = x_29;
goto block_26;
}
}
case 1:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_ctor_set_tag(x_11, 2);
x_15 = x_11;
goto block_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_15 = x_32;
goto block_26;
}
}
default: 
{
lean_object* x_33; 
x_33 = lean_box(0);
x_15 = x_33;
goto block_26;
}
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_IO_FS_Stream_writeLspMessage___closed__5;
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_IO_FS_Stream_writeLspMessage___closed__6;
x_24 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(x_23, x_13);
x_25 = l_List_appendTR___redArg(x_22, x_24);
x_5 = x_25;
goto block_10;
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = l_IO_FS_Stream_writeLspMessage___closed__5;
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_37);
x_39 = l_IO_FS_Stream_writeLspMessage___closed__6;
x_40 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(x_39, x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_5 = x_41;
goto block_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
x_44 = l_IO_FS_Stream_writeLspMessage___closed__5;
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_IO_FS_Stream_writeLspMessage___closed__6;
x_48 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(x_47, x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_5 = x_49;
goto block_10;
}
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_52 = x_2;
} else {
 lean_dec_ref(x_2);
 x_52 = lean_box(0);
}
x_53 = l_IO_FS_Stream_writeLspMessage___closed__4;
switch (lean_obj_tag(x_50)) {
case 0:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
lean_ctor_set_tag(x_50, 3);
x_54 = x_50;
goto block_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_54 = x_64;
goto block_61;
}
}
case 1:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_50);
if (x_65 == 0)
{
lean_ctor_set_tag(x_50, 2);
x_54 = x_50;
goto block_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
lean_dec(x_50);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_54 = x_67;
goto block_61;
}
}
default: 
{
lean_object* x_68; 
x_68 = lean_box(0);
x_54 = x_68;
goto block_61;
}
}
block_61:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
 lean_ctor_set_tag(x_55, 0);
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_5 = x_60;
goto block_10;
}
}
default: 
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_92; lean_object* x_93; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_71 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
lean_dec_ref(x_2);
x_92 = l_IO_FS_Stream_writeLspMessage___closed__4;
switch (lean_obj_tag(x_69)) {
case 0:
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_69);
if (x_110 == 0)
{
lean_ctor_set_tag(x_69, 3);
x_93 = x_69;
goto block_109;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_69, 0);
lean_inc(x_111);
lean_dec(x_69);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_93 = x_112;
goto block_109;
}
}
case 1:
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_69);
if (x_113 == 0)
{
lean_ctor_set_tag(x_69, 2);
x_93 = x_69;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_69, 0);
lean_inc(x_114);
lean_dec(x_69);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_93 = x_115;
goto block_109;
}
}
default: 
{
lean_object* x_116; 
x_116 = lean_box(0);
x_93 = x_116;
goto block_109;
}
}
block_91:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_71);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_85 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(x_84, x_72);
lean_dec(x_72);
x_86 = l_List_appendTR___redArg(x_83, x_85);
x_87 = l_Lean_Json_mkObj(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_89);
x_5 = x_90;
goto block_10;
}
block_109:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_IO_FS_Stream_writeLspMessage___closed__10;
x_96 = l_IO_FS_Stream_writeLspMessage___closed__11;
switch (x_70) {
case 0:
{
lean_object* x_97; 
x_97 = l_IO_FS_Stream_writeLspMessage___closed__15;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_97;
goto block_91;
}
case 1:
{
lean_object* x_98; 
x_98 = l_IO_FS_Stream_writeLspMessage___closed__19;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_98;
goto block_91;
}
case 2:
{
lean_object* x_99; 
x_99 = l_IO_FS_Stream_writeLspMessage___closed__23;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_99;
goto block_91;
}
case 3:
{
lean_object* x_100; 
x_100 = l_IO_FS_Stream_writeLspMessage___closed__27;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_100;
goto block_91;
}
case 4:
{
lean_object* x_101; 
x_101 = l_IO_FS_Stream_writeLspMessage___closed__31;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_101;
goto block_91;
}
case 5:
{
lean_object* x_102; 
x_102 = l_IO_FS_Stream_writeLspMessage___closed__35;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_102;
goto block_91;
}
case 6:
{
lean_object* x_103; 
x_103 = l_IO_FS_Stream_writeLspMessage___closed__39;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_103;
goto block_91;
}
case 7:
{
lean_object* x_104; 
x_104 = l_IO_FS_Stream_writeLspMessage___closed__43;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_104;
goto block_91;
}
case 8:
{
lean_object* x_105; 
x_105 = l_IO_FS_Stream_writeLspMessage___closed__47;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_105;
goto block_91;
}
case 9:
{
lean_object* x_106; 
x_106 = l_IO_FS_Stream_writeLspMessage___closed__51;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_106;
goto block_91;
}
case 10:
{
lean_object* x_107; 
x_107 = l_IO_FS_Stream_writeLspMessage___closed__55;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_107;
goto block_91;
}
default: 
{
lean_object* x_108; 
x_108 = l_IO_FS_Stream_writeLspMessage___closed__59;
x_73 = x_96;
x_74 = x_95;
x_75 = x_94;
x_76 = x_108;
goto block_91;
}
}
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
x_8 = l_Lean_Json_compress(x_7);
x_9 = l_IO_FS_Stream_writeSerializedLspMessage(x_1, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspMessage(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
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
lean_dec_ref(x_13);
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
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspRequest___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
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
lean_dec_ref(x_12);
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
x_10 = l_IO_FS_Stream_writeLspMessage(x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspNotification___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_IO_FS_Stream_writeLspMessage(x_2, x_3);
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
x_13 = l_IO_FS_Stream_writeLspMessage(x_2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspResponse___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_2);
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
x_13 = l_IO_FS_Stream_writeLspMessage(x_1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponseError(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
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
lean_dec_ref(x_1);
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
x_12 = l_IO_FS_Stream_writeLspMessage(x_2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2();
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7);
l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8 = _init_l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8();
lean_mark_persistent(l_String_Slice_split___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4);
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
l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0 = _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0();
lean_mark_persistent(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0);
l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1 = _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1);
l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2 = _init_l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2();
lean_mark_persistent(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2);
l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0 = _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0();
lean_mark_persistent(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0);
l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1 = _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1();
lean_mark_persistent(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1);
l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2 = _init_l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2();
lean_mark_persistent(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2);
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
l_IO_FS_Stream_writeSerializedLspMessage___closed__0 = _init_l_IO_FS_Stream_writeSerializedLspMessage___closed__0();
lean_mark_persistent(l_IO_FS_Stream_writeSerializedLspMessage___closed__0);
l_IO_FS_Stream_writeSerializedLspMessage___closed__1 = _init_l_IO_FS_Stream_writeSerializedLspMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_writeSerializedLspMessage___closed__1);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
