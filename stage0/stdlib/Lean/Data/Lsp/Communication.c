// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: Init Init.System.IO Lean.Data.JsonRpc
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
lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_match__1(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
extern lean_object* l_instReprList___rarg___closed__1;
lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(lean_object*);
lean_object* l_IO_FS_Stream_readLspNotificationAs___closed__1;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_0__mkPanicMessage___closed__2;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_String_takeRight(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage___closed__2;
lean_object* l_IO_FS_Stream_readLspResponseAs___closed__1;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields_match__1(lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage___closed__1;
lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_object* l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
lean_object* l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(uint8_t, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
lean_object* l_IO_FS_Stream_readLspMessage___closed__1;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__2(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
lean_object* l_IO_FS_Stream_readLspRequestAs___closed__1;
lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_String_toNat_x3f(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__3;
lean_object* l_IO_FS_Stream_writeLspResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_3(x_4, x_10, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\x0d\n");
return x_1;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
x_4 = l_instDecidableNot___rarg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_7 = l_String_takeRight(x_1, x_6);
x_8 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_String_dropRight(x_1, x_6);
x_12 = l___private_Init_Util_0__mkPanicMessage___closed__2;
x_13 = l_String_splitOn(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_String_intercalate(x_12, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_String_intercalate(x_12, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Invalid header field: ");
return x_1;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_8 = l_String_quote(x_1);
lean_dec(x_1);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Std_Format_defWidth;
x_11 = lean_format_pretty(x_9, x_10);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_instInhabitedParserDescr___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_2, x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Stream was closed");
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
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_apply_1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_1(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(x_5, x_1, x_12, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_6, x_5);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = l_prec_x28___x29___closed__3;
x_11 = lean_string_append(x_10, x_8);
x_12 = l_term_x5b___x5d___closed__5;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_9);
x_15 = l_prec_x28___x29___closed__7;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_7);
lean_dec(x_7);
return x_18;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_instInhabitedParserDescr___closed__1;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = 0;
x_23 = l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_22, x_21);
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = l_prec_x28___x29___closed__3;
x_27 = lean_string_append(x_26, x_24);
x_28 = l_term_x5b___x5d___closed__5;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_25);
x_31 = l_prec_x28___x29___closed__7;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_23);
lean_dec(x_23);
return x_33;
}
}
}
}
lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_instReprList___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_4, x_1);
lean_dec(x_1);
x_6 = l_term_x5b___x5d___closed__3;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_term_x5b___x5d___closed__9;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 1;
x_14 = l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_13, x_12);
lean_dec(x_12);
x_15 = l_term_x5b___x5d___closed__3;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_term_x5b___x5d___closed__9;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Content-Length");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("No Content-Length field in header: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Content-Length header field value '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a Nat");
return x_1;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_7 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(x_5);
x_9 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_String_toNat_x3f(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_17 = lean_string_append(x_16, x_14);
lean_dec(x_14);
x_18 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_25 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(x_22);
x_27 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_instInhabitedParserDescr___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_String_toNat_x3f(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_36 = lean_string_append(x_35, x_33);
lean_dec(x_33);
x_37 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_23);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_23);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
return x_3;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_Stream_readLspMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP message: ");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_IO_FS_Stream_readMessage(x_1, x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_io_error_to_string(x_8);
x_10 = l_IO_FS_Stream_readLspMessage___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_io_error_to_string(x_15);
x_18 = l_IO_FS_Stream_readLspMessage___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_instInhabitedParserDescr___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = l_IO_FS_Stream_readLspMessage___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_instInhabitedParserDescr___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_34 = lean_io_error_to_string(x_32);
x_35 = l_IO_FS_Stream_readLspMessage___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_instInhabitedParserDescr___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspRequestAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP request: ");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_readRequestAs(x_1, x_7, x_2, lean_box(0), x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_io_error_to_string(x_18);
x_21 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_instInhabitedParserDescr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_instInhabitedParserDescr___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_io_error_to_string(x_35);
x_38 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_instInhabitedParserDescr___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspNotificationAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP notification: ");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_readNotificationAs(x_1, x_7, x_2, lean_box(0), x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_io_error_to_string(x_18);
x_21 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_instInhabitedParserDescr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_instInhabitedParserDescr___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_io_error_to_string(x_35);
x_38 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_instInhabitedParserDescr___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspResponseAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot read LSP response: ");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_readResponseAs(x_1, x_7, x_2, lean_box(0), x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = l_IO_FS_Stream_readLspResponseAs___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_io_error_to_string(x_18);
x_21 = l_IO_FS_Stream_readLspResponseAs___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_instInhabitedParserDescr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = l_IO_FS_Stream_readLspResponseAs___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_instInhabitedParserDescr___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_io_error_to_string(x_35);
x_38 = l_IO_FS_Stream_readLspResponseAs___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_instInhabitedParserDescr___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Content-Length: ");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\x0d\n\x0d\n");
return x_1;
}
}
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_32 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_31, x_25);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
x_38 = l_List_append___rarg(x_37, x_32);
x_39 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Json_mkObj(x_40);
x_5 = x_41;
goto block_22;
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_30);
x_47 = l_List_append___rarg(x_46, x_32);
x_48 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Json_mkObj(x_49);
x_5 = x_50;
goto block_22;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_30);
x_53 = l_List_append___rarg(x_52, x_32);
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Json_mkObj(x_55);
x_5 = x_56;
goto block_22;
}
}
}
case 1:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_63 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_62, x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Json_mkObj(x_66);
x_5 = x_67;
goto block_22;
}
case 2:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_2, 0);
x_69 = lean_ctor_get(x_2, 1);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
switch (lean_obj_tag(x_68)) {
case 0:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Json_mkObj(x_80);
x_5 = x_81;
goto block_22;
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
x_87 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Json_mkObj(x_88);
x_5 = x_89;
goto block_22;
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_73);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Json_mkObj(x_93);
x_5 = x_94;
goto block_22;
}
}
}
default: 
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_97 = lean_ctor_get(x_2, 1);
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_97);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_97);
x_100 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_105 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_104, x_98);
switch (lean_obj_tag(x_95)) {
case 0:
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_95, 0);
lean_inc(x_135);
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_106 = x_136;
goto block_134;
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_95, 0);
lean_inc(x_137);
x_138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_106 = x_138;
goto block_134;
}
default: 
{
lean_object* x_139; 
x_139 = lean_box(0);
x_106 = x_139;
goto block_134;
}
}
block_134:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
switch (x_96) {
case 0:
{
lean_object* x_123; 
x_123 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_109 = x_123;
goto block_122;
}
case 1:
{
lean_object* x_124; 
x_124 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_109 = x_124;
goto block_122;
}
case 2:
{
lean_object* x_125; 
x_125 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_109 = x_125;
goto block_122;
}
case 3:
{
lean_object* x_126; 
x_126 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_109 = x_126;
goto block_122;
}
case 4:
{
lean_object* x_127; 
x_127 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_109 = x_127;
goto block_122;
}
case 5:
{
lean_object* x_128; 
x_128 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_109 = x_128;
goto block_122;
}
case 6:
{
lean_object* x_129; 
x_129 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_109 = x_129;
goto block_122;
}
case 7:
{
lean_object* x_130; 
x_130 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_109 = x_130;
goto block_122;
}
case 8:
{
lean_object* x_131; 
x_131 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_109 = x_131;
goto block_122;
}
case 9:
{
lean_object* x_132; 
x_132 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_109 = x_132;
goto block_122;
}
default: 
{
lean_object* x_133; 
x_133 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_109 = x_133;
goto block_122;
}
}
block_122:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
x_113 = l_List_append___rarg(x_112, x_105);
x_114 = l_Lean_Json_mkObj(x_113);
x_115 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_102);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Json_mkObj(x_120);
x_5 = x_121;
goto block_22;
}
}
}
}
block_22:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Json_compress(x_5);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = l_Nat_repr(x_7);
x_9 = l_IO_FS_Stream_writeLspMessage___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_IO_FS_Stream_writeLspMessage___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_6);
lean_dec(x_6);
x_14 = lean_apply_2(x_4, x_13, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_2, x_9, x_4);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspRequest___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspNotification___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponse___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponseError(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_10, x_4);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_apply_1(x_1, x_16);
lean_ctor_set(x_5, 0, x_17);
x_18 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
x_19 = l_IO_FS_Stream_writeLspMessage(x_2, x_18, x_4);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_13);
x_24 = l_IO_FS_Stream_writeLspMessage(x_2, x_23, x_4);
lean_dec(x_23);
return x_24;
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponseErrorWithData___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Communication(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4);
l_IO_FS_Stream_readLspMessage___closed__1 = _init_l_IO_FS_Stream_readLspMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspMessage___closed__1);
l_IO_FS_Stream_readLspRequestAs___closed__1 = _init_l_IO_FS_Stream_readLspRequestAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspRequestAs___closed__1);
l_IO_FS_Stream_readLspNotificationAs___closed__1 = _init_l_IO_FS_Stream_readLspNotificationAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspNotificationAs___closed__1);
l_IO_FS_Stream_readLspResponseAs___closed__1 = _init_l_IO_FS_Stream_readLspResponseAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspResponseAs___closed__1);
l_IO_FS_Stream_writeLspMessage___closed__1 = _init_l_IO_FS_Stream_writeLspMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__1);
l_IO_FS_Stream_writeLspMessage___closed__2 = _init_l_IO_FS_Stream_writeLspMessage___closed__2();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
