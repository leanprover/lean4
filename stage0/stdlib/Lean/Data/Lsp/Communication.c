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
LEAN_EXPORT lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__12;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__49;
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__57;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__10;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__30;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
lean_object* l_String_toNat_x3f(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__8;
lean_object* l_String_quote(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__50;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__39;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*);
static lean_object* l_IO_FS_Stream_readLspNotificationAs___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__20;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__11;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__6;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__48;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__19;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__15;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__24;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__25;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__7;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__14;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__42;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__38;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__53;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__45;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__63;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__58;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__35;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__21;
static lean_object* l_IO_FS_Stream_readLspRequestAs___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__4;
static lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3;
static lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__40;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__52;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__3;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__55;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__43;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__5;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__36;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__29;
static lean_object* l_IO_FS_Stream_readLspResponseAs___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__16;
static lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2;
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__26;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__18;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__59;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__37;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__44;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__9;
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__41;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__23;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__56;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__34;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__27;
static lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__46;
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__22;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__32;
LEAN_EXPORT lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__17;
static lean_object* l_IO_FS_Stream_readLspMessage___closed__1;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__60;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3;
lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__33;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__31;
static uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__47;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__51;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__62;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__61;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__28;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__54;
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_nat_sub(x_6, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Substring_prevn(x_8, x_10, x_9);
lean_dec(x_8);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_11);
x_13 = lean_string_utf8_extract(x_1, x_12, x_6);
lean_dec(x_6);
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_string_utf8_extract(x_1, x_7, x_12);
lean_dec(x_12);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
x_21 = l_String_splitOnAux(x_18, x_20, x_7, x_7, x_7, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_box(0);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_String_intercalate(x_20, x_23);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 1, x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_String_intercalate(x_20, x_32);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 1, x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_21);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_38 = x_23;
} else {
 lean_dec_ref(x_23);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_String_intercalate(x_20, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_1);
x_43 = lean_box(0);
return x_43;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3() {
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
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1;
x_3 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2;
lean_inc(x_5);
x_7 = l_Lean_Json_getObjVal_x3f(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_7);
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3;
x_10 = l_Lean_Json_getObjVal_x3f(x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_10);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 1;
return x_12;
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
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid header field: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 ", 175, 175);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_String_quote(x_1);
lean_dec(x_1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Std_Format_defWidth;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_format_pretty(x_10, x_11, x_12, x_12);
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_2, x_4);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
return x_36;
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Stream was closed", 17, 17);
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
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(x_6, x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(x_14, x_1, x_19, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_1);
x_21 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2;
x_10 = lean_string_append(x_9, x_7);
x_11 = lean_string_append(x_10, x_5);
x_12 = lean_string_append(x_11, x_8);
x_13 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_6, x_14);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1;
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
x_7 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2;
x_8 = lean_string_append(x_7, x_5);
x_9 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_6);
x_12 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = 93;
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2;
x_23 = lean_string_append(x_22, x_20);
x_24 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_21);
x_27 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_30, x_3);
x_32 = lean_string_push(x_31, x_19);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No Content-Length field in header: ", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length header field value '", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4() {
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
x_6 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_7 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = l_String_toNat_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_18 = lean_string_append(x_17, x_15);
lean_dec(x_15);
x_19 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
x_20 = lean_string_append(x_18, x_19);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_20);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_String_toNat_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_25 = lean_string_append(x_24, x_22);
lean_dec(x_22);
x_26 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
else
{
lean_object* x_29; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1;
x_33 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(x_30);
lean_dec(x_30);
x_35 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_42 = x_33;
} else {
 lean_dec_ref(x_33);
 x_42 = lean_box(0);
}
x_43 = l_String_toNat_x3f(x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3;
x_45 = lean_string_append(x_44, x_41);
lean_dec(x_41);
x_46 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__4;
x_47 = lean_string_append(x_45, x_46);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(18, 1, 0);
} else {
 x_48 = x_42;
 lean_ctor_set_tag(x_48, 18);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_3);
if (x_52 == 0)
{
return x_3;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readLspMessage___closed__1() {
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
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_20 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_29 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_37 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_1 = lean_mk_string_unchecked("Cannot read LSP request: ", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_23 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_32 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_40 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_1 = lean_mk_string_unchecked("Cannot read LSP notification: ", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_23 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_32 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_40 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_1 = lean_mk_string_unchecked("Cannot read LSP response: ", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_23 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_32 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
x_40 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jsonrpc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__3;
x_2 = l_IO_FS_Stream_writeLspMessage___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Length: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n\r\n", 4, 4);
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
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32600u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32601u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32602u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32603u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__33;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32002u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32001u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__41;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32801u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__45;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32800u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__49;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32900u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__53;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(32901u);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__57;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__60;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__61;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_writeLspMessage___closed__62;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_32 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_31, x_25);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_ctor_set_tag(x_23, 3);
x_34 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
x_37 = l_List_appendTR___rarg(x_36, x_32);
x_38 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Json_mkObj(x_39);
x_5 = x_40;
goto block_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
x_46 = l_List_appendTR___rarg(x_45, x_32);
x_47 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Json_mkObj(x_48);
x_5 = x_49;
goto block_22;
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_ctor_set_tag(x_23, 2);
x_51 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_30);
x_54 = l_List_appendTR___rarg(x_53, x_32);
x_55 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Json_mkObj(x_56);
x_5 = x_57;
goto block_22;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_23, 0);
lean_inc(x_58);
lean_dec(x_23);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_30);
x_63 = l_List_appendTR___rarg(x_62, x_32);
x_64 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Json_mkObj(x_65);
x_5 = x_66;
goto block_22;
}
}
default: 
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = l_IO_FS_Stream_writeLspMessage___closed__10;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_30);
x_69 = l_List_appendTR___rarg(x_68, x_32);
x_70 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Json_mkObj(x_71);
x_5 = x_72;
goto block_22;
}
}
}
case 1:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = lean_ctor_get(x_2, 1);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_74);
x_77 = l_IO_FS_Stream_writeLspMessage___closed__7;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_76);
lean_ctor_set(x_2, 0, x_77);
x_78 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_79 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_78, x_75);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Json_mkObj(x_82);
x_5 = x_83;
goto block_22;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_2);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_84);
x_87 = l_IO_FS_Stream_writeLspMessage___closed__7;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_IO_FS_Stream_writeLspMessage___closed__8;
x_90 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_89, x_85);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Json_mkObj(x_93);
x_5 = x_94;
goto block_22;
}
}
case 2:
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_2);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_2, 0);
x_97 = l_IO_FS_Stream_writeLspMessage___closed__11;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_97);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_98);
switch (lean_obj_tag(x_96)) {
case 0:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_ctor_set_tag(x_96, 3);
x_101 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_104 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_Json_mkObj(x_105);
x_5 = x_106;
goto block_22;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get(x_96, 0);
lean_inc(x_107);
lean_dec(x_96);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_99);
x_112 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Json_mkObj(x_113);
x_5 = x_114;
goto block_22;
}
}
case 1:
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_96);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_ctor_set_tag(x_96, 2);
x_116 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_96);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_99);
x_119 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Json_mkObj(x_120);
x_5 = x_121;
goto block_22;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_96, 0);
lean_inc(x_122);
lean_dec(x_96);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_99);
x_127 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Json_mkObj(x_128);
x_5 = x_129;
goto block_22;
}
}
default: 
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = l_IO_FS_Stream_writeLspMessage___closed__10;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_99);
x_132 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Json_mkObj(x_133);
x_5 = x_134;
goto block_22;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_2, 0);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_2);
x_137 = l_IO_FS_Stream_writeLspMessage___closed__11;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
switch (lean_obj_tag(x_135)) {
case 0:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(3, 1, 0);
} else {
 x_143 = x_142;
 lean_ctor_set_tag(x_143, 3);
}
lean_ctor_set(x_143, 0, x_141);
x_144 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
x_147 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Json_mkObj(x_148);
x_5 = x_149;
goto block_22;
}
case 1:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_150 = lean_ctor_get(x_135, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_151 = x_135;
} else {
 lean_dec_ref(x_135);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(2, 1, 0);
} else {
 x_152 = x_151;
 lean_ctor_set_tag(x_152, 2);
}
lean_ctor_set(x_152, 0, x_150);
x_153 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_140);
x_156 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Json_mkObj(x_157);
x_5 = x_158;
goto block_22;
}
default: 
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = l_IO_FS_Stream_writeLspMessage___closed__10;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_140);
x_161 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_Json_mkObj(x_162);
x_5 = x_163;
goto block_22;
}
}
}
}
default: 
{
lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_164 = lean_ctor_get(x_2, 0);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_166 = lean_ctor_get(x_2, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_2, 2);
lean_inc(x_167);
lean_dec(x_2);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_169 = l_IO_FS_Stream_writeLspMessage___closed__12;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_IO_FS_Stream_writeLspMessage___closed__13;
x_174 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_173, x_167);
lean_dec(x_167);
switch (lean_obj_tag(x_164)) {
case 0:
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_164);
if (x_205 == 0)
{
lean_ctor_set_tag(x_164, 3);
x_175 = x_164;
goto block_204;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_164, 0);
lean_inc(x_206);
lean_dec(x_164);
x_207 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_175 = x_207;
goto block_204;
}
}
case 1:
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_164);
if (x_208 == 0)
{
lean_ctor_set_tag(x_164, 2);
x_175 = x_164;
goto block_204;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_164, 0);
lean_inc(x_209);
lean_dec(x_164);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_175 = x_210;
goto block_204;
}
}
default: 
{
lean_object* x_211; 
x_211 = lean_box(0);
x_175 = x_211;
goto block_204;
}
}
block_204:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = l_IO_FS_Stream_writeLspMessage___closed__9;
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
switch (x_165) {
case 0:
{
lean_object* x_192; 
x_192 = l_IO_FS_Stream_writeLspMessage___closed__19;
x_178 = x_192;
goto block_191;
}
case 1:
{
lean_object* x_193; 
x_193 = l_IO_FS_Stream_writeLspMessage___closed__23;
x_178 = x_193;
goto block_191;
}
case 2:
{
lean_object* x_194; 
x_194 = l_IO_FS_Stream_writeLspMessage___closed__27;
x_178 = x_194;
goto block_191;
}
case 3:
{
lean_object* x_195; 
x_195 = l_IO_FS_Stream_writeLspMessage___closed__31;
x_178 = x_195;
goto block_191;
}
case 4:
{
lean_object* x_196; 
x_196 = l_IO_FS_Stream_writeLspMessage___closed__35;
x_178 = x_196;
goto block_191;
}
case 5:
{
lean_object* x_197; 
x_197 = l_IO_FS_Stream_writeLspMessage___closed__39;
x_178 = x_197;
goto block_191;
}
case 6:
{
lean_object* x_198; 
x_198 = l_IO_FS_Stream_writeLspMessage___closed__43;
x_178 = x_198;
goto block_191;
}
case 7:
{
lean_object* x_199; 
x_199 = l_IO_FS_Stream_writeLspMessage___closed__47;
x_178 = x_199;
goto block_191;
}
case 8:
{
lean_object* x_200; 
x_200 = l_IO_FS_Stream_writeLspMessage___closed__51;
x_178 = x_200;
goto block_191;
}
case 9:
{
lean_object* x_201; 
x_201 = l_IO_FS_Stream_writeLspMessage___closed__55;
x_178 = x_201;
goto block_191;
}
case 10:
{
lean_object* x_202; 
x_202 = l_IO_FS_Stream_writeLspMessage___closed__59;
x_178 = x_202;
goto block_191;
}
default: 
{
lean_object* x_203; 
x_203 = l_IO_FS_Stream_writeLspMessage___closed__63;
x_178 = x_203;
goto block_191;
}
}
block_191:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_179 = l_IO_FS_Stream_writeLspMessage___closed__14;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_172);
x_182 = l_List_appendTR___rarg(x_181, x_174);
x_183 = l_Lean_Json_mkObj(x_182);
x_184 = l_IO_FS_Stream_writeLspMessage___closed__15;
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_171);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_177);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_IO_FS_Stream_writeLspMessage___closed__4;
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = l_Lean_Json_mkObj(x_189);
x_5 = x_190;
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
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_9 = l_IO_FS_Stream_writeLspMessage___closed__5;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_IO_FS_Stream_writeLspMessage___closed__6;
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
x_16 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 2, x_8);
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_3, 2, x_7);
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_3, 2, x_13);
x_14 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_IO_FS_Stream_writeLspMessage(x_2, x_20, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_IO_FS_Stream_writeLspMessage(x_2, x_25, x_4);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspRequest___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_8);
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_13);
x_14 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_IO_FS_Stream_writeLspMessage(x_2, x_19, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_IO_FS_Stream_writeLspMessage(x_2, x_24, x_4);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspNotification___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponse___rarg), 4, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_8);
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
x_15 = l_IO_FS_Stream_writeLspMessage(x_2, x_14, x_4);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_apply_1(x_1, x_19);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set_tag(x_3, 3);
x_21 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_24);
x_25 = l_IO_FS_Stream_writeLspMessage(x_2, x_3, x_4);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_3);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_30 = x_5;
} else {
 lean_dec_ref(x_5);
 x_30 = lean_box(0);
}
x_31 = lean_apply_1(x_1, x_29);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_27);
x_34 = l_IO_FS_Stream_writeLspMessage(x_2, x_33, x_4);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponseErrorWithData___rarg), 4, 0);
return x_2;
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
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4();
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__2);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___lambda__1___closed__3);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1);
l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2 = _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1 = _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1();
lean_mark_persistent(l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__1);
l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2 = _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2();
lean_mark_persistent(l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__2);
l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3 = _init_l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3();
lean_mark_persistent(l_List_foldl___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__3___closed__3);
l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1 = _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1();
lean_mark_persistent(l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__1);
l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2 = _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2();
lean_mark_persistent(l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__2);
l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3 = _init_l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3();
lean_mark_persistent(l_List_toString___at___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___spec__2___closed__3);
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
l_IO_FS_Stream_writeLspMessage___closed__62 = _init_l_IO_FS_Stream_writeLspMessage___closed__62();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__62);
l_IO_FS_Stream_writeLspMessage___closed__63 = _init_l_IO_FS_Stream_writeLspMessage___closed__63();
lean_mark_persistent(l_IO_FS_Stream_writeLspMessage___closed__63);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
