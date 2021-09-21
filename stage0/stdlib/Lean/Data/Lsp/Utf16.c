// Lean compiler output
// Module: Lean.Data.Lsp.Utf16
// Imports: Init Init.Data.String Init.Data.Array Lean.Data.Lsp.Basic Lean.Data.Position
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
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_utf16Length___closed__1;
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length___lambda__1(uint32_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16(uint32_t);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos(lean_object*, lean_object*);
lean_object* l_String_foldrAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_FileMap_toPosition___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_utf16Length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_utf16Size___boxed(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65535;
x_3 = x_1 <= x_2;
if (x_3 == 0)
{
uint32_t x_4; 
x_4 = 2;
return x_4;
}
else
{
uint32_t x_5; 
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Char_utf16Size___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_utf16Size(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16(uint32_t x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Char_utf16Size(x_1);
x_3 = lean_uint32_to_nat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_utf16Length___lambda__1(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_utf16Length___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_utf16Length___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_String_utf16Length___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldrAux_loop___rarg(x_3, x_4, x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_utf16Length___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_utf16Length___lambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf16Length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_utf16Length(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_string_utf8_next(x_1, x_3);
x_10 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(x_10);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_11);
lean_dec(x_4);
x_2 = x_8;
x_3 = x_9;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_codepointPosToUtf16PosFrom(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_codepointPosToUtf16Pos(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_string_utf8_get(x_1, x_3);
x_8 = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(x_7);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_2 = x_9;
x_3 = x_10;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_utf16PosToCodepointPosFrom(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_utf16PosToCodepointPos(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_8;
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_codepointPosToUtf8PosFrom(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Array_isEmpty___rarg(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_back___at_Lean_FileMap_toPosition___spec__2(x_4);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_12 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_7, x_8, x_10, x_11);
x_13 = l_String_codepointPosToUtf8PosFrom(x_7, x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_7, x_8, x_14, x_14);
x_16 = l_String_codepointPosToUtf8PosFrom(x_7, x_14, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_array_fget(x_4, x_3);
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
x_21 = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(x_17, x_18, x_19, x_20);
x_22 = l_String_codepointPosToUtf8PosFrom(x_17, x_19, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_3, x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_instInhabitedNat;
x_10 = lean_array_get(x_9, x_8, x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(x_7, x_4, x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_leanPosToLspPos(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
x_4 = l_Lean_FileMap_leanPosToLspPos(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
lean_object* initialize_Lean_Data_Position(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Utf16(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_utf16Length___closed__1 = _init_l_String_utf16Length___closed__1();
lean_mark_persistent(l_String_utf16Length___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
