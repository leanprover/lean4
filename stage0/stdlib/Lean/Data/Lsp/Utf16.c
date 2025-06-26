// Lean compiler output
// Module: Lean.Data.Lsp.Utf16
// Imports: Init.Data.String Lean.Data.Lsp.Basic Lean.Data.Position Lean.DeclarationRange
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
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___at___String_utf16Length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_toLspRange(lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_utf16Size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofFilePositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___at___String_utf16Length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16(uint32_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65535;
x_3 = lean_uint32_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_String_foldrAux___at___String_utf16Length_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_string_utf8_prev(x_2, x_3);
lean_dec(x_3);
x_7 = lean_string_utf8_get(x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(x_7);
x_9 = lean_nat_add(x_8, x_1);
lean_dec(x_1);
lean_dec(x_8);
x_1 = x_9;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_foldrAux___at___String_utf16Length_spec__0(x_2, x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___at___String_utf16Length_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldrAux___at___String_utf16Length_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
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
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
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
x_4 = l_String_codepointPosToUtf16PosFrom(x_1, x_2, x_3);
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
x_4 = l_String_utf16PosToCodepointPosFrom(x_1, x_2, x_3);
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
if (x_5 == 1)
{
lean_dec(x_3);
return x_2;
}
else
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___redArg(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_back_x21___redArg(x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(x_1, x_3);
lean_dec(x_3);
lean_inc(x_6);
x_7 = l_String_utf16PosToCodepointPosFrom(x_5, x_4, x_6);
x_8 = l_String_codepointPosToUtf8PosFrom(x_5, x_6, x_7);
return x_8;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(x_1, x_7);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_String_codepointPosToUtf16PosFrom(x_5, x_4, x_8);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_String_codepointPosToUtf16PosFrom(x_5, x_4, x_8);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
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
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_4);
lean_dec(x_4);
x_7 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_5);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_8);
x_11 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_lspRangeToUtf8Range(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofFilePositions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_FileMap_leanPosToLspPos(x_1, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_3);
x_6 = l_Lean_FileMap_leanPosToLspPos(x_1, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_4 = l_Lean_FileMap_toPosition(x_1, x_2);
lean_inc(x_1);
x_5 = l_Lean_FileMap_toPosition(x_1, x_3);
x_6 = l_Lean_DeclarationRange_ofFilePositions(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_DeclarationRange_ofStringPositions(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_toLspRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_13);
x_14 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_24 = x_3;
} else {
 lean_dec_ref(x_3);
 x_24 = lean_box(0);
}
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
lean_object* initialize_Init_Data_String(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
