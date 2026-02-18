// Lean compiler output
// Module: Init.Data.String.FindPos
// Imports: public import Init.Data.String.Basic import Init.Omega import Init.Data.String.OrderInstances import Init.Data.String.Lemmas.Basic
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
uint8_t l_String_Pos_Raw_isValidForSlice(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Init.Data.String.FindPos"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__0 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__0_value;
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "String.Slice.Pos.prev!"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__1 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__1_value;
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "The start position has no previous position"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__2 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_posGE___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_posGE___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_posGE(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = l_String_Slice_posGE___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_posGT___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = l_String_Slice_posGE___redArg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_posGT(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = l_String_Slice_posGE___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_findNextPos___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_findNextPos___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_findNextPos(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_posGE___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_posGE___redArg(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_posGE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_posGE___redArg(x_6, x_2);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_posGT___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_2, x_6);
x_8 = l_String_Slice_posGE___redArg(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_posGT___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_posGT___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_posGT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = l_String_Slice_posGE___redArg(x_6, x_8);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_posGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_posGT(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLE(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLE___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_posLE(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
x_5 = l_String_Slice_posLE(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_posLT___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
x_6 = l_String_Slice_posLE(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_posLT(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_posLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_posLE(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_posLT___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_String_Slice_posLE(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_posLT___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_posLT___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_posLT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l_String_Slice_posLE(x_6, x_8);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_posLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_posLT(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
x_5 = l_String_Slice_posLE(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
x_6 = l_String_Slice_posLE(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prev(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_String_Slice_posLE(x_1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00String_Slice_Pos_prev_x21_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_Pos_prev_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__2));
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_unsigned_to_nat(115u);
x_4 = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__1));
x_5 = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_String_Slice_posLE(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_String_Slice_Pos_prev_x21___closed__3;
x_9 = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_String_Slice_posLE(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_prev___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l_String_Slice_posLE(x_6, x_8);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_prev(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_prev_x3f(x_5, x_2);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_prev_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_prev_x21(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_prev_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_12 = lean_nat_dec_eq(x_2, x_4);
if (x_12 == 0)
{
goto block_11;
}
else
{
if (x_5 == 0)
{
lean_dec(x_7);
return x_2;
}
else
{
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_9 = l_String_Slice_posLE(x_1, x_8);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prevn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_Pos_prevn(x_6, x_2, x_3);
lean_dec_ref(x_6);
return x_7;
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_Pos_prev_x21___closed__3 = _init_l_String_Slice_Pos_prev_x21___closed__3();
lean_mark_persistent(l_String_Slice_Pos_prev_x21___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
