// Lean compiler output
// Module: Init.LeanExt
// Imports: Init.Data.String.Basic Init.Data.UInt
#include "runtime/lean.h"
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
lean_object* l_Lean_ParserDescr_pushLeading;
lean_object* l_Lean_ParserDescr_orelse(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_optional(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_many(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_ParserDescr_try(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_unicodeSymbol(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t);
lean_object* l_Lean_ParserDescr_many1(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_many___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_parser(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_andthen(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_node(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_try___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_node___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_unicodeSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(10, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescrCore_inhabited(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_andthen(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_andthen(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_orelse(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_orelse(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_optional(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_optional(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_lookahead(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_lookahead(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_try(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_try___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_try(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_many(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_many___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_many(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_many1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_many1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(7, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_sepBy(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(8, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_sepBy1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_node(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(9, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_node___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_node(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_symbol(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(10, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_symbol(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_unicodeSymbol(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_unicodeSymbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_ParserDescr_unicodeSymbol(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_ParserDescr_pushLeading() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(12);
return x_1;
}
}
lean_object* l_Lean_ParserDescr_parser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_LeanExt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ParserDescr_pushLeading = _init_l_Lean_ParserDescr_pushLeading();
lean_mark_persistent(l_Lean_ParserDescr_pushLeading);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
