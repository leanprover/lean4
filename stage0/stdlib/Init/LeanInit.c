// Lean compiler output
// Module: Init.LeanInit
// Imports: Init.Data.String.Basic Init.Data.Array.Basic Init.Data.UInt Init.Data.Hashable Init.Control.Reader Init.Control.Option
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
lean_object* l_Array_getSepElems___rarg___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_pushLeading;
lean_object* l_Lean_MacroM_monadQuotation;
lean_object* l_Lean_ParserDescr_orelse(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_optional(uint8_t, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead(uint8_t, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_many(uint8_t, lean_object*);
lean_object* l_Lean_HasBeq___closed__1;
lean_object* l_Lean_ParserDescr_ident(uint8_t);
lean_object* l_Lean_mkNameSimple(lean_object*);
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_char(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Name_hashable___closed__1;
lean_object* l_Lean_ParserDescr_try(uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind___closed__2;
lean_object* l_Lean_Syntax_getKind___closed__1;
lean_object* l_Lean_Name_hashable;
lean_object* l_Lean_ParserDescr_str(uint8_t);
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t);
lean_object* l_Lean_Syntax_getKind___closed__4;
lean_object* l_Lean_ParserDescr_many1(uint8_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_optional___rarg___closed__1;
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_many___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_num___boxed(lean_object*);
lean_object* l_Array_getSepElems(lean_object*);
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hashEx___boxed(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_name_hash(lean_object*);
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object*);
lean_object* l_Array_getSepElems___rarg(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_ParserDescr_parser(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy(uint8_t, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_andthen(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_node(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_try___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_ident___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_str___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_node___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_parser___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_ParserDescr_char___boxed(lean_object*);
lean_object* l_Lean_HasBeq;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScopes(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_MacroM_monadQuotation___closed__1;
lean_object* l_Lean_Syntax_getKind___closed__3;
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_addMacroScopes___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_num(uint8_t);
lean_object* l_Lean_ParserDescr_symbol(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Name_hash___boxed(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___closed__2;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Name_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
size_t l_Lean_Name_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
size_t x_2; 
x_2 = 1723;
return x_2;
}
else
{
size_t x_3; 
x_3 = lean_ctor_get_usize(x_1, 2);
return x_3;
}
}
}
lean_object* l_Lean_Name_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Name_hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_hashable___closed__1;
return x_1;
}
}
size_t lean_name_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = l_Lean_Name_hash(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Name_hashEx___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_name_hash(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* lean_name_mk_string(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_string_hash(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* lean_name_mk_numeral(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_of_nat(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(2, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_Lean_mkNameSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_name_mk_string(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Name_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_name_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(10, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
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
lean_object* l_Lean_ParserDescr_num(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_num___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_num(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_str(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(13, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_str___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_str(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_char(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(14, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_char___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_char(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_ident(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(15, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_ident___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_ident(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(11, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_nonReservedSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_ParserDescr_nonReservedSymbol(x_1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ParserDescr_pushLeading() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(16);
return x_1;
}
}
lean_object* l_Lean_ParserDescr_parser(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(17, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_parser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_parser(x_4, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Syntax_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_getKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_getKind___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getKind(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getKind___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Syntax_getKind___closed__4;
return x_7;
}
}
}
}
uint8_t l_Lean_Syntax_isOfKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_getArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_empty___closed__1;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_addMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_addMacroScopes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_mk_numeral(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_addMacroScopes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_addMacroScopes___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_optional___rarg___closed__1;
x_2 = l_Lean_MacroM_monadQuotation___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MacroM_monadQuotation___closed__2;
return x_1;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_array_push(x_4, x_7);
x_9 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_getSepElems___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_getSepElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getSepElems___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_getSepElems___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_getSepElems___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Option(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_LeanInit(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Name_inhabited = _init_l_Lean_Name_inhabited();
lean_mark_persistent(l_Lean_Name_inhabited);
l_Lean_Name_hashable___closed__1 = _init_l_Lean_Name_hashable___closed__1();
lean_mark_persistent(l_Lean_Name_hashable___closed__1);
l_Lean_Name_hashable = _init_l_Lean_Name_hashable();
lean_mark_persistent(l_Lean_Name_hashable);
l_Lean_HasBeq___closed__1 = _init_l_Lean_HasBeq___closed__1();
lean_mark_persistent(l_Lean_HasBeq___closed__1);
l_Lean_HasBeq = _init_l_Lean_HasBeq();
lean_mark_persistent(l_Lean_HasBeq);
l_Lean_ParserDescr_pushLeading = _init_l_Lean_ParserDescr_pushLeading();
lean_mark_persistent(l_Lean_ParserDescr_pushLeading);
l_Lean_Syntax_inhabited = _init_l_Lean_Syntax_inhabited();
lean_mark_persistent(l_Lean_Syntax_inhabited);
l_Lean_Syntax_getKind___closed__1 = _init_l_Lean_Syntax_getKind___closed__1();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__1);
l_Lean_Syntax_getKind___closed__2 = _init_l_Lean_Syntax_getKind___closed__2();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__2);
l_Lean_Syntax_getKind___closed__3 = _init_l_Lean_Syntax_getKind___closed__3();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__3);
l_Lean_Syntax_getKind___closed__4 = _init_l_Lean_Syntax_getKind___closed__4();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__4);
l_Lean_MacroM_monadQuotation___closed__1 = _init_l_Lean_MacroM_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__1);
l_Lean_MacroM_monadQuotation___closed__2 = _init_l_Lean_MacroM_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__2);
l_Lean_MacroM_monadQuotation = _init_l_Lean_MacroM_monadQuotation();
lean_mark_persistent(l_Lean_MacroM_monadQuotation);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
