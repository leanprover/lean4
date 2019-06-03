// Lean compiler output
// Module: init.lean.parser.stringliteral
// Imports: init.lean.parser.parsec
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__1(obj*, uint32);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_parseStringLiteralAux(obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___boxed(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_Lean_Parser_MonadParsec_any___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral(obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_digit___rarg(obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar(obj*, obj*);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__1___boxed(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3(obj*, uint32);
obj* l_Lean_Parser_parseStringLiteralAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
extern obj* l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
obj* l_Lean_Parser_parseHexDigit___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
uint8 l_UInt32_decLe(uint32, uint32);
uint32 l_Char_ofNat(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__2(obj*, obj*, obj*, obj*, uint32);
obj* l_Lean_Parser_parseStringLiteral___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___boxed(obj*, obj*);
obj* l_Char_quoteCore(uint32);
uint8 l_String_OldIterator_hasNext___main(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___boxed(obj*, obj*);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__4(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHexDigit(obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Parser_parseHexDigit___rarg___closed__1;
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5___boxed(obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__5___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main(obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__6(obj*, obj*, obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5(obj*, uint32);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__5(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___rarg(obj*, obj*, uint32);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHexDigit___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__1(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::uint32_to_nat(x_2);
x_6 = lean::mk_nat_obj(48u);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_6, x_7, x_5, x_5);
return x_8;
}
else
{
uint32 x_9; uint32 x_10; uint8 x_11; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = 97;
x_11 = x_10 <= x_9;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_3);
lean::dec(x_2);
x_12 = l_Char_quoteCore(x_9);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_15 = lean::string_append(x_14, x_13);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_15, x_17, x_16, x_16);
return x_18;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = 102;
x_20 = x_9 <= x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_3);
lean::dec(x_2);
x_21 = l_Char_quoteCore(x_9);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_24 = lean::string_append(x_23, x_22);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
x_28 = lean::box_uint32(x_9);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_29, 0, x_3);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::apply_2(x_2, lean::box(0), x_29);
return x_30;
}
}
}
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::uint32_to_nat(x_2);
x_6 = lean::mk_nat_obj(97u);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_8 = lean::mk_nat_obj(10u);
x_9 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
x_10 = lean::apply_2(x_4, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_6, x_7, x_5, x_5);
return x_8;
}
else
{
uint32 x_9; uint32 x_10; uint8 x_11; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = 65;
x_11 = x_10 <= x_9;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_3);
lean::dec(x_2);
x_12 = l_Char_quoteCore(x_9);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_15 = lean::string_append(x_14, x_13);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_15, x_17, x_16, x_16);
return x_18;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = 70;
x_20 = x_9 <= x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_3);
lean::dec(x_2);
x_21 = l_Char_quoteCore(x_9);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_24 = lean::string_append(x_23, x_22);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
x_28 = lean::box_uint32(x_9);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_29, 0, x_3);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::apply_2(x_2, lean::box(0), x_29);
return x_30;
}
}
}
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::uint32_to_nat(x_2);
x_6 = lean::mk_nat_obj(65u);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_8 = lean::mk_nat_obj(10u);
x_9 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
x_10 = lean::apply_2(x_4, lean::box(0), x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_parseHexDigit___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("hexadecimal");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_4 = lean::cnstr_get(x_3, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::inc(x_2);
x_6 = l_Lean_Parser_MonadParsec_digit___rarg(x_1, x_2);
lean::inc(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_7, 0, x_3);
lean::inc(x_5);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_7);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_9);
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
lean::inc(x_9);
lean::inc(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg___lambda__2), 3, 2);
lean::closure_set(x_12, 0, x_2);
lean::closure_set(x_12, 1, x_9);
lean::inc(x_5);
lean::inc(x_11);
x_13 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_12);
lean::inc(x_3);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg___lambda__3___boxed), 2, 1);
lean::closure_set(x_14, 0, x_3);
lean::inc(x_5);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_13, x_14);
lean::inc(x_2);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg___lambda__4), 3, 2);
lean::closure_set(x_16, 0, x_2);
lean::closure_set(x_16, 1, x_9);
lean::inc(x_5);
x_17 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg___lambda__5___boxed), 2, 1);
lean::closure_set(x_18, 0, x_3);
x_19 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_17, x_18);
lean::inc(x_4);
x_20 = lean::apply_3(x_4, lean::box(0), x_15, x_19);
x_21 = lean::apply_3(x_4, lean::box(0), x_8, x_20);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
x_23 = l_Lean_Parser_parseHexDigit___rarg___closed__1;
x_24 = lean::apply_3(x_22, lean::box(0), x_23, x_21);
return x_24;
}
}
obj* l_Lean_Parser_parseHexDigit(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHexDigit___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_parseHexDigit___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_parseHexDigit___rarg___lambda__3(x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_parseHexDigit___rarg___lambda__5(x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_parseHexDigit___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseHexDigit(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::mk_nat_obj(16u);
x_9 = lean::nat_mul(x_8, x_2);
x_10 = lean::nat_add(x_9, x_3);
lean::dec(x_9);
x_11 = lean::nat_mul(x_8, x_10);
lean::dec(x_10);
x_12 = lean::nat_add(x_11, x_4);
lean::dec(x_11);
x_13 = lean::nat_mul(x_8, x_12);
lean::dec(x_12);
x_14 = lean::nat_add(x_13, x_5);
lean::dec(x_13);
x_15 = l_Char_ofNat(x_14);
lean::dec(x_14);
x_16 = lean::box_uint32(x_15);
x_17 = lean::apply_2(x_7, lean::box(0), x_16);
return x_17;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
lean::closure_set(x_7, 3, x_6);
x_8 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
lean::inc(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__2), 6, 5);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_5);
lean::closure_set(x_6, 3, x_3);
lean::closure_set(x_6, 4, x_4);
x_7 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_4, x_6);
return x_7;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__3), 5, 4);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_2);
lean::closure_set(x_5, 3, x_3);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint32 x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::mk_nat_obj(16u);
x_7 = lean::nat_mul(x_6, x_2);
x_8 = lean::nat_add(x_7, x_3);
lean::dec(x_7);
x_9 = l_Char_ofNat(x_8);
lean::dec(x_8);
x_10 = lean::box_uint32(x_9);
x_11 = lean::apply_2(x_5, lean::box(0), x_10);
return x_11;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__6(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("quoted character");
return x_1;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint32 x_6) {
_start:
{
uint32 x_7; uint8 x_8; 
x_7 = 92;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32 x_9; uint8 x_10; 
x_9 = 34;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 39;
x_12 = x_6 == x_11;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 110;
x_14 = x_6 == x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 116;
x_16 = x_6 == x_15;
if (x_16 == 0)
{
uint32 x_17; uint8 x_18; 
x_17 = 120;
x_18 = x_6 == x_17;
if (x_18 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 117;
x_20 = x_6 == x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_21 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_22 = l_Lean_Parser_MonadParsec_unexpectedAt___rarg(x_1, lean::box(0), x_21, x_2);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_2);
lean::inc(x_4);
x_23 = l_Lean_Parser_parseHexDigit___rarg(x_3, x_1, x_4);
lean::inc(x_23);
lean::inc(x_5);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__4), 4, 3);
lean::closure_set(x_24, 0, x_4);
lean::closure_set(x_24, 1, x_5);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_2);
lean::inc(x_4);
x_26 = l_Lean_Parser_parseHexDigit___rarg(x_3, x_1, x_4);
lean::inc(x_26);
lean::inc(x_5);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__6), 4, 3);
lean::closure_set(x_27, 0, x_4);
lean::closure_set(x_27, 1, x_5);
lean::closure_set(x_27, 2, x_26);
x_28 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_26, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; uint32 x_31; obj* x_32; obj* x_33; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_4, 0);
lean::inc(x_29);
lean::dec(x_4);
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_31 = 9;
x_32 = lean::box_uint32(x_31);
x_33 = lean::apply_2(x_30, lean::box(0), x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; uint32 x_36; obj* x_37; obj* x_38; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_34 = lean::cnstr_get(x_4, 0);
lean::inc(x_34);
lean::dec(x_4);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_36 = 10;
x_37 = lean::box_uint32(x_36);
x_38 = lean::apply_2(x_35, lean::box(0), x_37);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
lean::dec(x_4);
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_41 = lean::box_uint32(x_11);
x_42 = lean::apply_2(x_40, lean::box(0), x_41);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_4, 0);
lean::inc(x_43);
lean::dec(x_4);
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
lean::dec(x_43);
x_45 = lean::box_uint32(x_9);
x_46 = lean::apply_2(x_44, lean::box(0), x_45);
return x_46;
}
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_4, 0);
lean::inc(x_47);
lean::dec(x_4);
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_49 = lean::box_uint32(x_7);
x_50 = lean::apply_2(x_48, lean::box(0), x_49);
return x_50;
}
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_MonadParsec_any___rarg(x_1, x_2);
lean::inc(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__7___boxed), 6, 5);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_5);
lean::closure_set(x_7, 2, x_1);
lean::closure_set(x_7, 3, x_3);
lean::closure_set(x_7, 4, x_4);
x_8 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
lean::inc(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg___lambda__8), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
lean::closure_set(x_8, 3, x_4);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_parseQuotedChar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseQuotedChar___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseQuotedChar___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseQuotedChar___rarg___lambda__5(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint32 x_7; obj* x_8; 
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseQuotedChar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseQuotedChar(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint32 x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::string_push(x_1, x_6);
x_8 = l_Lean_Parser_parseStringLiteralAux___main___rarg(x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint32 x_7) {
_start:
{
uint32 x_8; uint8 x_9; 
x_8 = 92;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
lean::dec(x_6);
x_10 = 34;
x_11 = x_7 == x_10;
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::string_push(x_1, x_7);
x_13 = l_Lean_Parser_parseStringLiteralAux___main___rarg(x_2, x_3, x_4, x_5, x_12);
lean::dec(x_5);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::apply_2(x_15, lean::box(0), x_1);
return x_16;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_17 = l_Lean_Parser_parseQuotedChar___rarg(x_2, x_3, x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_2);
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
x_19 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_Lean_Parser_MonadParsec_any___rarg(x_1, x_2);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2___boxed), 7, 6);
lean::closure_set(x_12, 0, x_5);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
lean::closure_set(x_12, 4, x_9);
lean::closure_set(x_12, 5, x_10);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; uint32 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_14, 4);
lean::inc(x_15);
x_16 = 34;
x_17 = l_Lean_Parser_MonadParsec_ch___rarg(x_1, x_2, x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
lean::dec(x_14);
x_19 = lean::apply_2(x_18, lean::box(0), x_5);
x_20 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_17, x_19);
return x_20;
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteralAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint32 x_7; obj* x_8; 
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint32 x_8; obj* x_9; 
x_8 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_parseStringLiteralAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseStringLiteralAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseStringLiteralAux___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseStringLiteralAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_parseStringLiteralAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteralAux___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseStringLiteralAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseStringLiteralAux(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_String_splitAux___main___closed__1;
x_6 = l_Lean_Parser_parseStringLiteralAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint32 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
x_12 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_13 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteral___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_3);
x_15 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_Lean_Parser_parseStringLiteral___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint32 x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = 34;
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_MonadParsec_ch___rarg(x_1, x_2, x_5);
lean::inc(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteral___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_parseStringLiteral(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteral___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_parseStringLiteral___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_parseStringLiteral___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_parseStringLiteral___rarg___lambda__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_Lean_Parser_parseStringLiteral___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseStringLiteral(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_parser_parsec(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_stringliteral(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_parseHexDigit___rarg___closed__1 = _init_l_Lean_Parser_parseHexDigit___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHexDigit___rarg___closed__1);
l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1 = _init_l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1();
lean::mark_persistent(l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1);
return w;
}
