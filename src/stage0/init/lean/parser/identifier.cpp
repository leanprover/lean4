// Lean compiler output
// Module: init.lean.parser.identifier
// Imports: init.data.char.basic init.lean.parser.parsec
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
uint8 l_Lean_isSubScriptAlnum(uint32);
obj* l_Lean_isIdRest___boxed(obj*);
obj* l_Lean_idEndEscape___boxed;
obj* l_Lean_Parser_idPartDefault___rarg___boxed(obj*, obj*, obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l_Lean_Parser_identifier___rarg(obj*, obj*, obj*);
uint8 l_Char_isAlphanum(uint32);
obj* l_Lean_isLetterLike___boxed(obj*);
obj* l_Lean_Parser_cppIdentifier___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
uint32 l_Lean_isLetterLike___closed__13;
obj* l_Lean_Parser_idPartDefault___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mkStringResult___rarg(obj*, obj*);
obj* l_Lean_isLetterLike___closed__12___boxed;
uint32 l_Lean_isSubScriptAlnum___closed__3;
obj* l_Lean_Parser_idPartEscaped___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
uint8 l_Lean_isIdRest(uint32);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isIdEndEscape(uint32);
uint32 l_Lean_isSubScriptAlnum___closed__2;
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_isLetterLike___closed__5___boxed;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___boxed(obj*, obj*);
obj* l_Lean_isLetterLike___closed__6___boxed;
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_isIdBeginEscape___boxed(obj*);
uint32 l_Lean_isLetterLike___closed__6;
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(obj*, obj*);
uint32 l_Lean_isLetterLike___closed__10;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(obj*, obj*, uint32);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_isLetterLike___closed__13___boxed;
obj* l_Lean_Parser_idPart(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(obj*, obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(obj*, obj*);
uint32 l_Lean_isLetterLike___closed__14;
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_isLetterLike___closed__9___boxed;
obj* l_Lean_idBeginEscape___boxed;
obj* l_Lean_isGreek___closed__2___boxed;
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2(obj*, obj*, uint32);
obj* l_Lean_isIdFirst___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3;
uint32 l_Lean_isLetterLike___closed__4;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___boxed(obj*, obj*, obj*);
uint32 l_Lean_isLetterLike___closed__5;
obj* l_Lean_Parser_identifier___rarg___closed__1;
uint32 l_Lean_isLetterLike___closed__12;
obj* l_Lean_Parser_cIdentifier___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_identifier(obj*, obj*);
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___rarg___lambda__1(obj*, obj*, obj*);
obj* l_String_Iterator_remaining___main(obj*);
uint32 l_Lean_isLetterLike___closed__11;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(obj*, obj*, obj*);
uint8 l_Lean_isLetterLike(uint32);
uint32 l_Lean_isSubScriptAlnum___closed__5;
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_identifier___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isIdBeginEscape(uint32);
uint32 l_Lean_isSubScriptAlnum___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier(obj*, obj*);
obj* l_Lean_isLetterLike___closed__2___boxed;
obj* l_String_Iterator_next___main(obj*);
uint32 l_Lean_isSubScriptAlnum___closed__4;
uint32 l_Lean_isLetterLike___closed__1;
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_isSubScriptAlnum___closed__6___boxed;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2(obj*, obj*, uint32);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(obj*);
obj* l_Lean_isSubScriptAlnum___closed__4___boxed;
obj* l_Lean_Parser_cIdentifier___boxed(obj*, obj*);
obj* l_Lean_isLetterLike___closed__14___boxed;
obj* l_Lean_Parser_cIdentifier(obj*, obj*);
uint32 l_Char_ofNat(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_idPartEscaped___rarg(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
uint32 l_Lean_idBeginEscape;
obj* l_Char_quoteCore(uint32);
obj* l_Lean_isLetterLike___closed__4___boxed;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(obj*, obj*);
uint32 l_Lean_isLetterLike___closed__9;
uint32 l_Lean_isLetterLike___closed__8;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_String_append___boxed(obj*, obj*);
obj* l_Lean_isLetterLike___closed__7___boxed;
obj* l_Lean_isIdFirst___closed__1___boxed;
uint32 l_Lean_isGreek___closed__2;
uint32 l_Lean_isLetterLike___closed__3;
obj* l_Lean_isGreek___closed__1___boxed;
extern obj* l_Lean_Parser_MonadParsec_try___rarg___closed__1;
obj* l_Lean_isSubScriptAlnum___closed__1___boxed;
uint32 l_Lean_isLetterLike___closed__2;
obj* l_Dlist_singleton___rarg(obj*, obj*);
obj* l_Lean_isLetterLike___closed__8___boxed;
obj* l_Lean_isLetterLike___closed__3___boxed;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_isSubScriptAlnum___closed__5___boxed;
obj* l_Lean_Parser_cIdentifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2;
obj* l_Lean_isSubScriptAlnum___closed__3___boxed;
uint32 l_Lean_isLetterLike___closed__7;
obj* l_Lean_Parser_identifier___boxed(obj*, obj*);
obj* l_Lean_isGreek___boxed(obj*);
obj* l_Lean_isLetterLike___closed__10___boxed;
obj* l_Lean_isSubScriptAlnum___closed__2___boxed;
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___boxed(obj*);
obj* l_Lean_isLetterLike___closed__11___boxed;
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_cIdentifier___rarg___closed__1;
obj* l_Lean_Parser_idPart___boxed(obj*, obj*);
uint32 l_Lean_Parser_identifier___rarg___lambda__1___closed__1;
uint32 l_Lean_isGreek___closed__1;
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_idPartEscaped(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_isIdEndEscape___boxed(obj*);
uint8 l_String_Iterator_hasNext___main(obj*);
obj* l_Lean_Parser_idPartDefault___rarg(obj*, obj*, obj*);
uint32 l_Lean_isSubScriptAlnum___closed__6;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_identifier___rarg___lambda__1___closed__1___boxed;
uint32 l_Lean_idEndEscape;
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_cppIdentifier___boxed(obj*, obj*);
obj* l_Lean_Parser_idPart___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(obj*, obj*, obj*);
uint32 l_Lean_isIdFirst___closed__1;
uint8 l_Lean_isIdFirst(uint32);
obj* l_Lean_isLetterLike___closed__1___boxed;
obj* l_Lean_isIdRest___closed__1___boxed;
uint8 l_Lean_isGreek(uint32);
obj* l_Lean_Parser_cIdentifier___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(obj*, obj*);
extern obj* l_String_Iterator_extract___main___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_MonadParsec_ch___rarg(obj*, obj*, uint32);
obj* l_Lean_Parser_idPart___rarg___closed__1;
uint32 l_Lean_isIdRest___closed__1;
obj* l_Lean_isSubScriptAlnum___boxed(obj*);
uint32 _init_l_Lean_isGreek___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
return x_14;
}
}
uint32 _init_l_Lean_isGreek___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
x_12 = x_11 + x_1;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_1;
return x_17;
}
}
uint8 l_Lean_isGreek(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Lean_isGreek___closed__1;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = l_Lean_isGreek___closed__2;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* _init_l_Lean_isGreek___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isGreek___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isGreek___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isGreek___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_isGreek___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isGreek(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_Lean_isLetterLike___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; uint32 x_22; uint32 x_23; uint32 x_24; uint32 x_25; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
x_16 = x_15 + x_15;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
x_19 = x_18 + x_1;
x_20 = x_19 + x_19;
x_21 = x_20 + x_1;
x_22 = x_21 + x_21;
x_23 = x_22 + x_1;
x_24 = x_23 + x_23;
x_25 = x_24 + x_24;
return x_25;
}
}
uint32 _init_l_Lean_isLetterLike___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; uint32 x_22; uint32 x_23; uint32 x_24; uint32 x_25; uint32 x_26; uint32 x_27; uint32 x_28; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
x_19 = x_18 + x_18;
x_20 = x_19 + x_1;
x_21 = x_20 + x_20;
x_22 = x_21 + x_1;
x_23 = x_22 + x_22;
x_24 = x_23 + x_1;
x_25 = x_24 + x_24;
x_26 = x_25 + x_1;
x_27 = x_26 + x_26;
x_28 = x_27 + x_1;
return x_28;
}
}
uint32 _init_l_Lean_isLetterLike___closed__3() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__4() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_1;
x_19 = x_18 + x_18;
x_20 = x_19 + x_1;
return x_20;
}
}
uint32 _init_l_Lean_isLetterLike___closed__5() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_16;
return x_17;
}
}
uint32 _init_l_Lean_isLetterLike___closed__6() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; uint32 x_22; uint32 x_23; uint32 x_24; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
x_16 = x_15 + x_15;
x_17 = x_16 + x_1;
x_18 = x_17 + x_17;
x_19 = x_18 + x_1;
x_20 = x_19 + x_19;
x_21 = x_20 + x_1;
x_22 = x_21 + x_21;
x_23 = x_22 + x_1;
x_24 = x_23 + x_23;
return x_24;
}
}
uint32 _init_l_Lean_isLetterLike___closed__7() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__8() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_1;
return x_18;
}
}
uint32 _init_l_Lean_isLetterLike___closed__9() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__10() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
return x_13;
}
}
uint32 _init_l_Lean_isLetterLike___closed__11() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__12() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__13() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_1;
x_8 = x_7 + x_7;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
return x_15;
}
}
uint32 _init_l_Lean_isLetterLike___closed__14() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_1;
x_11 = x_10 + x_10;
x_12 = x_11 + x_1;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
x_16 = x_15 + x_15;
x_17 = x_16 + x_1;
return x_17;
}
}
uint8 l_Lean_isLetterLike(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; uint8 x_5; uint8 x_7; uint8 x_9; uint8 x_11; uint32 x_13; uint8 x_14; 
x_13 = l_Lean_isLetterLike___closed__12;
x_14 = x_13 <= x_0;
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
x_11 = x_15;
goto lbl_12;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = l_Lean_isLetterLike___closed__13;
x_17 = x_0 <= x_16;
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 0;
x_11 = x_18;
goto lbl_12;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = l_Lean_isLetterLike___closed__14;
x_20 = x_0 == x_19;
if (x_20 == 0)
{
uint8 x_21; 
x_21 = 1;
x_11 = x_21;
goto lbl_12;
}
else
{
uint8 x_22; 
x_22 = 0;
x_11 = x_22;
goto lbl_12;
}
}
}
lbl_2:
{
uint32 x_23; uint8 x_24; 
x_23 = l_Lean_isLetterLike___closed__1;
x_24 = x_23 <= x_0;
if (x_24 == 0)
{
if (x_1 == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = l_Lean_isLetterLike___closed__2;
x_26 = x_0 <= x_25;
if (x_26 == 0)
{
return x_1;
}
else
{
uint8 x_27; 
x_27 = 1;
return x_27;
}
}
}
lbl_4:
{
uint32 x_28; uint8 x_29; 
x_28 = l_Lean_isLetterLike___closed__3;
x_29 = x_28 <= x_0;
if (x_29 == 0)
{
if (x_3 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
}
else
{
uint32 x_30; uint8 x_31; 
x_30 = l_Lean_isLetterLike___closed__4;
x_31 = x_0 <= x_30;
if (x_31 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
uint8 x_32; 
x_32 = 1;
return x_32;
}
}
}
lbl_6:
{
uint32 x_33; uint8 x_34; 
x_33 = l_Lean_isLetterLike___closed__5;
x_34 = x_33 <= x_0;
if (x_34 == 0)
{
if (x_5 == 0)
{
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
}
else
{
uint32 x_35; uint8 x_36; 
x_35 = l_Lean_isLetterLike___closed__6;
x_36 = x_0 <= x_35;
if (x_36 == 0)
{
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
uint8 x_37; 
x_37 = 1;
return x_37;
}
}
}
lbl_8:
{
uint32 x_38; uint8 x_39; 
x_38 = l_Lean_isLetterLike___closed__7;
x_39 = x_38 <= x_0;
if (x_39 == 0)
{
if (x_7 == 0)
{
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = l_Lean_isLetterLike___closed__8;
x_41 = x_0 <= x_40;
if (x_41 == 0)
{
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
uint8 x_42; 
x_42 = 1;
return x_42;
}
}
}
lbl_10:
{
if (x_9 == 0)
{
x_5 = x_9;
goto lbl_6;
}
else
{
if (x_9 == 0)
{
x_3 = x_9;
goto lbl_4;
}
else
{
if (x_9 == 0)
{
x_1 = x_9;
goto lbl_2;
}
else
{
return x_9;
}
}
}
}
lbl_12:
{
uint8 x_43; uint8 x_45; 
if (x_11 == 0)
{
uint32 x_47; uint8 x_48; 
x_47 = l_Lean_isGreek___closed__1;
x_48 = x_47 <= x_0;
if (x_48 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
else
{
x_43 = x_11;
goto lbl_44;
}
}
else
{
x_45 = x_11;
goto lbl_46;
}
}
else
{
if (x_11 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
else
{
x_43 = x_11;
goto lbl_44;
}
}
else
{
x_45 = x_11;
goto lbl_46;
}
}
}
else
{
uint32 x_49; uint8 x_50; 
x_49 = l_Lean_isLetterLike___closed__11;
x_50 = x_0 <= x_49;
if (x_50 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
else
{
x_43 = x_11;
goto lbl_44;
}
}
else
{
x_45 = x_11;
goto lbl_46;
}
}
else
{
uint8 x_51; 
x_51 = 1;
x_45 = x_51;
goto lbl_46;
}
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
lbl_44:
{
uint32 x_52; uint8 x_53; 
x_52 = l_Lean_isLetterLike___closed__9;
x_53 = x_0 == x_52;
if (x_53 == 0)
{
if (x_43 == 0)
{
x_7 = x_43;
goto lbl_8;
}
else
{
x_9 = x_43;
goto lbl_10;
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
lbl_46:
{
uint32 x_54; uint8 x_55; 
x_54 = l_Lean_isLetterLike___closed__10;
x_55 = x_0 == x_54;
if (x_55 == 0)
{
if (x_45 == 0)
{
if (x_45 == 0)
{
x_7 = x_45;
goto lbl_8;
}
else
{
x_9 = x_45;
goto lbl_10;
}
}
else
{
x_43 = x_45;
goto lbl_44;
}
}
else
{
if (x_11 == 0)
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
else
{
x_43 = x_11;
goto lbl_44;
}
}
}
}
}
}
obj* _init_l_Lean_isLetterLike___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__4___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__4;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__5___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__5;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__6___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__6;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__7___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__7;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__8___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__8;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__9___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__9;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__10___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__10;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__11___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__11;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__12___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__12;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__13___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__13;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isLetterLike___closed__14___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isLetterLike___closed__14;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_isLetterLike___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isLetterLike(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__1() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_16;
x_18 = x_17 + x_1;
x_19 = x_18 + x_18;
return x_19;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__2() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_1;
x_4 = x_3 + x_3;
x_5 = x_4 + x_1;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
x_19 = x_18 + x_1;
x_20 = x_19 + x_19;
return x_20;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__3() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_1;
x_13 = x_12 + x_12;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
return x_16;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__4() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_1;
x_13 = x_12 + x_12;
x_14 = x_13 + x_1;
x_15 = x_14 + x_14;
x_16 = x_15 + x_1;
x_17 = x_16 + x_16;
x_18 = x_17 + x_17;
return x_18;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__5() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; uint32 x_18; uint32 x_19; uint32 x_20; uint32 x_21; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_7;
x_9 = x_8 + x_1;
x_10 = x_9 + x_9;
x_11 = x_10 + x_1;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_1;
x_16 = x_15 + x_15;
x_17 = x_16 + x_1;
x_18 = x_17 + x_17;
x_19 = x_18 + x_1;
x_20 = x_19 + x_19;
x_21 = x_20 + x_1;
return x_21;
}
}
uint32 _init_l_Lean_isSubScriptAlnum___closed__6() {
_start:
{
obj* x_0; uint32 x_1; uint32 x_2; uint32 x_3; uint32 x_4; uint32 x_5; uint32 x_6; uint32 x_7; uint32 x_8; uint32 x_9; uint32 x_10; uint32 x_11; uint32 x_12; uint32 x_13; uint32 x_14; uint32 x_15; uint32 x_16; uint32 x_17; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
x_2 = x_1 + x_1;
x_3 = x_2 + x_2;
x_4 = x_3 + x_3;
x_5 = x_4 + x_4;
x_6 = x_5 + x_5;
x_7 = x_6 + x_6;
x_8 = x_7 + x_1;
x_9 = x_8 + x_8;
x_10 = x_9 + x_9;
x_11 = x_10 + x_10;
x_12 = x_11 + x_11;
x_13 = x_12 + x_1;
x_14 = x_13 + x_13;
x_15 = x_14 + x_14;
x_16 = x_15 + x_15;
x_17 = x_16 + x_1;
return x_17;
}
}
uint8 l_Lean_isSubScriptAlnum(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; uint32 x_5; uint8 x_6; 
x_5 = l_Lean_isSubScriptAlnum___closed__5;
x_6 = x_5 <= x_0;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
x_3 = x_7;
goto lbl_4;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_Lean_isSubScriptAlnum___closed__6;
x_9 = x_0 <= x_8;
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
x_3 = x_10;
goto lbl_4;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
lbl_2:
{
uint32 x_12; uint8 x_13; 
x_12 = l_Lean_isSubScriptAlnum___closed__1;
x_13 = x_12 <= x_0;
if (x_13 == 0)
{
if (x_1 == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = l_Lean_isSubScriptAlnum___closed__2;
x_15 = x_0 <= x_14;
if (x_15 == 0)
{
return x_1;
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
lbl_4:
{
uint32 x_17; uint8 x_18; 
x_17 = l_Lean_isSubScriptAlnum___closed__3;
x_18 = x_17 <= x_0;
if (x_18 == 0)
{
if (x_3 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = l_Lean_isSubScriptAlnum___closed__4;
x_20 = x_0 <= x_19;
if (x_20 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
uint8 x_21; 
x_21 = 1;
return x_21;
}
}
}
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__2___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__2;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__4___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__4;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__5___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__5;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_Lean_isSubScriptAlnum___closed__6___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isSubScriptAlnum___closed__6;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_isSubScriptAlnum___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isSubScriptAlnum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_Lean_isIdFirst___closed__1() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(95u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
uint8 l_Lean_isIdFirst(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Char_isAlpha(x_0);
if (x_1 == 0)
{
uint32 x_2; uint8 x_3; 
x_2 = l_Lean_isIdFirst___closed__1;
x_3 = x_0 == x_2;
if (x_3 == 0)
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = l_Lean_isLetterLike(x_0);
return x_4;
}
else
{
return x_1;
}
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
else
{
if (x_1 == 0)
{
uint8 x_6; 
x_6 = l_Lean_isLetterLike(x_0);
return x_6;
}
else
{
return x_1;
}
}
}
}
obj* _init_l_Lean_isIdFirst___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isIdFirst___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_isIdFirst___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isIdFirst(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_Lean_isIdRest___closed__1() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(39u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
uint8 l_Lean_isIdRest(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; 
x_3 = l_Char_isAlphanum(x_0);
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = l_Lean_isIdFirst___closed__1;
x_5 = x_0 == x_4;
if (x_5 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
uint8 x_6; 
x_6 = l_Lean_isLetterLike(x_0);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = l_Lean_isSubScriptAlnum(x_0);
return x_7;
}
else
{
return x_6;
}
}
else
{
if (x_3 == 0)
{
uint8 x_8; 
x_8 = l_Lean_isSubScriptAlnum(x_0);
return x_8;
}
else
{
return x_3;
}
}
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
uint8 x_10; 
x_10 = l_Lean_isLetterLike(x_0);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = l_Lean_isSubScriptAlnum(x_0);
return x_11;
}
else
{
return x_10;
}
}
else
{
if (x_3 == 0)
{
uint8 x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_0);
return x_12;
}
else
{
return x_3;
}
}
}
}
lbl_2:
{
uint32 x_13; uint8 x_14; 
x_13 = l_Lean_isIdRest___closed__1;
x_14 = x_0 == x_13;
if (x_14 == 0)
{
if (x_1 == 0)
{
uint8 x_15; 
x_15 = l_Lean_isLetterLike(x_0);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = l_Lean_isSubScriptAlnum(x_0);
return x_16;
}
else
{
return x_15;
}
}
else
{
if (x_1 == 0)
{
uint8 x_17; 
x_17 = l_Lean_isSubScriptAlnum(x_0);
return x_17;
}
else
{
return x_1;
}
}
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
}
}
obj* _init_l_Lean_isIdRest___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_isIdRest___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_isIdRest___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isIdRest(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_Lean_idBeginEscape() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(171u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
obj* _init_l_Lean_idBeginEscape___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_idBeginEscape;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint32 _init_l_Lean_idEndEscape() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(187u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
obj* _init_l_Lean_idEndEscape___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_idEndEscape;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint8 l_Lean_isIdBeginEscape(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Lean_idBeginEscape;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Lean_isIdBeginEscape___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isIdBeginEscape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_isIdEndEscape(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_Lean_idEndEscape;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Lean_isIdEndEscape___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_isIdEndEscape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_Iterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_idPartDefault___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_5);
lean::inc(x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_Lean_Parser_idPartDefault(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_idPartDefault___rarg___lambda__2(x_0, x_1, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPartDefault___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_idPartDefault___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_idPartDefault(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_Iterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Lean_isIdEndEscape(x_10);
if (x_11 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_13 = lean::box_uint32(x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_13);
x_15 = lean::apply_2(x_1, lean::box(0), x_14);
return x_15;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
lean::dec(x_2);
x_18 = l_Char_quoteCore(x_10);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_22 = lean::string_append(x_20, x_19);
x_23 = lean::box(0);
x_24 = l_mjoin___rarg___closed__1;
x_25 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_22, x_24, x_23, x_23);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_4);
x_8 = lean::apply_2(x_4, lean::box(0), x_6);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_4);
lean::inc(x_2);
x_12 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_8, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
x_14 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_idPartEscaped___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; uint32 x_11; obj* x_14; obj* x_17; obj* x_18; uint32 x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 4);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_idBeginEscape;
lean::inc(x_1);
lean::inc(x_0);
x_14 = l_Lean_Parser_MonadParsec_ch___rarg(x_0, x_1, x_11);
lean::inc(x_1);
lean::inc(x_0);
x_17 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(x_0, x_1);
x_18 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_14, x_17);
x_19 = l_Lean_idEndEscape;
x_20 = l_Lean_Parser_MonadParsec_ch___rarg(x_0, x_1, x_19);
x_21 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_18, x_20);
return x_21;
}
}
obj* l_Lean_Parser_idPartEscaped(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartEscaped___rarg), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(x_0, x_1, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_idPartEscaped___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_idPartEscaped(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_idPart___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_isIdBeginEscape___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_idPart___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = l_Lean_Parser_idPartEscaped___rarg(x_0, x_1, x_2);
lean::inc(x_1);
lean::inc(x_0);
x_9 = l_Lean_Parser_idPartDefault___rarg(x_0, x_1, x_2);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_Lean_Parser_MonadParsec_curr___rarg(x_0, x_1);
x_22 = l_Lean_Parser_idPart___rarg___closed__1;
x_23 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_22, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_6);
x_25 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
obj* l_Lean_Parser_idPart(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPart___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_idPart___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_idPart(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_3);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_16, 0, x_3);
lean::closure_set(x_16, 1, x_0);
lean::closure_set(x_16, 2, x_1);
lean::closure_set(x_16, 3, x_2);
lean::closure_set(x_16, 4, x_8);
x_17 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_2, x_16);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_3);
x_25 = lean::apply_3(x_9, lean::box(0), x_17, x_24);
return x_25;
}
else
{
obj* x_28; obj* x_31; obj* x_34; 
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::apply_2(x_31, lean::box(0), x_3);
return x_34;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_String_Iterator_remaining___main(x_4);
x_6 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_2);
lean::closure_set(x_12, 2, x_4);
lean::closure_set(x_12, 3, x_3);
x_13 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg), 5, 0);
return x_2;
}
}
uint32 _init_l_Lean_Parser_identifier___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(46u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
obj* l_Lean_Parser_identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; uint32 x_12; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::box(0);
x_6 = lean_name_mk_string(x_5, x_4);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::dec(x_7);
x_12 = l_Lean_Parser_identifier___rarg___lambda__1___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_15 = l_Lean_Parser_MonadParsec_ch___rarg(x_1, x_2, x_12);
x_16 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_15, x_3);
x_17 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(x_1, x_2, x_0, x_6, x_16);
return x_17;
}
}
obj* _init_l_Lean_Parser_identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_Lean_Parser_idPart___rarg(x_0, x_1, x_2);
lean::inc(x_8);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identifier___rarg___lambda__1), 5, 4);
lean::closure_set(x_11, 0, x_2);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_1);
lean::closure_set(x_11, 3, x_8);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_13);
x_18 = lean::apply_3(x_13, lean::box(0), x_16, x_12);
x_19 = l_Lean_Parser_identifier___rarg___closed__1;
x_20 = lean::apply_3(x_13, lean::box(0), x_19, x_18);
return x_20;
}
}
obj* l_Lean_Parser_identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identifier___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_identifier___rarg___lambda__1___closed__1___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_Lean_Parser_identifier___rarg___lambda__1___closed__1;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_Lean_Parser_identifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_identifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; uint8 x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = l_String_Iterator_curr___main(x_2);
x_12 = l_Char_isAlphanum(x_11);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = l_Lean_isIdFirst___closed__1;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
if (x_12 == 0)
{
obj* x_16; 
lean::dec(x_9);
x_16 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::string_push(x_1, x_11);
x_18 = l_String_Iterator_next___main(x_2);
x_0 = x_9;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::string_push(x_1, x_11);
x_21 = l_String_Iterator_next___main(x_2);
x_0 = x_9;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
else
{
if (x_12 == 0)
{
obj* x_24; 
lean::dec(x_9);
x_24 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::string_push(x_1, x_11);
x_26 = l_String_Iterator_next___main(x_2);
x_0 = x_9;
x_1 = x_25;
x_2 = x_26;
goto _start;
}
}
}
}
else
{
obj* x_29; 
lean::dec(x_0);
x_29 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_29;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Char_isAlpha(x_10);
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = l_Lean_isIdFirst___closed__1;
x_13 = x_10 == x_12;
if (x_13 == 0)
{
if (x_11 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_2);
x_16 = l_Char_quoteCore(x_10);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean::string_append(x_17, x_16);
lean::dec(x_16);
x_20 = lean::string_append(x_18, x_17);
x_21 = lean::box(0);
x_22 = l_mjoin___rarg___closed__1;
x_23 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_20, x_22, x_21, x_21);
return x_23;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
x_25 = lean::box_uint32(x_10);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_26, 0, x_2);
lean::closure_set(x_26, 1, x_25);
x_27 = lean::apply_2(x_1, lean::box(0), x_26);
return x_27;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_29 = lean::box_uint32(x_10);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_30, 0, x_2);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::apply_2(x_1, lean::box(0), x_30);
return x_31;
}
}
else
{
if (x_11 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
lean::dec(x_2);
x_34 = l_Char_quoteCore(x_10);
x_35 = l_Char_HasRepr___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_38 = lean::string_append(x_36, x_35);
x_39 = lean::box(0);
x_40 = l_mjoin___rarg___closed__1;
x_41 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_38, x_40, x_39, x_39);
return x_41;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_0);
x_43 = lean::box_uint32(x_10);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_44, 0, x_2);
lean::closure_set(x_44, 1, x_43);
x_45 = lean::apply_2(x_1, lean::box(0), x_44);
return x_45;
}
}
}
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_cIdentifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_cIdentifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_5);
lean::inc(x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_13, x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_20 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_17);
x_22 = lean::apply_3(x_17, lean::box(0), x_20, x_16);
x_23 = l_Lean_Parser_cIdentifier___rarg___closed__1;
x_24 = lean::apply_3(x_17, lean::box(0), x_23, x_22);
return x_24;
}
}
obj* l_Lean_Parser_cIdentifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_cIdentifier___rarg___lambda__2(x_0, x_1, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_cIdentifier___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_cIdentifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_cIdentifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = l_String_Iterator_extract___main___closed__1;
x_8 = l_List_foldl___main___at_String_join___spec__1(x_7, x_6);
lean::dec(x_6);
x_10 = lean::apply_2(x_3, lean::box(0), x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("::");
return x_0;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("::");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_append___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_15 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1;
x_16 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2;
lean::inc(x_2);
lean::inc(x_1);
x_19 = l_Lean_Parser_MonadParsec_strCore___rarg(x_1, x_2, x_15, x_16);
x_20 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3;
x_21 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_20, x_19);
x_22 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_21, x_3);
x_23 = l_Lean_Parser_MonadParsec_many___rarg(x_1, x_2, lean::box(0), x_0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg___lambda__1), 3, 2);
lean::closure_set(x_24, 0, x_6);
lean::closure_set(x_24, 1, x_5);
x_25 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C++ identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_Lean_Parser_cIdentifier___rarg(x_0, x_1, x_2);
lean::inc(x_3);
lean::inc(x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg___lambda__2), 6, 5);
lean::closure_set(x_11, 0, x_2);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_1);
lean::closure_set(x_11, 3, x_7);
lean::closure_set(x_11, 4, x_3);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_7, x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_13);
x_18 = lean::apply_3(x_13, lean::box(0), x_16, x_12);
x_19 = l_Lean_Parser_cppIdentifier___rarg___closed__1;
x_20 = lean::apply_3(x_13, lean::box(0), x_19, x_18);
return x_20;
}
}
obj* l_Lean_Parser_cppIdentifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_cppIdentifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_cppIdentifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_char_basic(obj*);
obj* initialize_init_lean_parser_parsec(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_identifier(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
 l_Lean_isGreek___closed__1 = _init_l_Lean_isGreek___closed__1();
 l_Lean_isGreek___closed__2 = _init_l_Lean_isGreek___closed__2();
 l_Lean_isGreek___closed__1___boxed = _init_l_Lean_isGreek___closed__1___boxed();
lean::mark_persistent(l_Lean_isGreek___closed__1___boxed);
 l_Lean_isGreek___closed__2___boxed = _init_l_Lean_isGreek___closed__2___boxed();
lean::mark_persistent(l_Lean_isGreek___closed__2___boxed);
 l_Lean_isLetterLike___closed__1 = _init_l_Lean_isLetterLike___closed__1();
 l_Lean_isLetterLike___closed__2 = _init_l_Lean_isLetterLike___closed__2();
 l_Lean_isLetterLike___closed__3 = _init_l_Lean_isLetterLike___closed__3();
 l_Lean_isLetterLike___closed__4 = _init_l_Lean_isLetterLike___closed__4();
 l_Lean_isLetterLike___closed__5 = _init_l_Lean_isLetterLike___closed__5();
 l_Lean_isLetterLike___closed__6 = _init_l_Lean_isLetterLike___closed__6();
 l_Lean_isLetterLike___closed__7 = _init_l_Lean_isLetterLike___closed__7();
 l_Lean_isLetterLike___closed__8 = _init_l_Lean_isLetterLike___closed__8();
 l_Lean_isLetterLike___closed__9 = _init_l_Lean_isLetterLike___closed__9();
 l_Lean_isLetterLike___closed__10 = _init_l_Lean_isLetterLike___closed__10();
 l_Lean_isLetterLike___closed__11 = _init_l_Lean_isLetterLike___closed__11();
 l_Lean_isLetterLike___closed__12 = _init_l_Lean_isLetterLike___closed__12();
 l_Lean_isLetterLike___closed__13 = _init_l_Lean_isLetterLike___closed__13();
 l_Lean_isLetterLike___closed__14 = _init_l_Lean_isLetterLike___closed__14();
 l_Lean_isLetterLike___closed__1___boxed = _init_l_Lean_isLetterLike___closed__1___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__1___boxed);
 l_Lean_isLetterLike___closed__2___boxed = _init_l_Lean_isLetterLike___closed__2___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__2___boxed);
 l_Lean_isLetterLike___closed__3___boxed = _init_l_Lean_isLetterLike___closed__3___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__3___boxed);
 l_Lean_isLetterLike___closed__4___boxed = _init_l_Lean_isLetterLike___closed__4___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__4___boxed);
 l_Lean_isLetterLike___closed__5___boxed = _init_l_Lean_isLetterLike___closed__5___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__5___boxed);
 l_Lean_isLetterLike___closed__6___boxed = _init_l_Lean_isLetterLike___closed__6___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__6___boxed);
 l_Lean_isLetterLike___closed__7___boxed = _init_l_Lean_isLetterLike___closed__7___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__7___boxed);
 l_Lean_isLetterLike___closed__8___boxed = _init_l_Lean_isLetterLike___closed__8___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__8___boxed);
 l_Lean_isLetterLike___closed__9___boxed = _init_l_Lean_isLetterLike___closed__9___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__9___boxed);
 l_Lean_isLetterLike___closed__10___boxed = _init_l_Lean_isLetterLike___closed__10___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__10___boxed);
 l_Lean_isLetterLike___closed__11___boxed = _init_l_Lean_isLetterLike___closed__11___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__11___boxed);
 l_Lean_isLetterLike___closed__12___boxed = _init_l_Lean_isLetterLike___closed__12___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__12___boxed);
 l_Lean_isLetterLike___closed__13___boxed = _init_l_Lean_isLetterLike___closed__13___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__13___boxed);
 l_Lean_isLetterLike___closed__14___boxed = _init_l_Lean_isLetterLike___closed__14___boxed();
lean::mark_persistent(l_Lean_isLetterLike___closed__14___boxed);
 l_Lean_isSubScriptAlnum___closed__1 = _init_l_Lean_isSubScriptAlnum___closed__1();
 l_Lean_isSubScriptAlnum___closed__2 = _init_l_Lean_isSubScriptAlnum___closed__2();
 l_Lean_isSubScriptAlnum___closed__3 = _init_l_Lean_isSubScriptAlnum___closed__3();
 l_Lean_isSubScriptAlnum___closed__4 = _init_l_Lean_isSubScriptAlnum___closed__4();
 l_Lean_isSubScriptAlnum___closed__5 = _init_l_Lean_isSubScriptAlnum___closed__5();
 l_Lean_isSubScriptAlnum___closed__6 = _init_l_Lean_isSubScriptAlnum___closed__6();
 l_Lean_isSubScriptAlnum___closed__1___boxed = _init_l_Lean_isSubScriptAlnum___closed__1___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__1___boxed);
 l_Lean_isSubScriptAlnum___closed__2___boxed = _init_l_Lean_isSubScriptAlnum___closed__2___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__2___boxed);
 l_Lean_isSubScriptAlnum___closed__3___boxed = _init_l_Lean_isSubScriptAlnum___closed__3___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__3___boxed);
 l_Lean_isSubScriptAlnum___closed__4___boxed = _init_l_Lean_isSubScriptAlnum___closed__4___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__4___boxed);
 l_Lean_isSubScriptAlnum___closed__5___boxed = _init_l_Lean_isSubScriptAlnum___closed__5___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__5___boxed);
 l_Lean_isSubScriptAlnum___closed__6___boxed = _init_l_Lean_isSubScriptAlnum___closed__6___boxed();
lean::mark_persistent(l_Lean_isSubScriptAlnum___closed__6___boxed);
 l_Lean_isIdFirst___closed__1 = _init_l_Lean_isIdFirst___closed__1();
 l_Lean_isIdFirst___closed__1___boxed = _init_l_Lean_isIdFirst___closed__1___boxed();
lean::mark_persistent(l_Lean_isIdFirst___closed__1___boxed);
 l_Lean_isIdRest___closed__1 = _init_l_Lean_isIdRest___closed__1();
 l_Lean_isIdRest___closed__1___boxed = _init_l_Lean_isIdRest___closed__1___boxed();
lean::mark_persistent(l_Lean_isIdRest___closed__1___boxed);
 l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
 l_Lean_idBeginEscape___boxed = _init_l_Lean_idBeginEscape___boxed();
lean::mark_persistent(l_Lean_idBeginEscape___boxed);
 l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
 l_Lean_idEndEscape___boxed = _init_l_Lean_idEndEscape___boxed();
lean::mark_persistent(l_Lean_idEndEscape___boxed);
 l_Lean_Parser_idPart___rarg___closed__1 = _init_l_Lean_Parser_idPart___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_idPart___rarg___closed__1);
 l_Lean_Parser_identifier___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_identifier___rarg___lambda__1___closed__1();
 l_Lean_Parser_identifier___rarg___closed__1 = _init_l_Lean_Parser_identifier___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_identifier___rarg___closed__1);
 l_Lean_Parser_identifier___rarg___lambda__1___closed__1___boxed = _init_l_Lean_Parser_identifier___rarg___lambda__1___closed__1___boxed();
lean::mark_persistent(l_Lean_Parser_identifier___rarg___lambda__1___closed__1___boxed);
 l_Lean_Parser_cIdentifier___rarg___closed__1 = _init_l_Lean_Parser_cIdentifier___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_cIdentifier___rarg___closed__1);
 l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1 = _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1);
 l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2 = _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2);
 l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3 = _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3);
 l_Lean_Parser_cppIdentifier___rarg___closed__1 = _init_l_Lean_Parser_cppIdentifier___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_cppIdentifier___rarg___closed__1);
return w;
}
