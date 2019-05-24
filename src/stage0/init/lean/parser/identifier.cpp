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
obj* l_Lean_Parser_idPartDefault___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_identifier___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__mkStringResult___rarg(obj*, obj*);
uint8 l_Char_isAlphanum(uint32);
obj* l_Lean_isLetterLike___boxed(obj*);
obj* l_Lean_Parser_cppIdentifier___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___boxed(obj*, obj*);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_idPartEscaped___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
uint8 l_Lean_isIdRest(uint32);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___boxed(obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_isIdBeginEscape___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(obj*, obj*, uint32);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_idPart(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(obj*, obj*);
uint8 l_Char_isAlpha(uint32);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2(obj*, obj*, uint32);
obj* l_Lean_isIdFirst___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_identifier___rarg___closed__1;
obj* l_Lean_Parser_cIdentifier___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_identifier(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(obj*);
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(obj*, obj*, obj*);
uint8 l_Lean_isLetterLike(uint32);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_identifier___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(obj*, obj*, obj*);
uint8 l_Lean_isIdBeginEscape(uint32);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2(obj*, obj*, uint32);
uint8 l_UInt32_decLe(uint32, uint32);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj*);
obj* l_Lean_Parser_cIdentifier___boxed(obj*, obj*);
obj* l_Lean_Parser_cIdentifier(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_idPartEscaped___rarg(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
uint32 l_Lean_idBeginEscape;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj*, obj*, obj*);
obj* l_Char_quoteCore(uint32);
uint8 l_String_OldIterator_hasNext___main(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_String_append___boxed(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_try___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Parser_cppIdentifier___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_cIdentifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2;
obj* l_Lean_Parser_identifier___boxed(obj*, obj*);
obj* l_Lean_isGreek___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___boxed(obj*);
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_cIdentifier___rarg___closed__1;
obj* l_Lean_Parser_idPart___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_idPartEscaped(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_isIdEndEscape___boxed(obj*);
obj* l_Lean_Parser_idPartDefault___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1(obj*, obj*, obj*);
uint32 l_Lean_idEndEscape;
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_cppIdentifier___boxed(obj*, obj*);
obj* l_Lean_Parser_idPart___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isIdFirst(uint32);
uint8 l_Lean_isGreek(uint32);
obj* l_Lean_Parser_cIdentifier___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_MonadParsec_ch___rarg(obj*, obj*, uint32);
obj* l_Lean_Parser_idPart___rarg___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_isSubScriptAlnum___boxed(obj*);
uint8 l_Lean_isGreek(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = 913;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32 x_5; uint8 x_6; 
x_5 = 989;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
obj* l_Lean_isGreek___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isGreek(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isLetterLike(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; uint8 x_18; uint8 x_25; uint8 x_32; 
x_2 = 945;
x_32 = x_2 <= x_1;
if (x_32 == 0)
{
uint32 x_33; uint8 x_34; 
x_33 = 913;
x_34 = x_33 <= x_1;
if (x_34 == 0)
{
uint8 x_35; 
x_35 = 0;
x_25 = x_35;
goto block_31;
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 937;
x_37 = x_1 <= x_36;
if (x_37 == 0)
{
uint8 x_38; 
x_38 = 0;
x_25 = x_38;
goto block_31;
}
else
{
uint32 x_39; uint8 x_40; 
x_39 = 928;
x_40 = x_1 == x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = 931;
x_42 = x_1 == x_41;
if (x_42 == 0)
{
uint8 x_43; 
x_43 = 1;
return x_43;
}
else
{
uint8 x_44; 
x_44 = 0;
x_25 = x_44;
goto block_31;
}
}
else
{
uint8 x_45; 
x_45 = 0;
x_25 = x_45;
goto block_31;
}
}
}
}
else
{
uint32 x_46; uint8 x_47; 
x_46 = 969;
x_47 = x_1 <= x_46;
if (x_47 == 0)
{
uint32 x_48; uint8 x_49; 
x_48 = 913;
x_49 = x_48 <= x_1;
if (x_49 == 0)
{
uint8 x_50; 
x_50 = 0;
x_25 = x_50;
goto block_31;
}
else
{
uint32 x_51; uint8 x_52; 
x_51 = 937;
x_52 = x_1 <= x_51;
if (x_52 == 0)
{
uint8 x_53; 
x_53 = 0;
x_25 = x_53;
goto block_31;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = 928;
x_55 = x_1 == x_54;
if (x_55 == 0)
{
uint32 x_56; uint8 x_57; 
x_56 = 931;
x_57 = x_1 == x_56;
if (x_57 == 0)
{
uint8 x_58; 
x_58 = 1;
return x_58;
}
else
{
uint8 x_59; 
x_59 = 0;
x_25 = x_59;
goto block_31;
}
}
else
{
uint8 x_60; 
x_60 = 0;
x_25 = x_60;
goto block_31;
}
}
}
}
else
{
uint32 x_61; uint8 x_62; uint8 x_75; 
x_61 = 955;
x_75 = x_1 == x_61;
if (x_75 == 0)
{
uint8 x_76; 
x_76 = 1;
x_62 = x_76;
goto block_74;
}
else
{
uint8 x_77; 
x_77 = 0;
x_62 = x_77;
goto block_74;
}
block_74:
{
if (x_62 == 0)
{
uint32 x_63; uint8 x_64; 
x_63 = 913;
x_64 = x_63 <= x_1;
if (x_64 == 0)
{
x_25 = x_62;
goto block_31;
}
else
{
uint32 x_65; uint8 x_66; 
x_65 = 937;
x_66 = x_1 <= x_65;
if (x_66 == 0)
{
x_25 = x_62;
goto block_31;
}
else
{
uint32 x_67; uint8 x_68; 
x_67 = 928;
x_68 = x_1 == x_67;
if (x_68 == 0)
{
uint32 x_69; uint8 x_70; 
x_69 = 931;
x_70 = x_1 == x_69;
if (x_70 == 0)
{
uint8 x_71; 
x_71 = 1;
return x_71;
}
else
{
uint8 x_72; 
x_72 = 0;
x_25 = x_72;
goto block_31;
}
}
else
{
x_25 = x_62;
goto block_31;
}
}
}
}
else
{
uint8 x_73; 
x_73 = 1;
return x_73;
}
}
}
}
block_17:
{
uint32 x_4; uint8 x_5; 
x_4 = 8448;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = 119964;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = 120223;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = 8527;
x_11 = x_1 <= x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 119964;
x_13 = x_12 <= x_1;
if (x_13 == 0)
{
return x_11;
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 120223;
x_15 = x_1 <= x_14;
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
block_24:
{
uint32 x_19; uint8 x_20; 
x_19 = 7936;
x_20 = x_19 <= x_1;
if (x_20 == 0)
{
x_3 = x_18;
goto block_17;
}
else
{
uint32 x_21; uint8 x_22; 
x_21 = 8190;
x_22 = x_1 <= x_21;
if (x_22 == 0)
{
x_3 = x_22;
goto block_17;
}
else
{
uint8 x_23; 
x_23 = 1;
return x_23;
}
}
}
block_31:
{
uint32 x_26; uint8 x_27; 
x_26 = 970;
x_27 = x_26 <= x_1;
if (x_27 == 0)
{
x_18 = x_25;
goto block_24;
}
else
{
uint32 x_28; uint8 x_29; 
x_28 = 1019;
x_29 = x_1 <= x_28;
if (x_29 == 0)
{
x_18 = x_29;
goto block_24;
}
else
{
uint8 x_30; 
x_30 = 1;
return x_30;
}
}
}
}
}
obj* l_Lean_isLetterLike___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isLetterLike(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isSubScriptAlnum(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; uint8 x_18; 
x_2 = 8319;
x_18 = x_2 <= x_1;
if (x_18 == 0)
{
uint8 x_19; 
x_19 = 0;
x_3 = x_19;
goto block_17;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = 8329;
x_21 = x_1 <= x_20;
if (x_21 == 0)
{
x_3 = x_21;
goto block_17;
}
else
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
}
block_17:
{
uint32 x_4; uint8 x_5; 
x_4 = 8336;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = 7522;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = 7530;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = 8348;
x_11 = x_1 <= x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 7522;
x_13 = x_12 <= x_1;
if (x_13 == 0)
{
return x_11;
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 7530;
x_15 = x_1 <= x_14;
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
}
}
obj* l_Lean_isSubScriptAlnum___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isSubScriptAlnum(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isIdFirst(uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Char_isAlpha(x_1);
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_Lean_isLetterLike(x_1);
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_Lean_isIdFirst___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isIdFirst(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isIdRest(uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Char_isAlphanum(x_1);
if (x_2 == 0)
{
uint32 x_3; uint8 x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 39;
x_6 = x_1 == x_5;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = l_Lean_isLetterLike(x_1);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = l_Lean_isSubScriptAlnum(x_1);
return x_8;
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
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
}
obj* l_Lean_isIdRest___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isIdRest(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint32 _init_l_Lean_idBeginEscape() {
_start:
{
uint32 x_1; 
x_1 = 171;
return x_1;
}
}
uint32 _init_l_Lean_idEndEscape() {
_start:
{
uint32 x_1; 
x_1 = 187;
return x_1;
}
}
uint8 l_Lean_isIdBeginEscape(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = l_Lean_idBeginEscape;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_isIdBeginEscape___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isIdBeginEscape(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isIdEndEscape(uint32 x_1) {
_start:
{
uint32 x_2; uint8 x_3; 
x_2 = l_Lean_idEndEscape;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_isIdEndEscape___boxed(obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_isIdEndEscape(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Lean_isIdRest(x_10);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::string_push(x_2, x_10);
x_14 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_String_OldIterator_remaining___main(x_2);
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = lean::apply_2(x_3, lean::box(0), x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
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
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = l_Lean_isIdFirst(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_14 = lean::string_append(x_13, x_12);
x_15 = lean::box(0);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_14, x_16, x_15, x_15);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_18 = lean::box_uint32(x_9);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_19, 0, x_3);
lean::closure_set(x_19, 1, x_18);
x_20 = lean::apply_2(x_2, lean::box(0), x_19);
return x_20;
}
}
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2(obj* x_1, obj* x_2, uint32 x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean::string_push(x_4, x_3);
x_6 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg(x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_idPartDefault___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___lambda__1), 3, 2);
lean::closure_set(x_8, 0, x_2);
lean::closure_set(x_8, 1, x_5);
lean::inc(x_4);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_2);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_idPartDefault(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartDefault___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_idPartDefault___rarg___lambda__2(x_1, x_2, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_idPartDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_idPartDefault___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_idPartDefault___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPartDefault(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Lean_isIdEndEscape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::string_push(x_2, x_10);
x_13 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_15;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_String_OldIterator_remaining___main(x_2);
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = lean::apply_2(x_3, lean::box(0), x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
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
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = l_Lean_isIdEndEscape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_11 = lean::box_uint32(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::apply_2(x_2, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_3);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_9);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_17 = lean::string_append(x_16, x_15);
x_18 = lean::box(0);
x_19 = l_mjoin___rarg___closed__1;
x_20 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_17, x_19, x_18, x_18);
return x_20;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(obj* x_1, obj* x_2, uint32 x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean::string_push(x_4, x_3);
x_6 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg(x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_4);
x_6 = lean::apply_2(x_4, lean::box(0), x_5);
lean::inc(x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_4);
lean::inc(x_3);
x_8 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_6, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
x_10 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_idPartEscaped___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint32 x_6; obj* x_7; obj* x_8; obj* x_9; uint32 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_4, 4);
lean::inc(x_5);
x_6 = l_Lean_idBeginEscape;
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_Lean_Parser_MonadParsec_ch___rarg(x_1, x_2, x_6);
x_8 = lean::cnstr_get(x_4, 3);
lean::inc(x_8);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
x_9 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(x_1, x_2);
x_10 = l_Lean_idEndEscape;
x_11 = l_Lean_Parser_MonadParsec_ch___rarg(x_1, x_2, x_10);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_9, x_11);
x_13 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_12);
return x_13;
}
}
obj* l_Lean_Parser_idPartEscaped(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPartEscaped___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2(x_1, x_2, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_idPartEscaped___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPartEscaped(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_idPart___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_isIdBeginEscape___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_idPart___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_4 = l_Lean_Parser_idPartEscaped___rarg(x_1, x_2, x_3);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_Lean_Parser_idPartDefault___rarg(x_1, x_2, x_3);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_Lean_Parser_MonadParsec_curr___rarg(x_1, x_2);
x_11 = l_Lean_Parser_idPart___rarg___closed__1;
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_11, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_13, 0, x_5);
lean::closure_set(x_13, 1, x_4);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_idPart(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_idPart___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_idPart___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPart(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean_name_mk_string(x_1, x_6);
x_8 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_2, x_3, x_4, x_7, x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_5, x_8);
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_12, 0, x_4);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
lean::closure_set(x_12, 4, x_9);
x_13 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_3, x_12);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::apply_2(x_15, lean::box(0), x_4);
x_17 = lean::apply_3(x_10, lean::box(0), x_13, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_3);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::apply_2(x_19, lean::box(0), x_4);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_String_OldIterator_remaining___main(x_5);
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_1, x_2, x_3, x_4, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_3);
lean::closure_set(x_10, 2, x_5);
lean::closure_set(x_10, 3, x_4);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_identifier___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint32 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_5);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_8, 4);
lean::inc(x_9);
lean::dec(x_8);
x_10 = 46;
lean::inc(x_3);
lean::inc(x_2);
x_11 = l_Lean_Parser_MonadParsec_ch___rarg(x_2, x_3, x_10);
x_12 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_11, x_4);
x_13 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(x_2, x_3, x_1, x_7, x_12);
return x_13;
}
}
obj* _init_l_Lean_Parser_identifier___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("identifier");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_identifier___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_Lean_Parser_idPart___rarg(x_1, x_2, x_3);
lean::inc(x_5);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identifier___rarg___lambda__1), 5, 4);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_1);
lean::closure_set(x_6, 2, x_2);
lean::closure_set(x_6, 3, x_5);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_5, x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::apply_3(x_8, lean::box(0), x_9, x_7);
x_11 = l_Lean_Parser_identifier___rarg___closed__1;
x_12 = lean::apply_3(x_8, lean::box(0), x_11, x_10);
return x_12;
}
}
obj* l_Lean_Parser_identifier(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identifier___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_foldlAux___main___at_Lean_Parser_identifier___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_identifier___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_identifier(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Char_isAlphanum(x_10);
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 95;
x_13 = x_10 == x_12;
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_7);
x_14 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::string_push(x_2, x_10);
x_16 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::string_push(x_2, x_10);
x_19 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_1);
x_21 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_21;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_String_OldIterator_remaining___main(x_2);
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = lean::apply_2(x_3, lean::box(0), x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
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
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = l_Char_isAlpha(x_9);
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 95;
x_12 = x_9 == x_11;
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_3);
lean::dec(x_2);
x_13 = l_Char_quoteCore(x_9);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_16 = lean::string_append(x_15, x_14);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_16, x_18, x_17, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_1);
x_20 = lean::box_uint32(x_9);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_21, 0, x_3);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::apply_2(x_2, lean::box(0), x_21);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
x_23 = lean::box_uint32(x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_3);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_2, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2(obj* x_1, obj* x_2, uint32 x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean::string_push(x_4, x_3);
x_6 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg(x_2, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_cIdentifier___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("C identifier");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_cIdentifier___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___lambda__1), 3, 2);
lean::closure_set(x_8, 0, x_2);
lean::closure_set(x_8, 1, x_5);
lean::inc(x_4);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
lean::inc(x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_2);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_9, x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_13 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_12);
x_14 = lean::apply_3(x_12, lean::box(0), x_13, x_11);
x_15 = l_Lean_Parser_cIdentifier___rarg___closed__1;
x_16 = lean::apply_3(x_12, lean::box(0), x_15, x_14);
return x_16;
}
}
obj* l_Lean_Parser_cIdentifier(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cIdentifier___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_cIdentifier___rarg___lambda__2(x_1, x_2, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_cIdentifier___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_cIdentifier___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_cIdentifier___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_cIdentifier(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_List_foldl___main___at_String_join___spec__1(x_6, x_5);
lean::dec(x_5);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("::");
return x_1;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("::");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_append___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_7, 2);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__1;
x_12 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_13 = l_Lean_Parser_MonadParsec_strCore___rarg(x_2, x_3, x_11, x_12);
x_14 = l_Lean_Parser_cppIdentifier___rarg___lambda__2___closed__3;
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_14, x_13);
x_16 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_4);
x_17 = l_Lean_Parser_MonadParsec_many___rarg(x_2, x_3, lean::box(0), x_1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg___lambda__1), 3, 2);
lean::closure_set(x_18, 0, x_7);
lean::closure_set(x_18, 1, x_6);
x_19 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* _init_l_Lean_Parser_cppIdentifier___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("C++ identifier");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_cppIdentifier___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_Lean_Parser_cIdentifier___rarg(x_1, x_2, x_3);
lean::inc(x_4);
lean::inc(x_5);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg___lambda__2), 6, 5);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_1);
lean::closure_set(x_6, 2, x_2);
lean::closure_set(x_6, 3, x_5);
lean::closure_set(x_6, 4, x_4);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_5, x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::apply_3(x_8, lean::box(0), x_9, x_7);
x_11 = l_Lean_Parser_cppIdentifier___rarg___closed__1;
x_12 = lean::apply_3(x_8, lean::box(0), x_11, x_10);
return x_12;
}
}
obj* l_Lean_Parser_cppIdentifier(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_cppIdentifier___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_cppIdentifier___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_cppIdentifier(x_1, x_2);
lean::dec(x_1);
return x_3;
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
if (io_result_is_error(w)) return w;
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Parser_idPart___rarg___closed__1 = _init_l_Lean_Parser_idPart___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_idPart___rarg___closed__1);
l_Lean_Parser_identifier___rarg___closed__1 = _init_l_Lean_Parser_identifier___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_identifier___rarg___closed__1);
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
