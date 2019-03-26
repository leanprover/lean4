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
obj* l_Lean_Parser_identifier___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__mkStringResult___rarg(obj*, obj*);
uint8 l_Char_isAlphanum(uint32);
obj* l_Lean_isLetterLike___boxed(obj*);
obj* l_Lean_Parser_cppIdentifier___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___boxed(obj*, obj*);
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
obj* l_Lean_idBeginEscape___boxed;
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___boxed(obj*);
obj* l_Lean_Parser_cIdentifier___boxed(obj*, obj*);
obj* l_Lean_Parser_cIdentifier(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_idPartEscaped___rarg(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
uint32 l_Lean_idBeginEscape;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj*, obj*, obj*);
obj* l_Char_quoteCore(uint32);
uint8 l_String_OldIterator_hasNext___main(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___boxed(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_idPartEscaped___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_String_append___boxed(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_try___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj*, obj*);
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
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_cIdentifier___rarg___closed__1;
obj* l_Lean_Parser_idPart___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_idPartEscaped(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at_Lean_Parser_identifier___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_curr___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
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
uint8 l_Lean_isGreek(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 913;
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
x_4 = 989;
x_5 = x_0 <= x_4;
return x_5;
}
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
uint8 l_Lean_isLetterLike(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; uint8 x_4; uint8 x_6; uint8 x_8; uint8 x_10; 
x_1 = 945;
x_10 = x_1 <= x_0;
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
x_8 = x_11;
goto lbl_9;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = 969;
x_13 = x_0 <= x_12;
if (x_13 == 0)
{
uint8 x_14; 
x_14 = 0;
x_8 = x_14;
goto lbl_9;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 955;
x_16 = x_0 == x_15;
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 0;
x_8 = x_18;
goto lbl_9;
}
}
}
lbl_3:
{
uint32 x_19; uint8 x_20; 
x_19 = 8448;
x_20 = x_19 <= x_0;
if (x_20 == 0)
{
if (x_2 == 0)
{
uint32 x_21; uint8 x_22; 
x_21 = 119964;
x_22 = x_21 <= x_0;
if (x_22 == 0)
{
return x_2;
}
else
{
uint32 x_23; uint8 x_24; 
x_23 = 120223;
x_24 = x_0 <= x_23;
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint32 x_26; uint8 x_27; 
x_26 = 8527;
x_27 = x_0 <= x_26;
if (x_27 == 0)
{
uint32 x_28; uint8 x_29; 
x_28 = 119964;
x_29 = x_28 <= x_0;
if (x_29 == 0)
{
return x_27;
}
else
{
uint32 x_30; uint8 x_31; 
x_30 = 120223;
x_31 = x_0 <= x_30;
return x_31;
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
lbl_5:
{
uint32 x_33; uint8 x_34; 
x_33 = 7936;
x_34 = x_33 <= x_0;
if (x_34 == 0)
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
uint8 x_35; 
x_35 = 1;
return x_35;
}
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 8190;
x_37 = x_0 <= x_36;
if (x_37 == 0)
{
x_2 = x_37;
goto lbl_3;
}
else
{
uint8 x_38; 
x_38 = 1;
return x_38;
}
}
}
lbl_7:
{
uint32 x_39; uint8 x_40; 
x_39 = 970;
x_40 = x_39 <= x_0;
if (x_40 == 0)
{
if (x_6 == 0)
{
x_4 = x_6;
goto lbl_5;
}
else
{
uint8 x_41; 
x_41 = 1;
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = 1019;
x_43 = x_0 <= x_42;
if (x_43 == 0)
{
x_4 = x_43;
goto lbl_5;
}
else
{
uint8 x_44; 
x_44 = 1;
return x_44;
}
}
}
lbl_9:
{
uint32 x_45; uint8 x_46; 
x_45 = 913;
x_46 = x_45 <= x_0;
if (x_46 == 0)
{
if (x_8 == 0)
{
if (x_8 == 0)
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
uint8 x_47; 
x_47 = 1;
return x_47;
}
}
else
{
uint32 x_48; uint8 x_49; 
x_48 = 931;
x_49 = x_0 == x_48;
if (x_49 == 0)
{
uint8 x_50; 
x_50 = 1;
return x_50;
}
else
{
uint8 x_51; 
x_51 = 0;
x_6 = x_51;
goto lbl_7;
}
}
}
else
{
uint32 x_52; uint8 x_53; 
x_52 = 928;
x_53 = x_0 == x_52;
if (x_53 == 0)
{
uint32 x_54; uint8 x_55; 
x_54 = 931;
x_55 = x_0 == x_54;
if (x_55 == 0)
{
uint8 x_56; 
x_56 = 1;
return x_56;
}
else
{
uint8 x_57; 
x_57 = 0;
x_6 = x_57;
goto lbl_7;
}
}
else
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
uint8 x_58; 
x_58 = 1;
return x_58;
}
}
}
}
else
{
uint32 x_59; uint8 x_60; 
x_59 = 937;
x_60 = x_0 <= x_59;
if (x_60 == 0)
{
if (x_8 == 0)
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
uint8 x_61; 
x_61 = 1;
return x_61;
}
}
else
{
uint32 x_62; uint8 x_63; 
x_62 = 931;
x_63 = x_0 == x_62;
if (x_63 == 0)
{
uint8 x_64; 
x_64 = 1;
return x_64;
}
else
{
uint8 x_65; 
x_65 = 0;
x_6 = x_65;
goto lbl_7;
}
}
}
else
{
uint32 x_66; uint8 x_67; 
x_66 = 928;
x_67 = x_0 == x_66;
if (x_67 == 0)
{
uint32 x_68; uint8 x_69; 
x_68 = 931;
x_69 = x_0 == x_68;
if (x_69 == 0)
{
uint8 x_70; 
x_70 = 1;
return x_70;
}
else
{
uint8 x_71; 
x_71 = 0;
x_6 = x_71;
goto lbl_7;
}
}
else
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
uint8 x_72; 
x_72 = 1;
return x_72;
}
}
}
}
}
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
uint8 l_Lean_isSubScriptAlnum(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; uint8 x_4; 
x_1 = 8319;
x_4 = x_1 <= x_0;
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
x_2 = x_5;
goto lbl_3;
}
else
{
uint32 x_6; uint8 x_7; 
x_6 = 8329;
x_7 = x_0 <= x_6;
if (x_7 == 0)
{
x_2 = x_7;
goto lbl_3;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
lbl_3:
{
uint32 x_9; uint8 x_10; 
x_9 = 8336;
x_10 = x_9 <= x_0;
if (x_10 == 0)
{
if (x_2 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 7522;
x_12 = x_11 <= x_0;
if (x_12 == 0)
{
return x_2;
}
else
{
uint32 x_13; uint8 x_14; 
x_13 = 7530;
x_14 = x_0 <= x_13;
return x_14;
}
}
else
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = 8348;
x_17 = x_0 <= x_16;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; 
x_18 = 7522;
x_19 = x_18 <= x_0;
if (x_19 == 0)
{
return x_17;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = 7530;
x_21 = x_0 <= x_20;
return x_21;
}
}
else
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
}
}
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
uint8 l_Lean_isIdFirst(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Char_isAlpha(x_0);
if (x_1 == 0)
{
uint32 x_2; uint8 x_3; 
x_2 = 95;
x_3 = x_0 == x_2;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = l_Lean_isLetterLike(x_0);
return x_4;
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
uint8 x_6; 
x_6 = 1;
return x_6;
}
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
uint8 l_Lean_isIdRest(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Char_isAlphanum(x_0);
if (x_1 == 0)
{
uint32 x_2; uint8 x_3; 
x_2 = 95;
x_3 = x_0 == x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 39;
x_5 = x_0 == x_4;
if (x_5 == 0)
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
uint8 x_8; 
x_8 = 1;
return x_8;
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
uint32 x_0; 
x_0 = 171;
return x_0;
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
uint32 x_0; 
x_0 = 187;
return x_0;
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
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
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartDefault___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_OldIterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___rarg(x_2, x_0, x_1);
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
x_3 = l_String_OldIterator_hasNext___main(x_2);
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
x_10 = l_String_OldIterator_curr___main(x_2);
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
x_3 = l_String_splitAux___main___closed__1;
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartDefault___spec__2(x_0);
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_idPartEscaped___spec__2___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_OldIterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___rarg(x_2, x_0, x_1);
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
x_3 = l_String_OldIterator_hasNext___main(x_2);
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
x_10 = l_String_OldIterator_curr___main(x_2);
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
x_3 = l_String_splitAux___main___closed__1;
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_idPartEscaped___spec__3(x_0);
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
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
x_7 = lean::mk_nat_obj(1ul);
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
x_5 = l_String_OldIterator_remaining___main(x_4);
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
x_12 = 46;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; uint8 x_12; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = l_String_OldIterator_curr___main(x_2);
x_12 = l_Char_isAlphanum(x_11);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 95;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_9);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::string_push(x_1, x_11);
x_18 = l_String_OldIterator_next___main(x_2);
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
x_21 = l_String_OldIterator_next___main(x_2);
x_0 = x_9;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
}
else
{
obj* x_24; 
lean::dec(x_0);
x_24 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_24;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_cIdentifier___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_OldIterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___rarg(x_2, x_0, x_1);
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
x_3 = l_String_OldIterator_hasNext___main(x_2);
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
x_10 = l_String_OldIterator_curr___main(x_2);
x_11 = l_Char_isAlpha(x_10);
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 95;
x_13 = x_10 == x_12;
if (x_13 == 0)
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
}
}
obj* l_Lean_Parser_cIdentifier___rarg___lambda__2(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_splitAux___main___closed__1;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
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
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_cIdentifier___spec__2(x_0);
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
x_7 = l_String_splitAux___main___closed__1;
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
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
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
 l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
 l_Lean_idBeginEscape___boxed = _init_l_Lean_idBeginEscape___boxed();
lean::mark_persistent(l_Lean_idBeginEscape___boxed);
 l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
 l_Lean_idEndEscape___boxed = _init_l_Lean_idEndEscape___boxed();
lean::mark_persistent(l_Lean_idEndEscape___boxed);
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
