// Lean compiler output
// Module: init.lean.parser.identifier
// Imports: init.data.char.basic
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
uint8 l_Char_isAlphanum(uint32);
obj* l_Lean_isLetterLike___boxed(obj*);
uint8 l_Lean_isIdRest(uint32);
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_isIdBeginEscape___boxed(obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_Lean_isIdFirst___boxed(obj*);
uint8 l_Lean_isLetterLike(uint32);
uint8 l_Lean_isIdBeginEscape(uint32);
uint8 l_UInt32_decLe(uint32, uint32);
uint32 l_Lean_idBeginEscape;
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_isGreek___boxed(obj*);
obj* l_Lean_isIdEndEscape___boxed(obj*);
uint32 l_Lean_idEndEscape;
uint8 l_Lean_isIdFirst(uint32);
uint8 l_Lean_isGreek(uint32);
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
obj* initialize_init_data_char_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_identifier(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isGreek"), 1, l_Lean_isGreek___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isLetterLike"), 1, l_Lean_isLetterLike___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isSubScriptAlnum"), 1, l_Lean_isSubScriptAlnum___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isIdFirst"), 1, l_Lean_isIdFirst___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isIdRest"), 1, l_Lean_isIdRest___boxed);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isIdBeginEscape"), 1, l_Lean_isIdBeginEscape___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isIdEndEscape"), 1, l_Lean_isIdEndEscape___boxed);
return w;
}
