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
extern "C" {
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
uint32 x_2; uint8 x_3; uint8 x_19; uint8 x_27; uint8 x_35; uint8 x_59; 
x_2 = 945;
x_59 = x_2 <= x_1;
if (x_59 == 0)
{
uint8 x_60; 
x_60 = 0;
x_35 = x_60;
goto block_58;
}
else
{
uint32 x_61; uint8 x_62; 
x_61 = 969;
x_62 = x_1 <= x_61;
if (x_62 == 0)
{
uint8 x_63; 
x_63 = 0;
x_35 = x_63;
goto block_58;
}
else
{
uint32 x_64; uint8 x_65; 
x_64 = 955;
x_65 = x_1 == x_64;
if (x_65 == 0)
{
uint8 x_66; 
x_66 = 1;
return x_66;
}
else
{
uint8 x_67; 
x_67 = 0;
x_35 = x_67;
goto block_58;
}
}
}
block_18:
{
uint32 x_4; uint8 x_5; 
x_4 = 8448;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
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
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = 8527;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 119964;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
return x_12;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 120223;
x_16 = x_1 <= x_15;
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = 1;
return x_17;
}
}
}
block_26:
{
uint32 x_20; uint8 x_21; 
x_20 = 7936;
x_21 = x_20 <= x_1;
if (x_21 == 0)
{
if (x_19 == 0)
{
x_3 = x_19;
goto block_18;
}
else
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint32 x_23; uint8 x_24; 
x_23 = 8190;
x_24 = x_1 <= x_23;
if (x_24 == 0)
{
x_3 = x_24;
goto block_18;
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
}
block_34:
{
uint32 x_28; uint8 x_29; 
x_28 = 970;
x_29 = x_28 <= x_1;
if (x_29 == 0)
{
if (x_27 == 0)
{
x_19 = x_27;
goto block_26;
}
else
{
uint8 x_30; 
x_30 = 1;
return x_30;
}
}
else
{
uint32 x_31; uint8 x_32; 
x_31 = 1019;
x_32 = x_1 <= x_31;
if (x_32 == 0)
{
x_19 = x_32;
goto block_26;
}
else
{
uint8 x_33; 
x_33 = 1;
return x_33;
}
}
}
block_58:
{
uint32 x_36; uint8 x_37; 
x_36 = 913;
x_37 = x_36 <= x_1;
if (x_37 == 0)
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 928;
x_39 = x_1 == x_38;
if (x_39 == 0)
{
uint32 x_40; uint8 x_41; 
x_40 = 931;
x_41 = x_1 == x_40;
if (x_41 == 0)
{
uint8 x_42; 
x_42 = 1;
return x_42;
}
else
{
uint8 x_43; 
x_43 = 0;
x_27 = x_43;
goto block_34;
}
}
else
{
uint8 x_44; 
x_44 = 1;
return x_44;
}
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = 937;
x_46 = x_1 <= x_45;
if (x_46 == 0)
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint32 x_47; uint8 x_48; 
x_47 = 931;
x_48 = x_1 == x_47;
if (x_48 == 0)
{
uint8 x_49; 
x_49 = 1;
return x_49;
}
else
{
uint8 x_50; 
x_50 = 0;
x_27 = x_50;
goto block_34;
}
}
}
else
{
uint32 x_51; uint8 x_52; 
x_51 = 928;
x_52 = x_1 == x_51;
if (x_52 == 0)
{
uint32 x_53; uint8 x_54; 
x_53 = 931;
x_54 = x_1 == x_53;
if (x_54 == 0)
{
uint8 x_55; 
x_55 = 1;
return x_55;
}
else
{
uint8 x_56; 
x_56 = 0;
x_27 = x_56;
goto block_34;
}
}
else
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint8 x_57; 
x_57 = 1;
return x_57;
}
}
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
uint32 x_2; uint8 x_3; uint8 x_19; 
x_2 = 8319;
x_19 = x_2 <= x_1;
if (x_19 == 0)
{
uint8 x_20; 
x_20 = 0;
x_3 = x_20;
goto block_18;
}
else
{
uint32 x_21; uint8 x_22; 
x_21 = 8329;
x_22 = x_1 <= x_21;
if (x_22 == 0)
{
x_3 = x_22;
goto block_18;
}
else
{
uint8 x_23; 
x_23 = 1;
return x_23;
}
}
block_18:
{
uint32 x_4; uint8 x_5; 
x_4 = 8336;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
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
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = 8348;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 7522;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
return x_12;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 7530;
x_16 = x_1 <= x_15;
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = 1;
return x_17;
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
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
return w;
}
}
