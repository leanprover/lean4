// Lean compiler output
// Module: Init.Lean.Parser.Identifier
// Imports: Init.Data.Char.Basic
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
uint32_t l_Lean_idBeginEscape;
lean_object* l_Lean_isGreek___boxed(lean_object*);
uint32_t l_Lean_idEndEscape;
lean_object* l_Lean_isIdRest___boxed(lean_object*);
uint8_t l_Lean_isIdBeginEscape(uint32_t);
lean_object* l_Lean_isIdFirst___boxed(lean_object*);
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
uint8_t l_Lean_isIdEndEscape(uint32_t);
uint8_t l_Char_isAlpha(uint32_t);
uint8_t l_Lean_isLetterLike(uint32_t);
lean_object* l_Lean_isLetterLike___boxed(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
uint8_t l_Char_isAlphanum(uint32_t);
uint8_t l_Lean_isGreek(uint32_t);
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
uint8_t l_Lean_isIdRest(uint32_t);
uint8_t l_Lean_isGreek(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 913;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 989;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Lean_isGreek___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isGreek(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isLetterLike(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint8_t x_19; uint8_t x_27; uint8_t x_35; uint8_t x_59; 
x_2 = 945;
x_59 = x_2 <= x_1;
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
x_35 = x_60;
goto block_58;
}
else
{
uint32_t x_61; uint8_t x_62; 
x_61 = 969;
x_62 = x_1 <= x_61;
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_35 = x_63;
goto block_58;
}
else
{
uint32_t x_64; uint8_t x_65; 
x_64 = 955;
x_65 = x_1 == x_64;
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = 1;
return x_66;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_35 = x_67;
goto block_58;
}
}
}
block_18:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 8448;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 119964;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 120223;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 8527;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 119964;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
return x_12;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 120223;
x_16 = x_1 <= x_15;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
block_26:
{
uint32_t x_20; uint8_t x_21; 
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
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 8190;
x_24 = x_1 <= x_23;
if (x_24 == 0)
{
x_3 = x_24;
goto block_18;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
}
block_34:
{
uint32_t x_28; uint8_t x_29; 
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
uint8_t x_30; 
x_30 = 1;
return x_30;
}
}
else
{
uint32_t x_31; uint8_t x_32; 
x_31 = 1019;
x_32 = x_1 <= x_31;
if (x_32 == 0)
{
x_19 = x_32;
goto block_26;
}
else
{
uint8_t x_33; 
x_33 = 1;
return x_33;
}
}
}
block_58:
{
uint32_t x_36; uint8_t x_37; 
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
uint32_t x_38; uint8_t x_39; 
x_38 = 928;
x_39 = x_1 == x_38;
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 931;
x_41 = x_1 == x_40;
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 1;
return x_42;
}
else
{
uint8_t x_43; 
x_43 = 0;
x_27 = x_43;
goto block_34;
}
}
else
{
uint8_t x_44; 
x_44 = 1;
return x_44;
}
}
}
else
{
uint32_t x_45; uint8_t x_46; 
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
uint32_t x_47; uint8_t x_48; 
x_47 = 931;
x_48 = x_1 == x_47;
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 1;
return x_49;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_27 = x_50;
goto block_34;
}
}
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 928;
x_52 = x_1 == x_51;
if (x_52 == 0)
{
uint32_t x_53; uint8_t x_54; 
x_53 = 931;
x_54 = x_1 == x_53;
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 1;
return x_55;
}
else
{
uint8_t x_56; 
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
uint8_t x_57; 
x_57 = 1;
return x_57;
}
}
}
}
}
}
}
lean_object* l_Lean_isLetterLike___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isLetterLike(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isSubScriptAlnum(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint8_t x_19; 
x_2 = 8320;
x_19 = x_2 <= x_1;
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
x_3 = x_20;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 8329;
x_22 = x_1 <= x_21;
if (x_22 == 0)
{
x_3 = x_22;
goto block_18;
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
block_18:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 8336;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 7522;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 7530;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 8348;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 7522;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
return x_12;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 7530;
x_16 = x_1 <= x_15;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
}
}
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isSubScriptAlnum(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdFirst(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlpha(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_isLetterLike(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_isIdFirst___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdFirst(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdRest(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlphanum(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = x_1 == x_5;
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = x_1 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = x_1 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isLetterLike(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_1);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
lean_object* l_Lean_isIdRest___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdRest(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint32_t _init_l_Lean_idBeginEscape() {
_start:
{
uint32_t x_1; 
x_1 = 171;
return x_1;
}
}
uint32_t _init_l_Lean_idEndEscape() {
_start:
{
uint32_t x_1; 
x_1 = 187;
return x_1;
}
}
uint8_t l_Lean_isIdBeginEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idBeginEscape;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdBeginEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdEndEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idEndEscape;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_isIdEndEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdEndEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Char_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Identifier(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
