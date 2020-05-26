// Lean compiler output
// Module: Lean.Data.Json.Basic
// Imports: Init.System.IO Init.Data.String Init.Data.Int Init.Data.RBMap
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
lean_object* l_Lean_JsonNumber_decidableEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
lean_object* l_String_Iterator_remainingToString(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getNum_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getStr_x3f___boxed(lean_object*);
extern lean_object* l_Int_repr___closed__1;
lean_object* l_Lean_Json_getObj_x3f___boxed(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString___closed__5;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getArrVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_jsonNumberToString;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Int_zero;
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_jsonNumberToString___closed__1;
lean_object* l_Int_repr(lean_object*);
lean_object* l___private_Lean_Data_Json_Basic_2__countDigits(lean_object*);
lean_object* l_Lean_Json_intToJson(lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Lean_Json_boolToJson(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_jsonNumberHasRepr___closed__1;
extern lean_object* l_Int_zero___closed__1;
lean_object* l_Lean_Json_stringToJson(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Basic_1__countDigitsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_strLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArrVal_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_boolToJson___boxed(lean_object*);
lean_object* l_Lean_Json_getNat_x3f___boxed(lean_object*);
uint8_t l_Lean_JsonNumber_decidableEq(lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l_Lean_JsonNumber_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_jsonNumberHasRepr(lean_object*);
lean_object* l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_JsonNumber_natToJsonNumber___closed__1;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
extern lean_object* l_Int_one;
lean_object* l_Lean_JsonNumber_natToJsonNumber;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Basic_1__countDigitsAux(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_JsonNumber_toString___closed__4;
lean_object* l_Lean_JsonNumber_toString___closed__2;
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
uint8_t l_Lean_JsonNumber_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNum_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString___closed__1;
uint8_t l_Lean_strLt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_natToJson(lean_object*);
lean_object* l_Lean_Json_getObjValD___boxed(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Json_getArr_x3f___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_intToJsonNumber;
lean_object* l_Lean_JsonNumber_toString___closed__3;
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_intToJsonNumber___closed__1;
lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_JsonNumber_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
lean_object* l_Lean_JsonNumber_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonNumber_decEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_JsonNumber_decidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_JsonNumber_decEq(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_JsonNumber_decidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonNumber_decidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_JsonNumber_fromNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_to_int(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_JsonNumber_fromInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_JsonNumber_natToJsonNumber___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_fromNat), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_natToJsonNumber() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_natToJsonNumber___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_intToJsonNumber___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_fromInt), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_intToJsonNumber() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_intToJsonNumber___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_Json_Basic_1__countDigitsAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(9u);
x_4 = lean_nat_dec_le(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(10u);
x_6 = lean_nat_div(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l___private_Lean_Data_Json_Basic_1__countDigitsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Json_Basic_1__countDigitsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Json_Basic_2__countDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l___private_Lean_Data_Json_Basic_1__countDigitsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_6 = lean_string_utf8_get(x_1, x_5);
x_7 = 48;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* _init_l_Lean_JsonNumber_toString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_one;
x_2 = lean_int_add(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_JsonNumber_toString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_toString___closed__1;
x_2 = lean_int_add(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_JsonNumber_toString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_toString___closed__2;
x_2 = lean_int_add(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_JsonNumber_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonNumber_toString___closed__3;
x_2 = l_Int_one;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_JsonNumber_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("e");
return x_1;
}
}
lean_object* l_Lean_JsonNumber_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_Int_zero;
x_7 = lean_int_dec_le(x_6, x_2);
x_8 = lean_nat_abs(x_2);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_10 = l___private_Lean_Data_Json_Basic_1__countDigitsAux___main(x_8, x_9);
x_11 = lean_nat_to_int(x_10);
x_12 = l_Lean_JsonNumber_toString___closed__4;
x_13 = lean_int_add(x_12, x_11);
lean_dec(x_11);
lean_inc(x_3);
x_14 = lean_nat_to_int(x_3);
x_15 = lean_int_sub(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_int_dec_lt(x_15, x_6);
lean_inc(x_8);
x_17 = lean_nat_to_int(x_8);
if (x_16 == 0)
{
lean_dec(x_15);
x_18 = x_6;
goto block_57;
}
else
{
x_18 = x_15;
goto block_57;
}
block_57:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_19 = lean_nat_abs(x_18);
x_20 = lean_nat_sub(x_3, x_19);
lean_dec(x_19);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_nat_pow(x_21, x_20);
lean_dec(x_20);
x_23 = lean_nat_div(x_8, x_22);
lean_dec(x_8);
x_24 = lean_nat_to_int(x_22);
x_25 = lean_int_mod(x_17, x_24);
lean_dec(x_17);
x_26 = lean_int_add(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = l_Int_repr(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_29 = l_String_Iterator_next(x_28);
x_30 = l_String_Iterator_remainingToString(x_29);
lean_dec(x_29);
x_31 = l_Nat_repr(x_23);
x_32 = lean_string_utf8_byte_size(x_30);
x_33 = l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1(x_30, x_4, x_32);
x_34 = lean_string_utf8_extract(x_30, x_4, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_35 = lean_int_dec_eq(x_18, x_6);
if (x_7 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Int_repr___closed__1;
x_37 = lean_string_append(x_36, x_31);
lean_dec(x_31);
x_38 = l_System_FilePath_dirName___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Int_repr(x_18);
lean_dec(x_18);
x_42 = l_Lean_JsonNumber_toString___closed__5;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = lean_string_append(x_40, x_43);
lean_dec(x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_18);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean_string_append(x_40, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l_String_splitAux___main___closed__1;
x_48 = lean_string_append(x_47, x_31);
lean_dec(x_31);
x_49 = l_System_FilePath_dirName___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Int_repr(x_18);
lean_dec(x_18);
x_53 = l_Lean_JsonNumber_toString___closed__5;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = lean_string_append(x_51, x_54);
lean_dec(x_54);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_18);
x_56 = lean_string_append(x_51, x_47);
return x_56;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_3);
x_58 = l_Int_repr(x_2);
lean_dec(x_2);
return x_58;
}
}
}
lean_object* l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_Lean_JsonNumber_toString___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_JsonNumber_shiftl(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = lean_unsigned_to_nat(10u);
x_8 = lean_nat_pow(x_7, x_6);
lean_dec(x_6);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_int_mul(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_5, x_2);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_nat_sub(x_2, x_13);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_nat_pow(x_15, x_14);
lean_dec(x_14);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_mul(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonNumber_shiftl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_JsonNumber_shiftr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonNumber_shiftr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_JsonNumber_jsonNumberToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_jsonNumberToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_jsonNumberToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_JsonNumber_jsonNumberHasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
lean_object* l_Lean_JsonNumber_jsonNumberHasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Int_repr(x_2);
lean_dec(x_2);
x_5 = l_Sigma_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_JsonNumber_jsonNumberHasRepr___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_Sigma_HasRepr___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
uint8_t l_Lean_strLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_strLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_strLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_natToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Json_intToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Lean_Json_stringToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Json_boolToJson(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Json_boolToJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Json_boolToJson(x_2);
return x_3;
}
}
lean_object* l_Lean_Json_getObj_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_Json_getObj_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getArr_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_Json_getArr_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getArr_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getStr_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_Json_getStr_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getNat_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Int_zero___closed__1;
x_6 = lean_int_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_nat_abs(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
}
}
lean_object* l_Lean_Json_getNat_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getNat_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getInt_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* l_Lean_Json_getInt_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getInt_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getBool_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint8(x_1, 0);
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
}
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getBool_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getNum_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_Json_getNum_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getNum_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_string_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Lean_Json_getObjVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
}
lean_object* l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Json_getObjVal_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getArrVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Array_get_x3f___rarg(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
}
lean_object* l_Lean_Json_getArrVal_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getArrVal_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l_Lean_Json_getObjValD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
lean_object* initialize_Init_Data_Int(lean_object*);
lean_object* initialize_Init_Data_RBMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Json_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonNumber_natToJsonNumber___closed__1 = _init_l_Lean_JsonNumber_natToJsonNumber___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_natToJsonNumber___closed__1);
l_Lean_JsonNumber_natToJsonNumber = _init_l_Lean_JsonNumber_natToJsonNumber();
lean_mark_persistent(l_Lean_JsonNumber_natToJsonNumber);
l_Lean_JsonNumber_intToJsonNumber___closed__1 = _init_l_Lean_JsonNumber_intToJsonNumber___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_intToJsonNumber___closed__1);
l_Lean_JsonNumber_intToJsonNumber = _init_l_Lean_JsonNumber_intToJsonNumber();
lean_mark_persistent(l_Lean_JsonNumber_intToJsonNumber);
l_Lean_JsonNumber_toString___closed__1 = _init_l_Lean_JsonNumber_toString___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__1);
l_Lean_JsonNumber_toString___closed__2 = _init_l_Lean_JsonNumber_toString___closed__2();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__2);
l_Lean_JsonNumber_toString___closed__3 = _init_l_Lean_JsonNumber_toString___closed__3();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__3);
l_Lean_JsonNumber_toString___closed__4 = _init_l_Lean_JsonNumber_toString___closed__4();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__4);
l_Lean_JsonNumber_toString___closed__5 = _init_l_Lean_JsonNumber_toString___closed__5();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__5);
l_Lean_JsonNumber_jsonNumberToString___closed__1 = _init_l_Lean_JsonNumber_jsonNumberToString___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_jsonNumberToString___closed__1);
l_Lean_JsonNumber_jsonNumberToString = _init_l_Lean_JsonNumber_jsonNumberToString();
lean_mark_persistent(l_Lean_JsonNumber_jsonNumberToString);
l_Lean_JsonNumber_jsonNumberHasRepr___closed__1 = _init_l_Lean_JsonNumber_jsonNumberHasRepr___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_jsonNumberHasRepr___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
