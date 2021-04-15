// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: Init.Data.String.Basic Init.Data.UInt Init.Data.Nat.Div Init.Data.Repr Init.Data.Int.Basic Init.Data.Format.Basic Init.Control.Id Init.Control.Option
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
lean_object* l_instToStringUInt16(uint16_t);
lean_object* l_instToStringSubtype___rarg(lean_object*, lean_object*);
uint8_t l_String_isInt(lean_object*);
lean_object* l_String_Iterator_remainingToString(lean_object*);
lean_object* l_String_toInt_x3f___closed__1;
extern lean_object* l_instReprOption___rarg___closed__1;
lean_object* l_instToStringExcept_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringSigma_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__2;
lean_object* l_addParenHeuristic___closed__2;
lean_object* l_instToStringULift(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* l_Substring_drop(lean_object*, lean_object*);
extern lean_object* l_Int_instNegInt;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_instToStringExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toInt_x21___closed__1;
lean_object* l_instToStringDecidable_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Substring_toNat_x3f(lean_object*);
uint8_t l_String_anyAux_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_isInt___boxed(lean_object*);
lean_object* l_instToStringFin(lean_object*);
lean_object* l_instToStringUnit(lean_object*);
lean_object* l_String_toInt_x3f___lambda__1(lean_object*);
lean_object* l_instToStringFin___rarg(lean_object*);
lean_object* l_String_toInt_x3f___lambda__2(lean_object*);
lean_object* l_instToStringChar;
lean_object* l_instToStringUInt64___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_String_toSubstring(lean_object*);
lean_object* l_instToStringPUnit(lean_object*);
lean_object* l_String_toInt_x3f(lean_object*);
lean_object* l_instToStringInt_match__1(lean_object*);
lean_object* l_List_toStringAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toInt_x3f___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringProd___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toInt_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_instToStringSubstring(lean_object*);
extern lean_object* l_instReprBool___closed__2;
lean_object* l_String_toInt_x21(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_toStringAux___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_instToStringFormat(lean_object*);
lean_object* l_instToStringUInt32(uint32_t);
lean_object* l_instToStringDecidable(lean_object*);
lean_object* l_instReprExcept___rarg___closed__2;
lean_object* l_instToStringUInt8___boxed(lean_object*);
lean_object* l_instToStringId__1(lean_object*);
lean_object* l_instToStringOption_match__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_22151____closed__8;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instToStringUnit___boxed(lean_object*);
lean_object* l_String_toInt_x3f___closed__3;
lean_object* l_instToStringIterator(lean_object*);
extern lean_object* l_instReprList___rarg___closed__1;
uint8_t l_Substring_isNat(lean_object*);
lean_object* l_List_toStringAux_match__1(lean_object*, lean_object*);
lean_object* l_instToStringExcept___rarg___closed__1;
lean_object* l_instToStringInt_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringOption___rarg(lean_object*, lean_object*);
lean_object* l_instToStringUInt64(uint64_t);
lean_object* l_instToStringBool(uint8_t);
lean_object* l_instToStringString(lean_object*);
lean_object* l_List_toStringAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_instReprExcept_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringChar___closed__1;
lean_object* l_instToStringNat(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_instToStringId___rarg(lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_List_toString___rarg(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabitedInt;
lean_object* l_instToStringSubtype(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_instToStringList(lean_object*);
lean_object* l_List_toStringAux(lean_object*);
lean_object* l_instToStringUSize(size_t);
lean_object* l_instToStringIterator___boxed(lean_object*);
lean_object* l_instToStringSigma(lean_object*, lean_object*);
lean_object* l_String_toInt_x21_match__1(lean_object*);
lean_object* l_instToStringSum___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringSum___rarg___closed__1;
lean_object* l_String_toInt_x3f___lambda__2___closed__1;
lean_object* l_List_toString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_instToStringExcept___rarg___closed__2;
lean_object* l_List_toString_match__1(lean_object*, lean_object*);
lean_object* l_instToStringExcept(lean_object*, lean_object*);
lean_object* l_instReprExcept___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x2d_____closed__3;
lean_object* l_instToStringList___rarg(lean_object*);
lean_object* l_instToStringSigma___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_instToStringExcept_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringId(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_List_toStringAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprUnit___closed__1;
lean_object* l_instToStringString___boxed(lean_object*);
lean_object* l_instReprExcept___rarg___closed__1;
extern lean_object* l_Id_instMonadId;
lean_object* l_instToStringOption(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_instReprExcept___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString(lean_object*);
lean_object* l_instToStringSum(lean_object*, lean_object*);
lean_object* l_instToStringInt___boxed(lean_object*);
lean_object* l_instToStringPUnit___boxed(lean_object*);
lean_object* l_instToStringInt(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_instToStringId__1___rarg(lean_object*);
lean_object* l_instToStringUInt32___boxed(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_instToStringProd_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* l_instReprExcept_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringSum___rarg___closed__2;
lean_object* lean_nat_abs(lean_object*);
lean_object* l_instToStringSum_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringDecidable_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringOption___rarg___closed__1;
lean_object* l_instToStringOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringUInt16___boxed(lean_object*);
lean_object* l_instReprExcept(lean_object*, lean_object*);
lean_object* l_instToStringSum_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringId__1___rarg___boxed(lean_object*);
lean_object* l_instToStringSubstring___boxed(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_instToStringProd_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringId___rarg___boxed(lean_object*);
lean_object* l_instReprExcept___rarg___closed__3;
lean_object* l_instToStringUSize___boxed(lean_object*);
lean_object* l_instToStringInt_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_instToStringDecidable___rarg(uint8_t);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_instToStringDecidable_match__1(lean_object*, lean_object*);
lean_object* l_OptionT_instAlternativeOptionT___rarg(lean_object*);
lean_object* l_instToStringULift___rarg(lean_object*, lean_object*);
lean_object* l_addParenHeuristic___closed__3;
lean_object* l_instToStringProd(lean_object*, lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
lean_object* l_String_push___boxed(lean_object*, lean_object*);
lean_object* l_instToStringUInt8(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_instToStringBool___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_instToStringDecidable___rarg___boxed(lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__6;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_instToStringSigma_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instReprExcept___rarg___closed__4;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_addParenHeuristic___boxed(lean_object*);
lean_object* l_addParenHeuristic___closed__1;
extern lean_object* l_term_x5b___x5d___closed__3;
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_instToStringFin___boxed(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_instToStringId___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_instToStringId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringId___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_instToStringId___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringId__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_instToStringId__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringId__1___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_instToStringId__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringId__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringString(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_instToStringString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringSubstring(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instToStringSubstring___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringSubstring(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
return x_2;
}
}
lean_object* l_instToStringIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringIterator(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_22151____closed__8;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_instReprBool___closed__2;
return x_3;
}
}
}
lean_object* l_instToStringBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringBool(x_2);
return x_3;
}
}
lean_object* l_instToStringDecidable_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
}
}
lean_object* l_instToStringDecidable_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringDecidable_match__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_instToStringDecidable_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_instToStringDecidable_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_instToStringDecidable___rarg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_22151____closed__8;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_instReprBool___closed__2;
return x_3;
}
}
}
lean_object* l_instToStringDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringDecidable___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_instToStringDecidable___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringDecidable___rarg(x_2);
return x_3;
}
}
lean_object* l_List_toStringAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_box(x_1);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_4, x_13, x_14);
return x_15;
}
}
}
}
lean_object* l_List_toStringAux_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_toStringAux_match__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_List_toStringAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_List_toStringAux_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_List_toStringAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_Lean_instInhabitedParserDescr___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_term_x5b___x5d___closed__5;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = 0;
x_11 = l_List_toStringAux___rarg(x_1, x_10, x_6);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_14);
x_17 = 0;
x_18 = l_List_toStringAux___rarg(x_1, x_17, x_15);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toStringAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toStringAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_toStringAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_toStringAux___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_toString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_List_toString_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_toString_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_List_toString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_instReprList___rarg___closed__1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 1;
x_6 = l_List_toStringAux___rarg(x_1, x_5, x_2);
x_7 = l_term_x5b___x5d___closed__3;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_term_x5b___x5d___closed__9;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = l_List_toStringAux___rarg(x_1, x_14, x_13);
x_16 = l_term_x5b___x5d___closed__3;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_term_x5b___x5d___closed__9;
x_19 = lean_string_append(x_17, x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString___rarg), 2, 0);
return x_2;
}
}
lean_object* l_instToStringList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toString___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_instToStringList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringList___rarg), 1, 0);
return x_2;
}
}
lean_object* l_instToStringPUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprUnit___closed__1;
return x_2;
}
}
lean_object* l_instToStringPUnit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringPUnit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringULift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_instToStringULift(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringULift___rarg), 2, 0);
return x_2;
}
}
lean_object* l_instToStringUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprUnit___closed__1;
return x_2;
}
}
lean_object* l_instToStringUnit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringUnit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* l_instToStringInt_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_instInhabitedInt___closed__1;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
lean_object* l_instToStringInt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringInt_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_instToStringInt_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instToStringInt_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_instToStringInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabitedInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_repr(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = l_Nat_repr(x_9);
x_11 = l_term_x2d_____closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_instToStringInt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringInt(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringChar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_alloc_closure((void*)(l_String_push___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToStringChar() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringChar___closed__1;
return x_1;
}
}
lean_object* l_instToStringFin___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
lean_object* l_instToStringFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringFin___rarg), 1, 0);
return x_2;
}
}
lean_object* l_instToStringFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringFin(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringUInt8(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt8(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt16(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt16(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt32(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt32(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt64(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_instToStringUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instToStringUInt64(x_2);
return x_3;
}
}
lean_object* l_instToStringUSize(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
}
lean_object* l_instToStringUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instToStringUSize(x_2);
return x_3;
}
}
lean_object* l_instToStringFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Format_defWidth;
x_3 = lean_format_pretty(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_addParenHeuristic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{");
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#[");
return x_1;
}
}
static lean_object* _init_l_addParenHeuristic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
lean_object* l_addParenHeuristic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_prec_x28___x29___closed__3;
x_3 = l_String_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_term_x5b___x5d___closed__3;
x_5 = l_String_isPrefixOf(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_addParenHeuristic___closed__1;
x_7 = l_String_isPrefixOf(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_addParenHeuristic___closed__2;
x_9 = l_String_isPrefixOf(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_string_utf8_byte_size(x_1);
x_11 = l_addParenHeuristic___closed__3;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_String_anyAux_loop(x_1, x_10, x_11, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_string_append(x_2, x_1);
x_15 = l_prec_x28___x29___closed__7;
x_16 = lean_string_append(x_14, x_15);
return x_16;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_addParenHeuristic___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_addParenHeuristic(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_instToStringOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instToStringOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringOption_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_instToStringOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(some ");
return x_1;
}
}
lean_object* l_instToStringOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_instReprOption___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_addParenHeuristic(x_5);
lean_dec(x_5);
x_7 = l_instToStringOption___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_prec_x28___x29___closed__7;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
}
}
lean_object* l_instToStringOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToStringOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_instToStringSum_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instToStringSum_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instToStringSum_match__1___rarg), 3, 0);
return x_4;
}
}
static lean_object* _init_l_instToStringSum___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(inl ");
return x_1;
}
}
static lean_object* _init_l_instToStringSum___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(inr ");
return x_1;
}
}
lean_object* l_instToStringSum___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_addParenHeuristic(x_5);
lean_dec(x_5);
x_7 = l_instToStringSum___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_prec_x28___x29___closed__7;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_2, x_11);
x_13 = l_addParenHeuristic(x_12);
lean_dec(x_12);
x_14 = l_instToStringSum___rarg___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_prec_x28___x29___closed__7;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
}
lean_object* l_instToStringSum(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSum___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instToStringProd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instToStringProd_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instToStringProd_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instToStringProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_prec_x28___x29___closed__3;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_term_x5b___x5d___closed__5;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_prec_x28___x29___closed__7;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
lean_object* l_instToStringProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringProd___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instToStringSigma_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_instToStringSigma_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instToStringSigma_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_instToStringSigma___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_instReprSigma___rarg___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_term_x5b___x5d___closed__5;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_2(x_2, x_4, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_instReprSigma___rarg___closed__6;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
lean_object* l_instToStringSigma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSigma___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instToStringSubtype___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_instToStringSubtype(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringSubtype___rarg), 2, 0);
return x_3;
}
}
lean_object* l_String_toInt_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_String_toInt_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_OptionT_instAlternativeOptionT___rarg(x_1);
return x_2;
}
}
lean_object* l_String_toInt_x3f___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_String_toInt_x3f___lambda__2___closed__1;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_nat_to_int(x_1);
x_6 = l_Int_instNegInt;
x_7 = lean_apply_1(x_6, x_5);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
static lean_object* _init_l_String_toInt_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toInt_x3f___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_String_toInt_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_String_toInt_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toInt_x3f___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_String_toInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_String_toInt_x3f___lambda__2___closed__1;
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_String_toNat_x3f(x_1);
lean_dec(x_1);
x_11 = l_String_toInt_x3f___closed__1;
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = l_String_toInt_x3f___closed__2;
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = l_String_toSubstring(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_drop(x_15, x_16);
x_18 = l_Substring_toNat_x3f(x_17);
x_19 = l_String_toInt_x3f___closed__3;
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_String_isNat(x_1);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_string_utf8_byte_size(x_1);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_8, x_9, x_2);
lean_dec(x_8);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_7);
x_13 = l_Substring_isNat(x_12);
return x_13;
}
}
}
lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_String_toInt_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_String_toInt_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_toInt_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_String_toInt_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Int expected");
return x_1;
}
}
lean_object* l_String_toInt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toInt_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Int_instInhabitedInt;
x_4 = l_String_toInt_x21___closed__1;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* l_instToStringExcept_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_instToStringExcept_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instToStringExcept_match__1___rarg), 3, 0);
return x_4;
}
}
static lean_object* _init_l_instToStringExcept___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error: ");
return x_1;
}
}
static lean_object* _init_l_instToStringExcept___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ok: ");
return x_1;
}
}
lean_object* l_instToStringExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_instToStringExcept___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_8);
x_10 = l_instToStringExcept___rarg___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
}
lean_object* l_instToStringExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToStringExcept___rarg), 3, 0);
return x_3;
}
}
lean_object* l_instReprExcept_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_4, x_7, x_2);
return x_8;
}
}
}
lean_object* l_instReprExcept_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instReprExcept_match__1___rarg), 4, 0);
return x_4;
}
}
static lean_object* _init_l_instReprExcept___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Except.error ");
return x_1;
}
}
static lean_object* _init_l_instReprExcept___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprExcept___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprExcept___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Except.ok ");
return x_1;
}
}
static lean_object* _init_l_instReprExcept___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprExcept___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_instReprExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_apply_2(x_1, x_5, x_6);
x_8 = l_instReprExcept___rarg___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1024u);
x_13 = lean_apply_2(x_2, x_11, x_12);
x_14 = l_instReprExcept___rarg___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Repr_addAppParen(x_15, x_4);
return x_16;
}
}
}
lean_object* l_instReprExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprExcept___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_instReprExcept___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instReprExcept___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Nat_Div(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_Int_Basic(lean_object*);
lean_object* initialize_Init_Data_Format_Basic(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Option(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_ToString_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instToStringChar___closed__1 = _init_l_instToStringChar___closed__1();
lean_mark_persistent(l_instToStringChar___closed__1);
l_instToStringChar = _init_l_instToStringChar();
lean_mark_persistent(l_instToStringChar);
l_addParenHeuristic___closed__1 = _init_l_addParenHeuristic___closed__1();
lean_mark_persistent(l_addParenHeuristic___closed__1);
l_addParenHeuristic___closed__2 = _init_l_addParenHeuristic___closed__2();
lean_mark_persistent(l_addParenHeuristic___closed__2);
l_addParenHeuristic___closed__3 = _init_l_addParenHeuristic___closed__3();
lean_mark_persistent(l_addParenHeuristic___closed__3);
l_instToStringOption___rarg___closed__1 = _init_l_instToStringOption___rarg___closed__1();
lean_mark_persistent(l_instToStringOption___rarg___closed__1);
l_instToStringSum___rarg___closed__1 = _init_l_instToStringSum___rarg___closed__1();
lean_mark_persistent(l_instToStringSum___rarg___closed__1);
l_instToStringSum___rarg___closed__2 = _init_l_instToStringSum___rarg___closed__2();
lean_mark_persistent(l_instToStringSum___rarg___closed__2);
l_String_toInt_x3f___lambda__2___closed__1 = _init_l_String_toInt_x3f___lambda__2___closed__1();
lean_mark_persistent(l_String_toInt_x3f___lambda__2___closed__1);
l_String_toInt_x3f___closed__1 = _init_l_String_toInt_x3f___closed__1();
lean_mark_persistent(l_String_toInt_x3f___closed__1);
l_String_toInt_x3f___closed__2 = _init_l_String_toInt_x3f___closed__2();
lean_mark_persistent(l_String_toInt_x3f___closed__2);
l_String_toInt_x3f___closed__3 = _init_l_String_toInt_x3f___closed__3();
lean_mark_persistent(l_String_toInt_x3f___closed__3);
l_String_toInt_x21___closed__1 = _init_l_String_toInt_x21___closed__1();
lean_mark_persistent(l_String_toInt_x21___closed__1);
l_instToStringExcept___rarg___closed__1 = _init_l_instToStringExcept___rarg___closed__1();
lean_mark_persistent(l_instToStringExcept___rarg___closed__1);
l_instToStringExcept___rarg___closed__2 = _init_l_instToStringExcept___rarg___closed__2();
lean_mark_persistent(l_instToStringExcept___rarg___closed__2);
l_instReprExcept___rarg___closed__1 = _init_l_instReprExcept___rarg___closed__1();
lean_mark_persistent(l_instReprExcept___rarg___closed__1);
l_instReprExcept___rarg___closed__2 = _init_l_instReprExcept___rarg___closed__2();
lean_mark_persistent(l_instReprExcept___rarg___closed__2);
l_instReprExcept___rarg___closed__3 = _init_l_instReprExcept___rarg___closed__3();
lean_mark_persistent(l_instReprExcept___rarg___closed__3);
l_instReprExcept___rarg___closed__4 = _init_l_instReprExcept___rarg___closed__4();
lean_mark_persistent(l_instReprExcept___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
