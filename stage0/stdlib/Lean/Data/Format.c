// Lean compiler output
// Module: Lean.Data.Format
// Imports: Init Lean.Data.Options
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
lean_object* l_Lean_toStringToFormat___rarg___closed__1;
lean_object* l_Lean_dataValueHasFormat___closed__1;
lean_object* l_Lean_List_format___rarg___closed__4;
lean_object* l_Lean_Format_spaceUptoLine___main(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Format_repr___main(lean_object*);
lean_object* l_String_toFormat(lean_object*);
lean_object* l___private_Lean_Data_Format_1__merge(lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOfAux___main(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_arrayHasFormat___spec__1___rarg(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l_Lean_kvMapHasFormat;
lean_object* l_Lean_Format_repr___main___closed__11;
lean_object* l_Lean_Format_spaceUptoLine_x27___main(lean_object*, lean_object*);
uint8_t l_Lean_Format_getUnicode(lean_object*);
lean_object* l_Lean_Format_getWidth___closed__3;
lean_object* l_Lean_Format_join(lean_object*);
lean_object* l_Lean_List_format___rarg___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_usizeHasFormat___boxed(lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_dataValueHasFormat;
lean_object* l_Lean_Format_HasAppend(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main(lean_object*);
lean_object* l_Nat_repeatAux___main___at_String_pushn___spec__1(uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Format_indentOption___closed__2;
lean_object* l_Lean_formatDataValue___closed__1;
lean_object* l_Lean_Format_getIndent___boxed(lean_object*);
lean_object* l_Lean_Format_getIndent___closed__1;
lean_object* l_Lean_Format_prefixJoin___main(lean_object*);
lean_object* l_Lean_HasRepr___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Format_bracket(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_spaceUptoLine_x27___main___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Format_repr(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l_Lean_Format_repr___main___closed__12;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_arrayHasFormat(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_1__merge___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_listHasFormat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_formatEntry(lean_object*);
lean_object* l_Lean_Format_prefixJoin___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_format___rarg(lean_object*, lean_object*);
lean_object* l_Lean_usizeHasFormat(size_t);
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_Lean_Format_be___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_widthOption(lean_object*);
extern lean_object* l_Int_zero;
lean_object* l_Lean_List_format___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinArraySep___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_uint16HasFormat___boxed(lean_object*);
lean_object* l_Lean_Format_spaceUptoLine___main___closed__1;
lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_uint64HasFormat___boxed(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Format_defWidth;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSuffix(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__13;
lean_object* l_Lean_Format_pretty___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Option_format(lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l_Lean_Format_repr___main___closed__6;
lean_object* l_Lean_Format_indentOption(lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Format_repr___main___closed__17;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Format_widthOption___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Format_widthOption___closed__1;
lean_object* l_Lean_formatHasToString(lean_object*);
lean_object* l_Lean_Option_format___rarg___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Format_widthOption___closed__3;
lean_object* l_Lean_HasRepr___closed__3;
lean_object* l_Lean_Format_be(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Option_format___rarg___closed__2;
lean_object* l_Lean_Format_spaceUptoLine___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatDataValue___closed__3;
lean_object* l_Lean_entryHasFormat___closed__1;
lean_object* l_Lean_List_format(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__2;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Format_fill(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__4;
lean_object* l_Lean_Format_repr___main___closed__1;
lean_object* l_Lean_toStringToFormat___rarg(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg___closed__1;
lean_object* l_Lean_formatEntry___closed__2;
lean_object* l_Lean_Format_join___boxed(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__8;
lean_object* l_Lean_Format_spaceUptoLine_x27(lean_object*, lean_object*);
lean_object* l_Lean_Format_join___closed__1;
lean_object* lean_format_group(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__19;
lean_object* l_Lean_optionHasFormat(lean_object*);
lean_object* l_Lean_Format_joinArraySep___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_repr___main___closed__9;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_kvMapHasFormat___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_formatDataValue___closed__4;
lean_object* l_Lean_formatKVMap(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_prodHasFormat(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr___lambda__1(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__18;
lean_object* l_Lean_Format_repr___main___closed__15;
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Format_defUnicode;
lean_object* l_Lean_Format_getUnicode___closed__2;
lean_object* l_Lean_Format_getUnicode___closed__1;
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Lean_Format_joinSep___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_repr___main___closed__7;
lean_object* l_Lean_Format_Inhabited;
lean_object* l_Lean_Format_repr___main___closed__3;
lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Lean_Format_isNil___boxed(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Format_join___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Format_HasCoe(lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Lean_Format_getUnicode___boxed(lean_object*);
lean_object* l_Lean_Format_SpaceResult_inhabited;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_be___main___closed__1;
lean_object* l_Lean_Format_be___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_repr___main___closed__14;
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Format_unicodeOption___closed__3;
lean_object* l_Lean_Format_repr___main___closed__5;
lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_Format_prefixJoin(lean_object*);
lean_object* l_Lean_Format_joinSuffix___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_formatDataValue___closed__2;
lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Format_unicodeOption___closed__1;
lean_object* l_Lean_Format_joinSep(lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg(lean_object*, lean_object*);
lean_object* l_String_offsetOfPosAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_paren___closed__1;
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Lean_fmt(lean_object*);
lean_object* l_Lean_Format_spaceUptoLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_spaceUptoLine___main___closed__2;
lean_object* l_Lean_nameHasFormat(lean_object*);
lean_object* l_Lean_Format_getWidth___closed__2;
lean_object* l_Lean_Format_getWidth___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_toStringToFormat(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Format_getWidth___boxed(lean_object*);
lean_object* l_Lean_uint64HasFormat(uint64_t);
lean_object* l_Lean_formatHasFormat;
lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_uint32HasFormat(uint32_t);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_Format_be___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_Format_Coe(lean_object*);
lean_object* l_Lean_optionHasFormat___rarg(lean_object*);
lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_Format_spaceUptoLine_x27___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Format_getIndent(lean_object*);
uint8_t l_Lean_Format_FlattenBehavior_hasBeq(uint8_t, uint8_t);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasRepr;
lean_object* l_Lean_natHasFormat(lean_object*);
lean_object* l_Lean_Format_paren___closed__4;
lean_object* l_Lean_Format_getWidth___closed__4;
lean_object* l_Lean_Format_SpaceResult_inhabited___closed__1;
lean_object* l_Lean_Format_joinSuffix___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_prodHasFormat___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatDataValue(lean_object*);
lean_object* l_Lean_Option_format___rarg___closed__3;
lean_object* l_Lean_entryHasFormat;
lean_object* l_Lean_toStringToFormat___rarg___lambda__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_uint16HasFormat(uint16_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_uint32HasFormat___boxed(lean_object*);
lean_object* l_Lean_Format_FlattenBehavior_hasBeq___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Format_join___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Format_indentOption___closed__3;
lean_object* l_Lean_fmt___at_Lean_arrayHasFormat___spec__1(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Format_defIndent;
lean_object* l_Lean_Format_joinArraySep(lean_object*);
lean_object* l_Lean_Format_indentOption___closed__1;
lean_object* l_Lean_List_format___rarg___closed__3;
lean_object* lean_format_append(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSuffix___main(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Format_repr___main___closed__10;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Format_prefixJoin___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Data_Format_2__pushGroup(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_listHasFormat___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1(lean_object*);
lean_object* l_Lean_Format_sbracket(lean_object*);
lean_object* l_Lean_Format_unicodeOption___closed__2;
lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_Format_getIndent___closed__2;
lean_object* l_Lean_stringHasFormat(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Format_spaceUptoLine(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Format_getWidth(lean_object*);
lean_object* l_Lean_Format_paren(lean_object*);
lean_object* l_Lean_Format_unicodeOption(lean_object*);
lean_object* l___private_Lean_Data_Format_2__pushGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Format_FlattenBehavior_hasBeq(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
lean_object* l_Lean_Format_FlattenBehavior_hasBeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Format_FlattenBehavior_hasBeq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Format_fill(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* lean_format_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_format_group(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_HasAppend(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_HasCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Format_Coe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_List_foldl___main___at_Lean_Format_join___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l_Lean_Format_join___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Format_join(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Format_join___closed__1;
x_3 = l_List_foldl___main___at_Lean_Format_join___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_Format_join___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Format_join___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Format_join___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Format_join(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Format_isNil(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Format_isNil___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Format_isNil(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_SpaceResult_inhabited___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Format_SpaceResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Format_SpaceResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_Format_1__merge(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_nat_sub(x_1, x_4);
x_8 = lean_apply_1(x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_12);
return x_15;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l___private_Lean_Data_Format_1__merge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_1__merge(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Format_spaceUptoLine___main___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Format_spaceUptoLine___main___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_Format_spaceUptoLine___main(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; 
x_4 = l_Lean_Format_SpaceResult_inhabited___closed__1;
return x_4;
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Format_spaceUptoLine___main___closed__1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Format_spaceUptoLine___main___closed__2;
return x_6;
}
}
case 2:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 10;
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_String_posOfAux___main(x_7, x_8, x_9, x_10);
x_12 = l_String_offsetOfPosAux___main(x_7, x_11, x_10, x_10);
x_13 = lean_nat_dec_eq(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
}
case 3:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 1);
x_1 = x_18;
goto _start;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = l_Lean_Format_spaceUptoLine___main(x_20, x_2, x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_3, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_22);
x_26 = lean_nat_sub(x_3, x_23);
x_27 = l_Lean_Format_spaceUptoLine___main(x_21, x_2, x_26);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_nat_add(x_23, x_29);
lean_dec(x_29);
lean_dec(x_23);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_31);
return x_34;
}
}
else
{
lean_dec(x_23);
return x_22;
}
}
else
{
lean_dec(x_23);
return x_22;
}
}
default: 
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = 1;
x_1 = x_35;
x_2 = x_36;
goto _start;
}
}
}
}
lean_object* l_Lean_Format_spaceUptoLine___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Format_spaceUptoLine___main(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Format_spaceUptoLine(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Format_spaceUptoLine___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_spaceUptoLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Format_spaceUptoLine(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Format_spaceUptoLine_x27___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Format_SpaceResult_inhabited___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Format_spaceUptoLine___main(x_15, x_10, x_2);
lean_dec(x_15);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_5, 1, x_8);
lean_ctor_set(x_5, 0, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
x_20 = lean_nat_sub(x_2, x_17);
x_21 = l_Lean_Format_spaceUptoLine_x27___main(x_5, x_20);
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_nat_add(x_17, x_23);
lean_dec(x_23);
lean_dec(x_17);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_25);
return x_28;
}
}
else
{
lean_dec(x_17);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_dec(x_17);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Format_spaceUptoLine___main(x_31, x_10, x_2);
lean_dec(x_31);
lean_ctor_set(x_4, 0, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_nat_dec_lt(x_2, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
x_37 = lean_nat_sub(x_2, x_34);
x_38 = l_Lean_Format_spaceUptoLine_x27___main(x_33, x_37);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_nat_add(x_34, x_40);
lean_dec(x_40);
lean_dec(x_34);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_39);
return x_43;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
return x_32;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
return x_32;
}
}
}
else
{
uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_45 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
lean_dec(x_4);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_48 = x_5;
} else {
 lean_dec_ref(x_5);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Format_spaceUptoLine___main(x_49, x_44, x_2);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 1, x_45);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_nat_dec_lt(x_2, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_50);
x_56 = lean_nat_sub(x_2, x_53);
x_57 = l_Lean_Format_spaceUptoLine_x27___main(x_52, x_56);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_nat_add(x_53, x_59);
lean_dec(x_59);
lean_dec(x_53);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_58);
return x_62;
}
else
{
lean_dec(x_53);
lean_dec(x_52);
return x_50;
}
}
else
{
lean_dec(x_53);
lean_dec(x_52);
return x_50;
}
}
}
}
}
}
lean_object* l_Lean_Format_spaceUptoLine_x27___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Format_spaceUptoLine_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_spaceUptoLine_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_2__pushGroup(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = 1;
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 1, x_1);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Lean_Format_spaceUptoLine_x27___main(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_nat_dec_le(x_9, x_4);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 1, x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = 0;
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 1, x_1);
lean_inc(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = l_Lean_Format_spaceUptoLine_x27___main(x_15, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_le(x_17, x_4);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
lean_object* l___private_Lean_Data_Format_2__pushGroup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Data_Format_2__pushGroup(x_5, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Format_be___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
lean_object* l_Lean_Format_be___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
lean_ctor_set(x_5, 0, x_15);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_5);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_11);
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_24 = x_6;
} else {
 lean_dec_ref(x_6);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
x_4 = x_26;
goto _start;
}
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_4, 1);
x_30 = lean_ctor_get(x_4, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get(x_5, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_36 = x_6;
} else {
 lean_dec_ref(x_6);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
lean_inc(x_35);
lean_ctor_set(x_5, 0, x_35);
if (x_33 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_35);
lean_free_object(x_4);
x_57 = lean_box(x_32);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
x_38 = x_58;
goto block_56;
}
else
{
uint8_t x_59; lean_object* x_60; 
lean_dec(x_5);
x_59 = 0;
lean_inc(x_35);
x_60 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_60, 0, x_35);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 1, x_33);
lean_inc(x_29);
lean_ctor_set(x_4, 0, x_60);
if (x_32 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_nat_dec_le(x_62, x_1);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_64, 0, x_35);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 1, x_33);
x_65 = lean_box(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_38 = x_66;
goto block_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_nat_sub(x_1, x_2);
lean_inc(x_4);
x_68 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_nat_dec_le(x_69, x_67);
lean_dec(x_67);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_nat_dec_le(x_72, x_1);
lean_dec(x_72);
x_74 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_74, 0, x_35);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 1, x_33);
x_75 = lean_box(x_59);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_38 = x_76;
goto block_56;
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_4);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_78, 0, x_35);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 1, x_33);
x_79 = lean_box(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_38 = x_80;
goto block_56;
}
}
}
block_56:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Int_toNat(x_37);
lean_dec(x_37);
x_43 = l_Lean_Format_be___main___closed__1;
x_44 = lean_string_append(x_3, x_43);
x_45 = 32;
lean_inc(x_42);
x_46 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_45, x_42, x_44);
if (lean_is_scalar(x_36)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_36;
}
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_29);
x_2 = x_42;
x_3 = x_46;
x_4 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_2, x_50);
lean_dec(x_2);
x_52 = l_String_Iterator_HasRepr___closed__2;
x_53 = lean_string_append(x_3, x_52);
if (lean_is_scalar(x_36)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_36;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_29);
x_2 = x_51;
x_3 = x_53;
x_4 = x_54;
goto _start;
}
}
}
else
{
uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_82 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_84 = x_6;
} else {
 lean_dec_ref(x_6);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_9, 1);
lean_inc(x_85);
lean_dec(x_9);
lean_inc(x_83);
x_86 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_81);
lean_ctor_set_uint8(x_86, sizeof(void*)*1 + 1, x_82);
if (x_82 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_83);
lean_free_object(x_4);
x_106 = lean_box(x_81);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_86);
x_87 = x_107;
goto block_105;
}
else
{
uint8_t x_108; lean_object* x_109; 
lean_dec(x_86);
x_108 = 0;
lean_inc(x_83);
x_109 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_109, 0, x_83);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 1, x_82);
lean_inc(x_29);
lean_ctor_set(x_4, 0, x_109);
if (x_81 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_1);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_nat_dec_le(x_111, x_1);
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_113, 0, x_83);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 1, x_82);
x_114 = lean_box(x_108);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_87 = x_115;
goto block_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_nat_sub(x_1, x_2);
lean_inc(x_4);
x_117 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_nat_dec_le(x_118, x_116);
lean_dec(x_116);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = l_Lean_Format_spaceUptoLine_x27___main(x_4, x_1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_nat_dec_le(x_121, x_1);
lean_dec(x_121);
x_123 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_123, 0, x_83);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*1 + 1, x_82);
x_124 = lean_box(x_108);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_87 = x_125;
goto block_105;
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_126 = 1;
x_127 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_127, 0, x_83);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 1, x_82);
x_128 = lean_box(x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_87 = x_129;
goto block_105;
}
}
}
block_105:
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint32_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Int_toNat(x_85);
lean_dec(x_85);
x_92 = l_Lean_Format_be___main___closed__1;
x_93 = lean_string_append(x_3, x_92);
x_94 = 32;
lean_inc(x_91);
x_95 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_94, x_91, x_93);
if (lean_is_scalar(x_84)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_84;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_29);
x_2 = x_91;
x_3 = x_95;
x_4 = x_96;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_2, x_99);
lean_dec(x_2);
x_101 = l_String_Iterator_HasRepr___closed__2;
x_102 = lean_string_append(x_3, x_101);
if (lean_is_scalar(x_84)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_84;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_29);
x_2 = x_100;
x_3 = x_102;
x_4 = x_103;
goto _start;
}
}
}
}
else
{
lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_4, 1);
lean_inc(x_130);
lean_dec(x_4);
x_131 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_132 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_133 = x_5;
} else {
 lean_dec_ref(x_5);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_6, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_135 = x_6;
} else {
 lean_dec_ref(x_6);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_9, 1);
lean_inc(x_136);
lean_dec(x_9);
lean_inc(x_134);
if (lean_is_scalar(x_133)) {
 x_137 = lean_alloc_ctor(0, 1, 2);
} else {
 x_137 = x_133;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_131);
lean_ctor_set_uint8(x_137, sizeof(void*)*1 + 1, x_132);
if (x_132 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_134);
x_157 = lean_box(x_131);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_137);
x_138 = x_158;
goto block_156;
}
else
{
uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_137);
x_159 = 0;
lean_inc(x_134);
x_160 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_160, 0, x_134);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*1 + 1, x_132);
lean_inc(x_130);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_130);
if (x_131 == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = l_Lean_Format_spaceUptoLine_x27___main(x_161, x_1);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_nat_dec_le(x_163, x_1);
lean_dec(x_163);
x_165 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_165, 0, x_134);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*1 + 1, x_132);
x_166 = lean_box(x_159);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_138 = x_167;
goto block_156;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_nat_sub(x_1, x_2);
lean_inc(x_161);
x_169 = l_Lean_Format_spaceUptoLine_x27___main(x_161, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_nat_dec_le(x_170, x_168);
lean_dec(x_168);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = l_Lean_Format_spaceUptoLine_x27___main(x_161, x_1);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_nat_dec_le(x_173, x_1);
lean_dec(x_173);
x_175 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_175, 0, x_134);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*1 + 1, x_132);
x_176 = lean_box(x_159);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_138 = x_177;
goto block_156;
}
else
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_161);
x_178 = 1;
x_179 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_179, 0, x_134);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*1 + 1, x_132);
x_180 = lean_box(x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_138 = x_181;
goto block_156;
}
}
}
block_156:
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint32_t x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_2);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = l_Int_toNat(x_136);
lean_dec(x_136);
x_143 = l_Lean_Format_be___main___closed__1;
x_144 = lean_string_append(x_3, x_143);
x_145 = 32;
lean_inc(x_142);
x_146 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_145, x_142, x_144);
if (lean_is_scalar(x_135)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_135;
}
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_130);
x_2 = x_142;
x_3 = x_146;
x_4 = x_147;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_136);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
lean_dec(x_138);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_add(x_2, x_150);
lean_dec(x_2);
x_152 = l_String_Iterator_HasRepr___closed__2;
x_153 = lean_string_append(x_3, x_152);
if (lean_is_scalar(x_135)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_135;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_130);
x_2 = x_151;
x_3 = x_153;
x_4 = x_154;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_4, 1);
lean_inc(x_182);
lean_dec(x_4);
x_183 = !lean_is_exclusive(x_5);
if (x_183 == 0)
{
uint8_t x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_185 = lean_ctor_get(x_5, 0);
lean_dec(x_185);
x_186 = !lean_is_exclusive(x_6);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_6, 1);
x_188 = lean_ctor_get(x_6, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_9);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_9, 1);
x_191 = lean_ctor_get(x_9, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_10);
if (x_192 == 0)
{
lean_object* x_193; uint32_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_193 = lean_ctor_get(x_10, 0);
x_194 = 10;
x_195 = lean_string_utf8_byte_size(x_193);
x_196 = lean_unsigned_to_nat(0u);
x_197 = l_String_posOfAux___main(x_193, x_194, x_195, x_196);
x_198 = lean_nat_dec_eq(x_197, x_195);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint32_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_free_object(x_5);
lean_dec(x_2);
x_199 = lean_string_utf8_extract(x_193, x_196, x_197);
x_200 = lean_string_append(x_3, x_199);
lean_dec(x_199);
x_201 = 32;
x_202 = l_Int_toNat(x_190);
x_203 = l_Lean_Format_be___main___closed__1;
lean_inc(x_202);
x_204 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_201, x_202, x_203);
x_205 = lean_string_append(x_200, x_204);
lean_dec(x_204);
x_206 = lean_string_utf8_next(x_193, x_197);
lean_dec(x_197);
x_207 = lean_string_utf8_extract(x_193, x_206, x_195);
lean_dec(x_195);
lean_dec(x_206);
lean_dec(x_193);
lean_ctor_set(x_10, 0, x_207);
x_208 = lean_nat_sub(x_1, x_202);
x_209 = l___private_Lean_Data_Format_2__pushGroup(x_184, x_6, x_182, x_208);
lean_dec(x_208);
x_2 = x_202;
x_3 = x_205;
x_4 = x_209;
goto _start;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_197);
lean_dec(x_195);
lean_free_object(x_10);
lean_free_object(x_9);
lean_dec(x_190);
x_211 = lean_string_length(x_193);
x_212 = lean_nat_add(x_2, x_211);
lean_dec(x_211);
lean_dec(x_2);
x_213 = lean_string_append(x_3, x_193);
lean_dec(x_193);
lean_ctor_set(x_5, 0, x_187);
lean_ctor_set(x_6, 1, x_182);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_212;
x_3 = x_213;
x_4 = x_6;
goto _start;
}
}
else
{
lean_object* x_215; uint32_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_215 = lean_ctor_get(x_10, 0);
lean_inc(x_215);
lean_dec(x_10);
x_216 = 10;
x_217 = lean_string_utf8_byte_size(x_215);
x_218 = lean_unsigned_to_nat(0u);
x_219 = l_String_posOfAux___main(x_215, x_216, x_217, x_218);
x_220 = lean_nat_dec_eq(x_219, x_217);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint32_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_free_object(x_5);
lean_dec(x_2);
x_221 = lean_string_utf8_extract(x_215, x_218, x_219);
x_222 = lean_string_append(x_3, x_221);
lean_dec(x_221);
x_223 = 32;
x_224 = l_Int_toNat(x_190);
x_225 = l_Lean_Format_be___main___closed__1;
lean_inc(x_224);
x_226 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_223, x_224, x_225);
x_227 = lean_string_append(x_222, x_226);
lean_dec(x_226);
x_228 = lean_string_utf8_next(x_215, x_219);
lean_dec(x_219);
x_229 = lean_string_utf8_extract(x_215, x_228, x_217);
lean_dec(x_217);
lean_dec(x_228);
lean_dec(x_215);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_9, 0, x_230);
x_231 = lean_nat_sub(x_1, x_224);
x_232 = l___private_Lean_Data_Format_2__pushGroup(x_184, x_6, x_182, x_231);
lean_dec(x_231);
x_2 = x_224;
x_3 = x_227;
x_4 = x_232;
goto _start;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_219);
lean_dec(x_217);
lean_free_object(x_9);
lean_dec(x_190);
x_234 = lean_string_length(x_215);
x_235 = lean_nat_add(x_2, x_234);
lean_dec(x_234);
lean_dec(x_2);
x_236 = lean_string_append(x_3, x_215);
lean_dec(x_215);
lean_ctor_set(x_5, 0, x_187);
lean_ctor_set(x_6, 1, x_182);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_235;
x_3 = x_236;
x_4 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint32_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_238 = lean_ctor_get(x_9, 1);
lean_inc(x_238);
lean_dec(x_9);
x_239 = lean_ctor_get(x_10, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_240 = x_10;
} else {
 lean_dec_ref(x_10);
 x_240 = lean_box(0);
}
x_241 = 10;
x_242 = lean_string_utf8_byte_size(x_239);
x_243 = lean_unsigned_to_nat(0u);
x_244 = l_String_posOfAux___main(x_239, x_241, x_242, x_243);
x_245 = lean_nat_dec_eq(x_244, x_242);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; uint32_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_free_object(x_5);
lean_dec(x_2);
x_246 = lean_string_utf8_extract(x_239, x_243, x_244);
x_247 = lean_string_append(x_3, x_246);
lean_dec(x_246);
x_248 = 32;
x_249 = l_Int_toNat(x_238);
x_250 = l_Lean_Format_be___main___closed__1;
lean_inc(x_249);
x_251 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_248, x_249, x_250);
x_252 = lean_string_append(x_247, x_251);
lean_dec(x_251);
x_253 = lean_string_utf8_next(x_239, x_244);
lean_dec(x_244);
x_254 = lean_string_utf8_extract(x_239, x_253, x_242);
lean_dec(x_242);
lean_dec(x_253);
lean_dec(x_239);
if (lean_is_scalar(x_240)) {
 x_255 = lean_alloc_ctor(2, 1, 0);
} else {
 x_255 = x_240;
}
lean_ctor_set(x_255, 0, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_238);
lean_ctor_set(x_6, 0, x_256);
x_257 = lean_nat_sub(x_1, x_249);
x_258 = l___private_Lean_Data_Format_2__pushGroup(x_184, x_6, x_182, x_257);
lean_dec(x_257);
x_2 = x_249;
x_3 = x_252;
x_4 = x_258;
goto _start;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_238);
x_260 = lean_string_length(x_239);
x_261 = lean_nat_add(x_2, x_260);
lean_dec(x_260);
lean_dec(x_2);
x_262 = lean_string_append(x_3, x_239);
lean_dec(x_239);
lean_ctor_set(x_5, 0, x_187);
lean_ctor_set(x_6, 1, x_182);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_261;
x_3 = x_262;
x_4 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint32_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_264 = lean_ctor_get(x_6, 1);
lean_inc(x_264);
lean_dec(x_6);
x_265 = lean_ctor_get(x_9, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_266 = x_9;
} else {
 lean_dec_ref(x_9);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_10, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_268 = x_10;
} else {
 lean_dec_ref(x_10);
 x_268 = lean_box(0);
}
x_269 = 10;
x_270 = lean_string_utf8_byte_size(x_267);
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_String_posOfAux___main(x_267, x_269, x_270, x_271);
x_273 = lean_nat_dec_eq(x_272, x_270);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; uint32_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_free_object(x_5);
lean_dec(x_2);
x_274 = lean_string_utf8_extract(x_267, x_271, x_272);
x_275 = lean_string_append(x_3, x_274);
lean_dec(x_274);
x_276 = 32;
x_277 = l_Int_toNat(x_265);
x_278 = l_Lean_Format_be___main___closed__1;
lean_inc(x_277);
x_279 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_276, x_277, x_278);
x_280 = lean_string_append(x_275, x_279);
lean_dec(x_279);
x_281 = lean_string_utf8_next(x_267, x_272);
lean_dec(x_272);
x_282 = lean_string_utf8_extract(x_267, x_281, x_270);
lean_dec(x_270);
lean_dec(x_281);
lean_dec(x_267);
if (lean_is_scalar(x_268)) {
 x_283 = lean_alloc_ctor(2, 1, 0);
} else {
 x_283 = x_268;
}
lean_ctor_set(x_283, 0, x_282);
if (lean_is_scalar(x_266)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_266;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_265);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_264);
x_286 = lean_nat_sub(x_1, x_277);
x_287 = l___private_Lean_Data_Format_2__pushGroup(x_184, x_285, x_182, x_286);
lean_dec(x_286);
x_2 = x_277;
x_3 = x_280;
x_4 = x_287;
goto _start;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_265);
x_289 = lean_string_length(x_267);
x_290 = lean_nat_add(x_2, x_289);
lean_dec(x_289);
lean_dec(x_2);
x_291 = lean_string_append(x_3, x_267);
lean_dec(x_267);
lean_ctor_set(x_5, 0, x_264);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_5);
lean_ctor_set(x_292, 1, x_182);
x_2 = x_290;
x_3 = x_291;
x_4 = x_292;
goto _start;
}
}
}
else
{
uint8_t x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint32_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_294 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_295 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_296 = lean_ctor_get(x_6, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_297 = x_6;
} else {
 lean_dec_ref(x_6);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_9, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_299 = x_9;
} else {
 lean_dec_ref(x_9);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_10, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_301 = x_10;
} else {
 lean_dec_ref(x_10);
 x_301 = lean_box(0);
}
x_302 = 10;
x_303 = lean_string_utf8_byte_size(x_300);
x_304 = lean_unsigned_to_nat(0u);
x_305 = l_String_posOfAux___main(x_300, x_302, x_303, x_304);
x_306 = lean_nat_dec_eq(x_305, x_303);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; uint32_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_2);
x_307 = lean_string_utf8_extract(x_300, x_304, x_305);
x_308 = lean_string_append(x_3, x_307);
lean_dec(x_307);
x_309 = 32;
x_310 = l_Int_toNat(x_298);
x_311 = l_Lean_Format_be___main___closed__1;
lean_inc(x_310);
x_312 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_309, x_310, x_311);
x_313 = lean_string_append(x_308, x_312);
lean_dec(x_312);
x_314 = lean_string_utf8_next(x_300, x_305);
lean_dec(x_305);
x_315 = lean_string_utf8_extract(x_300, x_314, x_303);
lean_dec(x_303);
lean_dec(x_314);
lean_dec(x_300);
if (lean_is_scalar(x_301)) {
 x_316 = lean_alloc_ctor(2, 1, 0);
} else {
 x_316 = x_301;
}
lean_ctor_set(x_316, 0, x_315);
if (lean_is_scalar(x_299)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_299;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_297;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_296);
x_319 = lean_nat_sub(x_1, x_310);
x_320 = l___private_Lean_Data_Format_2__pushGroup(x_295, x_318, x_182, x_319);
lean_dec(x_319);
x_2 = x_310;
x_3 = x_313;
x_4 = x_320;
goto _start;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_299);
lean_dec(x_298);
x_322 = lean_string_length(x_300);
x_323 = lean_nat_add(x_2, x_322);
lean_dec(x_322);
lean_dec(x_2);
x_324 = lean_string_append(x_3, x_300);
lean_dec(x_300);
x_325 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_325, 0, x_296);
lean_ctor_set_uint8(x_325, sizeof(void*)*1, x_294);
lean_ctor_set_uint8(x_325, sizeof(void*)*1 + 1, x_295);
if (lean_is_scalar(x_297)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_297;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_182);
x_2 = x_323;
x_3 = x_324;
x_4 = x_326;
goto _start;
}
}
}
case 3:
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_4);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_ctor_get(x_4, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_5);
if (x_330 == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_5, 0);
lean_dec(x_331);
x_332 = !lean_is_exclusive(x_6);
if (x_332 == 0)
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_ctor_get(x_6, 0);
lean_dec(x_333);
x_334 = !lean_is_exclusive(x_9);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_ctor_get(x_9, 1);
x_336 = lean_ctor_get(x_9, 0);
lean_dec(x_336);
x_337 = lean_ctor_get(x_10, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_10, 1);
lean_inc(x_338);
lean_dec(x_10);
x_339 = lean_int_add(x_335, x_337);
lean_dec(x_337);
lean_dec(x_335);
lean_ctor_set(x_9, 1, x_339);
lean_ctor_set(x_9, 0, x_338);
goto _start;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_9, 1);
lean_inc(x_341);
lean_dec(x_9);
x_342 = lean_ctor_get(x_10, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_10, 1);
lean_inc(x_343);
lean_dec(x_10);
x_344 = lean_int_add(x_341, x_342);
lean_dec(x_342);
lean_dec(x_341);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_6, 0, x_345);
goto _start;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_347 = lean_ctor_get(x_6, 1);
lean_inc(x_347);
lean_dec(x_6);
x_348 = lean_ctor_get(x_9, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_349 = x_9;
} else {
 lean_dec_ref(x_9);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_10, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_10, 1);
lean_inc(x_351);
lean_dec(x_10);
x_352 = lean_int_add(x_348, x_350);
lean_dec(x_350);
lean_dec(x_348);
if (lean_is_scalar(x_349)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_349;
}
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_347);
lean_ctor_set(x_5, 0, x_354);
goto _start;
}
}
else
{
uint8_t x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_356 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_357 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_358 = lean_ctor_get(x_6, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_359 = x_6;
} else {
 lean_dec_ref(x_6);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_9, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_361 = x_9;
} else {
 lean_dec_ref(x_9);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_10, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_10, 1);
lean_inc(x_363);
lean_dec(x_10);
x_364 = lean_int_add(x_360, x_362);
lean_dec(x_362);
lean_dec(x_360);
if (lean_is_scalar(x_361)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_361;
}
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
if (lean_is_scalar(x_359)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_359;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_358);
x_367 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*1, x_356);
lean_ctor_set_uint8(x_367, sizeof(void*)*1 + 1, x_357);
lean_ctor_set(x_4, 0, x_367);
goto _start;
}
}
else
{
lean_object* x_369; uint8_t x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_369 = lean_ctor_get(x_4, 1);
lean_inc(x_369);
lean_dec(x_4);
x_370 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_371 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_372 = x_5;
} else {
 lean_dec_ref(x_5);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_6, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_374 = x_6;
} else {
 lean_dec_ref(x_6);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_9, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_376 = x_9;
} else {
 lean_dec_ref(x_9);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_10, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_10, 1);
lean_inc(x_378);
lean_dec(x_10);
x_379 = lean_int_add(x_375, x_377);
lean_dec(x_377);
lean_dec(x_375);
if (lean_is_scalar(x_376)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_376;
}
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
if (lean_is_scalar(x_374)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_374;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_373);
if (lean_is_scalar(x_372)) {
 x_382 = lean_alloc_ctor(0, 1, 2);
} else {
 x_382 = x_372;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*1, x_370);
lean_ctor_set_uint8(x_382, sizeof(void*)*1 + 1, x_371);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_369);
x_4 = x_383;
goto _start;
}
}
case 4:
{
uint8_t x_385; 
x_385 = !lean_is_exclusive(x_4);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_386 = lean_ctor_get(x_4, 1);
x_387 = lean_ctor_get(x_4, 0);
lean_dec(x_387);
x_388 = !lean_is_exclusive(x_5);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_5, 0);
lean_dec(x_389);
x_390 = !lean_is_exclusive(x_6);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_6, 0);
lean_dec(x_391);
x_392 = !lean_is_exclusive(x_9);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_9, 1);
x_394 = lean_ctor_get(x_9, 0);
lean_dec(x_394);
x_395 = lean_ctor_get(x_10, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_10, 1);
lean_inc(x_396);
lean_dec(x_10);
lean_inc(x_393);
lean_ctor_set(x_9, 0, x_395);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_6, 0, x_397);
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_4, 0, x_9);
lean_ctor_set(x_5, 0, x_4);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_5);
lean_ctor_set(x_398, 1, x_386);
x_4 = x_398;
goto _start;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_400 = lean_ctor_get(x_9, 1);
lean_inc(x_400);
lean_dec(x_9);
x_401 = lean_ctor_get(x_10, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_10, 1);
lean_inc(x_402);
lean_dec(x_10);
lean_inc(x_400);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_400);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_400);
lean_ctor_set(x_6, 0, x_404);
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_4, 0, x_403);
lean_ctor_set(x_5, 0, x_4);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_5);
lean_ctor_set(x_405, 1, x_386);
x_4 = x_405;
goto _start;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_407 = lean_ctor_get(x_6, 1);
lean_inc(x_407);
lean_dec(x_6);
x_408 = lean_ctor_get(x_9, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_409 = x_9;
} else {
 lean_dec_ref(x_9);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_10, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_10, 1);
lean_inc(x_411);
lean_dec(x_10);
lean_inc(x_408);
if (lean_is_scalar(x_409)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_409;
}
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_408);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_408);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_407);
lean_ctor_set(x_4, 1, x_414);
lean_ctor_set(x_4, 0, x_412);
lean_ctor_set(x_5, 0, x_4);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_5);
lean_ctor_set(x_415, 1, x_386);
x_4 = x_415;
goto _start;
}
}
else
{
uint8_t x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_417 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_418 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_419 = lean_ctor_get(x_6, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_420 = x_6;
} else {
 lean_dec_ref(x_6);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_9, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_422 = x_9;
} else {
 lean_dec_ref(x_9);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_10, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_10, 1);
lean_inc(x_424);
lean_dec(x_10);
lean_inc(x_421);
if (lean_is_scalar(x_422)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_422;
}
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_421);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_421);
if (lean_is_scalar(x_420)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_420;
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_419);
lean_ctor_set(x_4, 1, x_427);
lean_ctor_set(x_4, 0, x_425);
x_428 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_428, 0, x_4);
lean_ctor_set_uint8(x_428, sizeof(void*)*1, x_417);
lean_ctor_set_uint8(x_428, sizeof(void*)*1 + 1, x_418);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_386);
x_4 = x_429;
goto _start;
}
}
else
{
lean_object* x_431; uint8_t x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_431 = lean_ctor_get(x_4, 1);
lean_inc(x_431);
lean_dec(x_4);
x_432 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_433 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_434 = x_5;
} else {
 lean_dec_ref(x_5);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_6, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_436 = x_6;
} else {
 lean_dec_ref(x_6);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_9, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_438 = x_9;
} else {
 lean_dec_ref(x_9);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_10, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_10, 1);
lean_inc(x_440);
lean_dec(x_10);
lean_inc(x_437);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_437);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_437);
if (lean_is_scalar(x_436)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_436;
}
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_435);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_443);
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(0, 1, 2);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_432);
lean_ctor_set_uint8(x_445, sizeof(void*)*1 + 1, x_433);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_431);
x_4 = x_446;
goto _start;
}
}
default: 
{
uint8_t x_448; 
x_448 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_448 == 0)
{
uint8_t x_449; 
x_449 = !lean_is_exclusive(x_4);
if (x_449 == 0)
{
lean_object* x_450; uint8_t x_451; 
x_450 = lean_ctor_get(x_4, 0);
lean_dec(x_450);
x_451 = !lean_is_exclusive(x_5);
if (x_451 == 0)
{
lean_object* x_452; uint8_t x_453; 
x_452 = lean_ctor_get(x_5, 0);
lean_dec(x_452);
x_453 = !lean_is_exclusive(x_6);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; uint8_t x_456; 
x_454 = lean_ctor_get(x_6, 1);
x_455 = lean_ctor_get(x_6, 0);
lean_dec(x_455);
x_456 = !lean_is_exclusive(x_9);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_457 = lean_ctor_get(x_9, 0);
lean_dec(x_457);
x_458 = lean_ctor_get(x_10, 0);
lean_inc(x_458);
x_459 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_458);
x_460 = lean_box(0);
lean_ctor_set(x_6, 1, x_460);
lean_ctor_set(x_5, 0, x_454);
x_461 = lean_nat_sub(x_1, x_2);
x_462 = l___private_Lean_Data_Format_2__pushGroup(x_459, x_6, x_4, x_461);
lean_dec(x_461);
x_4 = x_462;
goto _start;
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_464 = lean_ctor_get(x_9, 1);
lean_inc(x_464);
lean_dec(x_9);
x_465 = lean_ctor_get(x_10, 0);
lean_inc(x_465);
x_466 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_464);
x_468 = lean_box(0);
lean_ctor_set(x_6, 1, x_468);
lean_ctor_set(x_6, 0, x_467);
lean_ctor_set(x_5, 0, x_454);
x_469 = lean_nat_sub(x_1, x_2);
x_470 = l___private_Lean_Data_Format_2__pushGroup(x_466, x_6, x_4, x_469);
lean_dec(x_469);
x_4 = x_470;
goto _start;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_472 = lean_ctor_get(x_6, 1);
lean_inc(x_472);
lean_dec(x_6);
x_473 = lean_ctor_get(x_9, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_474 = x_9;
} else {
 lean_dec_ref(x_9);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_10, 0);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (lean_is_scalar(x_474)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_474;
}
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_473);
x_478 = lean_box(0);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set(x_5, 0, x_472);
x_480 = lean_nat_sub(x_1, x_2);
x_481 = l___private_Lean_Data_Format_2__pushGroup(x_476, x_479, x_4, x_480);
lean_dec(x_480);
x_4 = x_481;
goto _start;
}
}
else
{
uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_483 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_484 = lean_ctor_get(x_6, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_485 = x_6;
} else {
 lean_dec_ref(x_6);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_9, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_487 = x_9;
} else {
 lean_dec_ref(x_9);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_10, 0);
lean_inc(x_488);
x_489 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (lean_is_scalar(x_487)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_487;
}
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_486);
x_491 = lean_box(0);
if (lean_is_scalar(x_485)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_485;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_493, 0, x_484);
lean_ctor_set_uint8(x_493, sizeof(void*)*1, x_448);
lean_ctor_set_uint8(x_493, sizeof(void*)*1 + 1, x_483);
lean_ctor_set(x_4, 0, x_493);
x_494 = lean_nat_sub(x_1, x_2);
x_495 = l___private_Lean_Data_Format_2__pushGroup(x_489, x_492, x_4, x_494);
lean_dec(x_494);
x_4 = x_495;
goto _start;
}
}
else
{
lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_497 = lean_ctor_get(x_4, 1);
lean_inc(x_497);
lean_dec(x_4);
x_498 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_499 = x_5;
} else {
 lean_dec_ref(x_5);
 x_499 = lean_box(0);
}
x_500 = lean_ctor_get(x_6, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_501 = x_6;
} else {
 lean_dec_ref(x_6);
 x_501 = lean_box(0);
}
x_502 = lean_ctor_get(x_9, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_503 = x_9;
} else {
 lean_dec_ref(x_9);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_10, 0);
lean_inc(x_504);
x_505 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (lean_is_scalar(x_503)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_503;
}
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_502);
x_507 = lean_box(0);
if (lean_is_scalar(x_501)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_501;
}
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
if (lean_is_scalar(x_499)) {
 x_509 = lean_alloc_ctor(0, 1, 2);
} else {
 x_509 = x_499;
}
lean_ctor_set(x_509, 0, x_500);
lean_ctor_set_uint8(x_509, sizeof(void*)*1, x_448);
lean_ctor_set_uint8(x_509, sizeof(void*)*1 + 1, x_498);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_497);
x_511 = lean_nat_sub(x_1, x_2);
x_512 = l___private_Lean_Data_Format_2__pushGroup(x_505, x_508, x_510, x_511);
lean_dec(x_511);
x_4 = x_512;
goto _start;
}
}
else
{
uint8_t x_514; 
x_514 = !lean_is_exclusive(x_4);
if (x_514 == 0)
{
lean_object* x_515; uint8_t x_516; 
x_515 = lean_ctor_get(x_4, 0);
lean_dec(x_515);
x_516 = !lean_is_exclusive(x_5);
if (x_516 == 0)
{
lean_object* x_517; uint8_t x_518; 
x_517 = lean_ctor_get(x_5, 0);
lean_dec(x_517);
x_518 = !lean_is_exclusive(x_6);
if (x_518 == 0)
{
lean_object* x_519; uint8_t x_520; 
x_519 = lean_ctor_get(x_6, 0);
lean_dec(x_519);
x_520 = !lean_is_exclusive(x_9);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
x_521 = lean_ctor_get(x_9, 0);
lean_dec(x_521);
x_522 = lean_ctor_get(x_10, 0);
lean_inc(x_522);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_522);
goto _start;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_9, 1);
lean_inc(x_524);
lean_dec(x_9);
x_525 = lean_ctor_get(x_10, 0);
lean_inc(x_525);
lean_dec(x_10);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_524);
lean_ctor_set(x_6, 0, x_526);
goto _start;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_528 = lean_ctor_get(x_6, 1);
lean_inc(x_528);
lean_dec(x_6);
x_529 = lean_ctor_get(x_9, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_530 = x_9;
} else {
 lean_dec_ref(x_9);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_10, 0);
lean_inc(x_531);
lean_dec(x_10);
if (lean_is_scalar(x_530)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_530;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_529);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_528);
lean_ctor_set(x_5, 0, x_533);
goto _start;
}
}
else
{
uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_535 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
lean_dec(x_5);
x_536 = lean_ctor_get(x_6, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_537 = x_6;
} else {
 lean_dec_ref(x_6);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_9, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_539 = x_9;
} else {
 lean_dec_ref(x_9);
 x_539 = lean_box(0);
}
x_540 = lean_ctor_get(x_10, 0);
lean_inc(x_540);
lean_dec(x_10);
if (lean_is_scalar(x_539)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_539;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_538);
if (lean_is_scalar(x_537)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_537;
}
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_536);
x_543 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set_uint8(x_543, sizeof(void*)*1, x_448);
lean_ctor_set_uint8(x_543, sizeof(void*)*1 + 1, x_535);
lean_ctor_set(x_4, 0, x_543);
goto _start;
}
}
else
{
lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_545 = lean_ctor_get(x_4, 1);
lean_inc(x_545);
lean_dec(x_4);
x_546 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_547 = x_5;
} else {
 lean_dec_ref(x_5);
 x_547 = lean_box(0);
}
x_548 = lean_ctor_get(x_6, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_549 = x_6;
} else {
 lean_dec_ref(x_6);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_9, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_551 = x_9;
} else {
 lean_dec_ref(x_9);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_10, 0);
lean_inc(x_552);
lean_dec(x_10);
if (lean_is_scalar(x_551)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_551;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_550);
if (lean_is_scalar(x_549)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_549;
}
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_548);
if (lean_is_scalar(x_547)) {
 x_555 = lean_alloc_ctor(0, 1, 2);
} else {
 x_555 = x_547;
}
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set_uint8(x_555, sizeof(void*)*1, x_448);
lean_ctor_set_uint8(x_555, sizeof(void*)*1 + 1, x_546);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_545);
x_4 = x_556;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Format_be___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Format_be___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Format_be(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Format_be___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Format_be___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Format_be(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Format_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
lean_object* _init_l_Lean_Format_paren___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ULift_HasRepr___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Format_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = l_Lean_Format_paren___closed__3;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_Format_paren___closed__4;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Format_paren___closed__2;
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Format_sbracket___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__2;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_sbracket___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_sbracket___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_sbracket___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_sbracket___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Format_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = l_Lean_Format_sbracket___closed__3;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_Format_sbracket___closed__4;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Format_sbracket___closed__2;
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Format_defIndent() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
uint8_t _init_l_Lean_Format_defUnicode() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_Lean_Format_defWidth() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(120u);
return x_1;
}
}
lean_object* _init_l_Lean_Format_getWidth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("format");
return x_1;
}
}
lean_object* _init_l_Lean_Format_getWidth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_getWidth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("width");
return x_1;
}
}
lean_object* _init_l_Lean_Format_getWidth___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_getWidth___closed__2;
x_2 = l_Lean_Format_getWidth___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_getWidth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Format_getWidth___closed__4;
x_3 = l_Lean_Format_defWidth;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_getWidth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Format_getWidth(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_getIndent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indent");
return x_1;
}
}
lean_object* _init_l_Lean_Format_getIndent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_getWidth___closed__2;
x_2 = l_Lean_Format_getIndent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_getIndent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Format_getIndent___closed__2;
x_3 = l_Lean_Format_defIndent;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_getIndent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Format_getIndent(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_getUnicode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unicode");
return x_1;
}
}
lean_object* _init_l_Lean_Format_getUnicode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_getWidth___closed__2;
x_2 = l_Lean_Format_getUnicode___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Format_getUnicode(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Format_getUnicode___closed__2;
x_3 = l_Lean_Format_defUnicode;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_getUnicode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Format_getUnicode(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_indentOption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defIndent;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_indentOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indentation");
return x_1;
}
}
lean_object* _init_l_Lean_Format_indentOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Format_indentOption___closed__1;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_indentOption___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_indentOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Format_getIndent___closed__2;
x_3 = l_Lean_Format_indentOption___closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Format_unicodeOption___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defUnicode;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_unicodeOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unicode characters");
return x_1;
}
}
lean_object* _init_l_Lean_Format_unicodeOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Format_unicodeOption___closed__1;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_unicodeOption___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_unicodeOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Format_getUnicode___closed__2;
x_3 = l_Lean_Format_unicodeOption___closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Format_widthOption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defWidth;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_widthOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("line width");
return x_1;
}
}
lean_object* _init_l_Lean_Format_widthOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Format_widthOption___closed__1;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_widthOption___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_widthOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Format_getWidth___closed__4;
x_3 = l_Lean_Format_widthOption___closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* lean_format_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = l_Int_zero;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_String_splitAux___main___closed__1;
x_13 = l_Lean_Format_be___main(x_2, x_11, x_12, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Format_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Format_getWidth(x_2);
x_4 = lean_format_pretty(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_pretty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_pretty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_toStringToFormat___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_toStringToFormat___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_toStringToFormat___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_toStringToFormat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_toStringToFormat___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_toStringToFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_toStringToFormat___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_formatHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasOfNat___closed__1;
return x_1;
}
}
lean_object* l_Lean_stringHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
lean_inc(x_3);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = l_Lean_Format_joinSep___main___rarg(x_1, x_5, x_3);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Format_joinSep___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_joinSep___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Format_joinSep___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_joinSep___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Format_prefixJoin___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
lean_inc(x_2);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Format_prefixJoin___main___rarg(x_1, x_2, x_6);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Format_prefixJoin___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_prefixJoin___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Format_prefixJoin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Format_prefixJoin___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_prefixJoin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_prefixJoin___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinSuffix___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
lean_inc(x_3);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = l_Lean_Format_joinSuffix___main___rarg(x_1, x_6, x_3);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Format_joinSuffix___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_joinSuffix___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinSuffix___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Format_joinSuffix___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_joinSuffix___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_List_format___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_List_format___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
lean_object* _init_l_Lean_List_format___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_List_format___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_List_format___rarg___closed__3;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_List_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_List_format___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_4 = l_Lean_List_format___rarg___closed__4;
x_5 = l_Lean_Format_joinSep___main___rarg(x_1, x_2, x_4);
x_6 = l_Lean_Format_sbracket___closed__3;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Format_sbracket___closed__4;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Format_sbracket___closed__2;
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_List_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_List_format___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_listHasFormat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_List_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_listHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_listHasFormat___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_arrayHasFormat___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_List_format___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_arrayHasFormat___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_fmt___at_Lean_arrayHasFormat___spec__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_arrayHasFormat___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_arrayHasFormat___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l_Lean_List_format___rarg(x_1, x_3);
x_5 = l_Lean_arrayHasFormat___rarg___closed__1;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_arrayHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_arrayHasFormat___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_arrayHasFormat___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_arrayHasFormat___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Option_format___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Option_format___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some ");
return x_1;
}
}
lean_object* _init_l_Lean_Option_format___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_format___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Option_format___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_Option_format___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_Option_format___rarg___closed__3;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Option_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_format___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_optionHasFormat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_format___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_optionHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_optionHasFormat___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_prodHasFormat___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lean_List_format___rarg___closed__3;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_1(x_2, x_5);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Format_paren___closed__3;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Format_paren___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Format_paren___closed__2;
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 0;
x_20 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
return x_20;
}
}
lean_object* l_Lean_prodHasFormat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_prodHasFormat___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
if (x_11 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = lean_apply_1(x_1, x_9);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_5 = x_13;
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_3);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_3);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_9);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_5 = x_13;
x_6 = x_19;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinArraySep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(x_1, x_2, x_3, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Format_joinArraySep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Format_joinArraySep___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Format_joinArraySep___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Format_joinArraySep___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_natHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_uint16HasFormat(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Lean_uint16HasFormat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_uint16HasFormat(x_2);
return x_3;
}
}
lean_object* l_Lean_uint32HasFormat(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Lean_uint32HasFormat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_uint32HasFormat(x_2);
return x_3;
}
}
lean_object* l_Lean_uint64HasFormat(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Lean_uint64HasFormat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_uint64HasFormat(x_2);
return x_3;
}
}
lean_object* l_Lean_usizeHasFormat(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Lean_usizeHasFormat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_usizeHasFormat(x_2);
return x_3;
}
}
lean_object* l_Lean_nameHasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.nil");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.line");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.text");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_repr___main___closed__6;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.nest");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_repr___main___closed__9;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.append ");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_repr___main___closed__12;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.group");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_repr___main___closed__15;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.fill");
return x_1;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Format_repr___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_repr___main___closed__18;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Format_repr___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Format_repr___main___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Format_repr___main___closed__4;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_String_quote(x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = l_Lean_Format_repr___main___closed__7;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = l_Lean_Format_paren___closed__3;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Format_paren___closed__4;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Format_paren___closed__2;
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = 0;
x_16 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_String_quote(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Format_repr___main___closed__7;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Format_paren___closed__3;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Format_paren___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Format_paren___closed__2;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = 0;
x_29 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
return x_29;
}
}
case 3:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = l_Int_repr(x_31);
lean_dec(x_31);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Format_repr___main___closed__10;
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_35);
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Format_repr___main(x_32);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Format_paren___closed__3;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Format_paren___closed__4;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Format_paren___closed__2;
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = 0;
x_47 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_1);
x_50 = l_Int_repr(x_48);
lean_dec(x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Format_repr___main___closed__10;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Format_repr___main(x_49);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Format_paren___closed__3;
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Format_paren___closed__4;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Format_paren___closed__2;
x_63 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = 0;
x_65 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
return x_65;
}
}
case 4:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_1);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
x_69 = l_Lean_Format_repr___main(x_67);
x_70 = l_Lean_Format_repr___main___closed__13;
lean_ctor_set(x_1, 1, x_69);
lean_ctor_set(x_1, 0, x_70);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Format_repr___main(x_68);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Format_paren___closed__3;
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_Format_paren___closed__4;
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Format_paren___closed__2;
x_80 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = 0;
x_82 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_83 = lean_ctor_get(x_1, 0);
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_1);
x_85 = l_Lean_Format_repr___main(x_83);
x_86 = l_Lean_Format_repr___main___closed__13;
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Format_repr___main(x_84);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Format_paren___closed__3;
x_93 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Format_paren___closed__4;
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Format_paren___closed__2;
x_97 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = 0;
x_99 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
return x_99;
}
}
default: 
{
uint8_t x_100; 
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_ctor_get(x_1, 0);
x_103 = l_Lean_Format_repr___main(x_102);
x_104 = l_Lean_Format_repr___main___closed__16;
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_Format_paren___closed__3;
x_107 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Format_paren___closed__4;
x_109 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Format_paren___closed__2;
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = 0;
lean_ctor_set(x_1, 0, x_111);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_112);
return x_1;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
lean_dec(x_1);
x_114 = l_Lean_Format_repr___main(x_113);
x_115 = l_Lean_Format_repr___main___closed__16;
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_Format_paren___closed__3;
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Format_paren___closed__4;
x_120 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Format_paren___closed__2;
x_122 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = 0;
x_124 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
return x_124;
}
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_1);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_126 = lean_ctor_get(x_1, 0);
x_127 = l_Lean_Format_repr___main(x_126);
x_128 = l_Lean_Format_repr___main___closed__19;
x_129 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Format_paren___closed__3;
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Format_paren___closed__4;
x_133 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Format_paren___closed__2;
x_135 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = 0;
lean_ctor_set(x_1, 0, x_135);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_136);
return x_1;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
lean_dec(x_1);
x_138 = l_Lean_Format_repr___main(x_137);
x_139 = l_Lean_Format_repr___main___closed__19;
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Format_paren___closed__3;
x_142 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Format_paren___closed__4;
x_144 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_Format_paren___closed__2;
x_146 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = 0;
x_148 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
return x_148;
}
}
}
}
}
}
lean_object* l_Lean_Format_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Format_repr___main(x_1);
return x_2;
}
}
lean_object* l_Lean_formatHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_HasRepr___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HasRepr___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_HasRepr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Format_repr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_HasRepr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_HasRepr___closed__2;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HasRepr___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_formatDataValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_formatDataValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_HasRepr___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_formatDataValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
lean_object* _init_l_Lean_formatDataValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatDataValue___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_formatDataValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_String_quote(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_formatDataValue___closed__1;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_formatDataValue___closed__2;
return x_7;
}
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_System_FilePath_dirName___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_8);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_formatDataValue___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Nat_repr(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Int_repr(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_dataValueHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatDataValue), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_dataValueHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_dataValueHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_formatEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
lean_object* _init_l_Lean_formatEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatEntry___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_formatEntry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_dirName___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_formatEntry___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_formatDataValue(x_3);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* _init_l_Lean_entryHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatEntry), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_entryHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_entryHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_formatEntry(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_formatEntry(x_7);
lean_inc(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(x_4, x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_formatKVMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_formatKVMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_2 = l_Lean_formatKVMap___closed__1;
x_3 = l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(x_1, x_2);
x_4 = l_Lean_Format_sbracket___closed__3;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_Format_sbracket___closed__4;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Format_sbracket___closed__2;
x_9 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
return x_11;
}
}
lean_object* _init_l_Lean_kvMapHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatKVMap), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_kvMapHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_kvMapHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(x_4, x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_String_toFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Format_be___main___closed__1;
x_3 = l_String_splitOn(x_1, x_2);
x_4 = lean_box(1);
x_5 = l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Options(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Format(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Format_Inhabited = _init_l_Lean_Format_Inhabited();
lean_mark_persistent(l_Lean_Format_Inhabited);
l_Lean_Format_join___closed__1 = _init_l_Lean_Format_join___closed__1();
lean_mark_persistent(l_Lean_Format_join___closed__1);
l_Lean_Format_SpaceResult_inhabited___closed__1 = _init_l_Lean_Format_SpaceResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_Format_SpaceResult_inhabited___closed__1);
l_Lean_Format_SpaceResult_inhabited = _init_l_Lean_Format_SpaceResult_inhabited();
lean_mark_persistent(l_Lean_Format_SpaceResult_inhabited);
l_Lean_Format_spaceUptoLine___main___closed__1 = _init_l_Lean_Format_spaceUptoLine___main___closed__1();
lean_mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__1);
l_Lean_Format_spaceUptoLine___main___closed__2 = _init_l_Lean_Format_spaceUptoLine___main___closed__2();
lean_mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__2);
l_Lean_Format_be___main___closed__1 = _init_l_Lean_Format_be___main___closed__1();
lean_mark_persistent(l_Lean_Format_be___main___closed__1);
l_Lean_Format_paren___closed__1 = _init_l_Lean_Format_paren___closed__1();
lean_mark_persistent(l_Lean_Format_paren___closed__1);
l_Lean_Format_paren___closed__2 = _init_l_Lean_Format_paren___closed__2();
lean_mark_persistent(l_Lean_Format_paren___closed__2);
l_Lean_Format_paren___closed__3 = _init_l_Lean_Format_paren___closed__3();
lean_mark_persistent(l_Lean_Format_paren___closed__3);
l_Lean_Format_paren___closed__4 = _init_l_Lean_Format_paren___closed__4();
lean_mark_persistent(l_Lean_Format_paren___closed__4);
l_Lean_Format_sbracket___closed__1 = _init_l_Lean_Format_sbracket___closed__1();
lean_mark_persistent(l_Lean_Format_sbracket___closed__1);
l_Lean_Format_sbracket___closed__2 = _init_l_Lean_Format_sbracket___closed__2();
lean_mark_persistent(l_Lean_Format_sbracket___closed__2);
l_Lean_Format_sbracket___closed__3 = _init_l_Lean_Format_sbracket___closed__3();
lean_mark_persistent(l_Lean_Format_sbracket___closed__3);
l_Lean_Format_sbracket___closed__4 = _init_l_Lean_Format_sbracket___closed__4();
lean_mark_persistent(l_Lean_Format_sbracket___closed__4);
l_Lean_Format_defIndent = _init_l_Lean_Format_defIndent();
lean_mark_persistent(l_Lean_Format_defIndent);
l_Lean_Format_defUnicode = _init_l_Lean_Format_defUnicode();
l_Lean_Format_defWidth = _init_l_Lean_Format_defWidth();
lean_mark_persistent(l_Lean_Format_defWidth);
l_Lean_Format_getWidth___closed__1 = _init_l_Lean_Format_getWidth___closed__1();
lean_mark_persistent(l_Lean_Format_getWidth___closed__1);
l_Lean_Format_getWidth___closed__2 = _init_l_Lean_Format_getWidth___closed__2();
lean_mark_persistent(l_Lean_Format_getWidth___closed__2);
l_Lean_Format_getWidth___closed__3 = _init_l_Lean_Format_getWidth___closed__3();
lean_mark_persistent(l_Lean_Format_getWidth___closed__3);
l_Lean_Format_getWidth___closed__4 = _init_l_Lean_Format_getWidth___closed__4();
lean_mark_persistent(l_Lean_Format_getWidth___closed__4);
l_Lean_Format_getIndent___closed__1 = _init_l_Lean_Format_getIndent___closed__1();
lean_mark_persistent(l_Lean_Format_getIndent___closed__1);
l_Lean_Format_getIndent___closed__2 = _init_l_Lean_Format_getIndent___closed__2();
lean_mark_persistent(l_Lean_Format_getIndent___closed__2);
l_Lean_Format_getUnicode___closed__1 = _init_l_Lean_Format_getUnicode___closed__1();
lean_mark_persistent(l_Lean_Format_getUnicode___closed__1);
l_Lean_Format_getUnicode___closed__2 = _init_l_Lean_Format_getUnicode___closed__2();
lean_mark_persistent(l_Lean_Format_getUnicode___closed__2);
l_Lean_Format_indentOption___closed__1 = _init_l_Lean_Format_indentOption___closed__1();
lean_mark_persistent(l_Lean_Format_indentOption___closed__1);
l_Lean_Format_indentOption___closed__2 = _init_l_Lean_Format_indentOption___closed__2();
lean_mark_persistent(l_Lean_Format_indentOption___closed__2);
l_Lean_Format_indentOption___closed__3 = _init_l_Lean_Format_indentOption___closed__3();
lean_mark_persistent(l_Lean_Format_indentOption___closed__3);
res = l_Lean_Format_indentOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Format_unicodeOption___closed__1 = _init_l_Lean_Format_unicodeOption___closed__1();
lean_mark_persistent(l_Lean_Format_unicodeOption___closed__1);
l_Lean_Format_unicodeOption___closed__2 = _init_l_Lean_Format_unicodeOption___closed__2();
lean_mark_persistent(l_Lean_Format_unicodeOption___closed__2);
l_Lean_Format_unicodeOption___closed__3 = _init_l_Lean_Format_unicodeOption___closed__3();
lean_mark_persistent(l_Lean_Format_unicodeOption___closed__3);
res = l_Lean_Format_unicodeOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Format_widthOption___closed__1 = _init_l_Lean_Format_widthOption___closed__1();
lean_mark_persistent(l_Lean_Format_widthOption___closed__1);
l_Lean_Format_widthOption___closed__2 = _init_l_Lean_Format_widthOption___closed__2();
lean_mark_persistent(l_Lean_Format_widthOption___closed__2);
l_Lean_Format_widthOption___closed__3 = _init_l_Lean_Format_widthOption___closed__3();
lean_mark_persistent(l_Lean_Format_widthOption___closed__3);
res = l_Lean_Format_widthOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_toStringToFormat___rarg___closed__1 = _init_l_Lean_toStringToFormat___rarg___closed__1();
lean_mark_persistent(l_Lean_toStringToFormat___rarg___closed__1);
l_Lean_formatHasFormat = _init_l_Lean_formatHasFormat();
lean_mark_persistent(l_Lean_formatHasFormat);
l_Lean_List_format___rarg___closed__1 = _init_l_Lean_List_format___rarg___closed__1();
lean_mark_persistent(l_Lean_List_format___rarg___closed__1);
l_Lean_List_format___rarg___closed__2 = _init_l_Lean_List_format___rarg___closed__2();
lean_mark_persistent(l_Lean_List_format___rarg___closed__2);
l_Lean_List_format___rarg___closed__3 = _init_l_Lean_List_format___rarg___closed__3();
lean_mark_persistent(l_Lean_List_format___rarg___closed__3);
l_Lean_List_format___rarg___closed__4 = _init_l_Lean_List_format___rarg___closed__4();
lean_mark_persistent(l_Lean_List_format___rarg___closed__4);
l_Lean_arrayHasFormat___rarg___closed__1 = _init_l_Lean_arrayHasFormat___rarg___closed__1();
lean_mark_persistent(l_Lean_arrayHasFormat___rarg___closed__1);
l_Lean_Option_format___rarg___closed__1 = _init_l_Lean_Option_format___rarg___closed__1();
lean_mark_persistent(l_Lean_Option_format___rarg___closed__1);
l_Lean_Option_format___rarg___closed__2 = _init_l_Lean_Option_format___rarg___closed__2();
lean_mark_persistent(l_Lean_Option_format___rarg___closed__2);
l_Lean_Option_format___rarg___closed__3 = _init_l_Lean_Option_format___rarg___closed__3();
lean_mark_persistent(l_Lean_Option_format___rarg___closed__3);
l_Lean_Format_repr___main___closed__1 = _init_l_Lean_Format_repr___main___closed__1();
lean_mark_persistent(l_Lean_Format_repr___main___closed__1);
l_Lean_Format_repr___main___closed__2 = _init_l_Lean_Format_repr___main___closed__2();
lean_mark_persistent(l_Lean_Format_repr___main___closed__2);
l_Lean_Format_repr___main___closed__3 = _init_l_Lean_Format_repr___main___closed__3();
lean_mark_persistent(l_Lean_Format_repr___main___closed__3);
l_Lean_Format_repr___main___closed__4 = _init_l_Lean_Format_repr___main___closed__4();
lean_mark_persistent(l_Lean_Format_repr___main___closed__4);
l_Lean_Format_repr___main___closed__5 = _init_l_Lean_Format_repr___main___closed__5();
lean_mark_persistent(l_Lean_Format_repr___main___closed__5);
l_Lean_Format_repr___main___closed__6 = _init_l_Lean_Format_repr___main___closed__6();
lean_mark_persistent(l_Lean_Format_repr___main___closed__6);
l_Lean_Format_repr___main___closed__7 = _init_l_Lean_Format_repr___main___closed__7();
lean_mark_persistent(l_Lean_Format_repr___main___closed__7);
l_Lean_Format_repr___main___closed__8 = _init_l_Lean_Format_repr___main___closed__8();
lean_mark_persistent(l_Lean_Format_repr___main___closed__8);
l_Lean_Format_repr___main___closed__9 = _init_l_Lean_Format_repr___main___closed__9();
lean_mark_persistent(l_Lean_Format_repr___main___closed__9);
l_Lean_Format_repr___main___closed__10 = _init_l_Lean_Format_repr___main___closed__10();
lean_mark_persistent(l_Lean_Format_repr___main___closed__10);
l_Lean_Format_repr___main___closed__11 = _init_l_Lean_Format_repr___main___closed__11();
lean_mark_persistent(l_Lean_Format_repr___main___closed__11);
l_Lean_Format_repr___main___closed__12 = _init_l_Lean_Format_repr___main___closed__12();
lean_mark_persistent(l_Lean_Format_repr___main___closed__12);
l_Lean_Format_repr___main___closed__13 = _init_l_Lean_Format_repr___main___closed__13();
lean_mark_persistent(l_Lean_Format_repr___main___closed__13);
l_Lean_Format_repr___main___closed__14 = _init_l_Lean_Format_repr___main___closed__14();
lean_mark_persistent(l_Lean_Format_repr___main___closed__14);
l_Lean_Format_repr___main___closed__15 = _init_l_Lean_Format_repr___main___closed__15();
lean_mark_persistent(l_Lean_Format_repr___main___closed__15);
l_Lean_Format_repr___main___closed__16 = _init_l_Lean_Format_repr___main___closed__16();
lean_mark_persistent(l_Lean_Format_repr___main___closed__16);
l_Lean_Format_repr___main___closed__17 = _init_l_Lean_Format_repr___main___closed__17();
lean_mark_persistent(l_Lean_Format_repr___main___closed__17);
l_Lean_Format_repr___main___closed__18 = _init_l_Lean_Format_repr___main___closed__18();
lean_mark_persistent(l_Lean_Format_repr___main___closed__18);
l_Lean_Format_repr___main___closed__19 = _init_l_Lean_Format_repr___main___closed__19();
lean_mark_persistent(l_Lean_Format_repr___main___closed__19);
l_Lean_HasRepr___closed__1 = _init_l_Lean_HasRepr___closed__1();
lean_mark_persistent(l_Lean_HasRepr___closed__1);
l_Lean_HasRepr___closed__2 = _init_l_Lean_HasRepr___closed__2();
lean_mark_persistent(l_Lean_HasRepr___closed__2);
l_Lean_HasRepr___closed__3 = _init_l_Lean_HasRepr___closed__3();
lean_mark_persistent(l_Lean_HasRepr___closed__3);
l_Lean_HasRepr = _init_l_Lean_HasRepr();
lean_mark_persistent(l_Lean_HasRepr);
l_Lean_formatDataValue___closed__1 = _init_l_Lean_formatDataValue___closed__1();
lean_mark_persistent(l_Lean_formatDataValue___closed__1);
l_Lean_formatDataValue___closed__2 = _init_l_Lean_formatDataValue___closed__2();
lean_mark_persistent(l_Lean_formatDataValue___closed__2);
l_Lean_formatDataValue___closed__3 = _init_l_Lean_formatDataValue___closed__3();
lean_mark_persistent(l_Lean_formatDataValue___closed__3);
l_Lean_formatDataValue___closed__4 = _init_l_Lean_formatDataValue___closed__4();
lean_mark_persistent(l_Lean_formatDataValue___closed__4);
l_Lean_dataValueHasFormat___closed__1 = _init_l_Lean_dataValueHasFormat___closed__1();
lean_mark_persistent(l_Lean_dataValueHasFormat___closed__1);
l_Lean_dataValueHasFormat = _init_l_Lean_dataValueHasFormat();
lean_mark_persistent(l_Lean_dataValueHasFormat);
l_Lean_formatEntry___closed__1 = _init_l_Lean_formatEntry___closed__1();
lean_mark_persistent(l_Lean_formatEntry___closed__1);
l_Lean_formatEntry___closed__2 = _init_l_Lean_formatEntry___closed__2();
lean_mark_persistent(l_Lean_formatEntry___closed__2);
l_Lean_entryHasFormat___closed__1 = _init_l_Lean_entryHasFormat___closed__1();
lean_mark_persistent(l_Lean_entryHasFormat___closed__1);
l_Lean_entryHasFormat = _init_l_Lean_entryHasFormat();
lean_mark_persistent(l_Lean_entryHasFormat);
l_Lean_formatKVMap___closed__1 = _init_l_Lean_formatKVMap___closed__1();
lean_mark_persistent(l_Lean_formatKVMap___closed__1);
l_Lean_kvMapHasFormat___closed__1 = _init_l_Lean_kvMapHasFormat___closed__1();
lean_mark_persistent(l_Lean_kvMapHasFormat___closed__1);
l_Lean_kvMapHasFormat = _init_l_Lean_kvMapHasFormat();
lean_mark_persistent(l_Lean_kvMapHasFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
