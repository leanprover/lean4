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
lean_object* l___private_Lean_Data_Format_11__be(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_repr___main(lean_object*);
lean_object* l_String_toFormat(lean_object*);
lean_object* l_String_posOfAux___main(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_arrayHasFormat___spec__1___rarg(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l_Lean_kvMapHasFormat;
lean_object* l_Lean_Format_repr___main___closed__11;
uint8_t l_Lean_Format_getUnicode(lean_object*);
lean_object* l___private_Lean_Data_Format_11__be___main___closed__3;
lean_object* l_Lean_Format_getWidth___closed__3;
lean_object* l_Lean_Format_join(lean_object*);
lean_object* l_Lean_List_format___rarg___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_usizeHasFormat___boxed(lean_object*);
lean_object* l___private_Lean_Data_Format_2__merge(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Format_prettyAux___closed__1;
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Format_repr(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l_Lean_Format_repr___main___closed__12;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_arrayHasFormat(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_Lean_listHasFormat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_formatEntry(lean_object*);
lean_object* l_Lean_Format_prefixJoin___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_format___rarg(lean_object*, lean_object*);
lean_object* l_Lean_usizeHasFormat(size_t);
lean_object* l___private_Lean_Data_Format_11__be___main___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l___private_Lean_Data_Format_11__be___main___closed__1;
lean_object* l_Lean_Format_widthOption(lean_object*);
extern lean_object* l_Int_zero;
lean_object* l_Lean_List_format___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinArraySep___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_10__pushNewline___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_uint16HasFormat___boxed(lean_object*);
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
lean_object* l___private_Lean_Data_Format_11__be___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_2__merge___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Option_format___rarg___closed__2;
lean_object* l_Lean_Format_joinSep___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatDataValue___closed__3;
lean_object* l_Lean_entryHasFormat___closed__1;
lean_object* l_Lean_List_format(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__2;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Format_fill(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__4;
lean_object* l_Lean_Format_repr___main___closed__1;
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_toStringToFormat___rarg(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_String_toFormat___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg___closed__1;
lean_object* l_Lean_formatEntry___closed__2;
lean_object* l___private_Lean_Data_Format_9__pushOutput___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Format_join___boxed(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__8;
lean_object* l_Lean_Format_join___closed__1;
lean_object* lean_format_group(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Format_repr___main___closed__19;
lean_object* l___private_Lean_Data_Format_11__be___main___closed__2;
lean_object* l_Lean_optionHasFormat(lean_object*);
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2;
lean_object* l_Lean_Format_joinArraySep___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_repr___main___closed__9;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_kvMapHasFormat___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_formatDataValue___closed__4;
lean_object* l_Lean_formatKVMap(lean_object*);
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_prodHasFormat(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr___lambda__1(lean_object*);
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_8__pushGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Id_Monad;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_11__be___main(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Format_unicodeOption___closed__1;
lean_object* l_Lean_Format_joinSep(lean_object*);
lean_object* l_Lean_arrayHasFormat___rarg(lean_object*, lean_object*);
lean_object* l_String_offsetOfPosAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_paren___closed__1;
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Lean_fmt(lean_object*);
lean_object* l___private_Lean_Data_Format_10__pushNewline(lean_object*, lean_object*);
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
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_Format_Coe(lean_object*);
lean_object* l_Lean_optionHasFormat___rarg(lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_Format_getIndent(lean_object*);
uint8_t l_Lean_Format_FlattenBehavior_hasBeq(uint8_t, uint8_t);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasRepr;
lean_object* l_Lean_natHasFormat(lean_object*);
lean_object* l_Lean_Format_paren___closed__4;
lean_object* l_Lean_Format_getWidth___closed__4;
lean_object* l_Lean_Format_SpaceResult_inhabited___closed__1;
lean_object* l_Lean_Format_joinSuffix___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_prodHasFormat___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_formatDataValue(lean_object*);
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine(lean_object*, uint8_t, lean_object*);
extern lean_object* l_PUnit_Inhabited;
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
lean_object* l___private_Lean_Data_Format_8__pushGroup(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_listHasFormat___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Format_joinArraySep___spec__1(lean_object*);
lean_object* l_Lean_Format_sbracket(lean_object*);
lean_object* l_Lean_Format_unicodeOption___closed__2;
lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_Format_getIndent___closed__2;
lean_object* l___private_Lean_Data_Format_9__pushOutput(lean_object*, lean_object*);
lean_object* l_Lean_stringHasFormat(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(lean_object*, lean_object*);
lean_object* l_Lean_Format_getWidth(lean_object*);
lean_object* l_Lean_Format_paren(lean_object*);
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Format_unicodeOption(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Format_Inhabited() {
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
static lean_object* _init_l_Lean_Format_join___closed__1() {
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
static lean_object* _init_l_Lean_Format_SpaceResult_inhabited___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Format_SpaceResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Format_SpaceResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_Format_2__merge(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_13);
return x_16;
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
lean_object* l___private_Lean_Data_Format_2__merge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_2__merge(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_5 = l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2;
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
if (x_2 == 0)
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = 0;
x_20 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_19);
return x_20;
}
}
case 3:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 1);
x_1 = x_21;
goto _start;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_23, x_2, x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_3, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_25);
x_29 = lean_nat_sub(x_3, x_26);
x_30 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_24, x_2, x_29);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_nat_add(x_26, x_32);
lean_dec(x_32);
lean_dec(x_26);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
x_35 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_nat_add(x_26, x_36);
lean_dec(x_36);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 1, x_35);
return x_38;
}
}
else
{
lean_dec(x_26);
return x_25;
}
}
else
{
lean_dec(x_26);
return x_25;
}
}
default: 
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = 1;
x_1 = x_39;
x_2 = x_40;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Data_Format_3__spaceUptoLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_Format_3__spaceUptoLine(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(lean_object* x_1, lean_object* x_2) {
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
x_16 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_15, x_10, x_2);
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
x_21 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_5, x_20);
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
uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_26 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_nat_add(x_17, x_27);
lean_dec(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_26);
return x_29;
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_32, x_10, x_2);
lean_dec(x_32);
lean_ctor_set(x_4, 0, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_2, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
x_38 = lean_nat_sub(x_2, x_35);
x_39 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_34, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
x_41 = lean_ctor_get_uint8(x_39, sizeof(void*)*1 + 1);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = lean_nat_add(x_35, x_42);
lean_dec(x_42);
lean_dec(x_35);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 1, 2);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_41);
return x_45;
}
else
{
lean_dec(x_35);
lean_dec(x_34);
return x_33;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
return x_33;
}
}
}
else
{
uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
lean_dec(x_4);
x_48 = lean_ctor_get(x_5, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_50 = x_5;
} else {
 lean_dec_ref(x_5);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_Data_Format_3__spaceUptoLine___main(x_51, x_46, x_2);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 1, x_47);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = lean_nat_dec_lt(x_2, x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
x_58 = lean_nat_sub(x_2, x_55);
x_59 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_54, x_58);
lean_dec(x_58);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
x_61 = lean_ctor_get_uint8(x_59, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = lean_nat_add(x_55, x_62);
lean_dec(x_62);
lean_dec(x_55);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 2);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 1, x_61);
return x_65;
}
else
{
lean_dec(x_55);
lean_dec(x_54);
return x_52;
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
return x_52;
}
}
}
}
}
}
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_6__spaceUptoLine_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Format_6__spaceUptoLine_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_8__pushGroup(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
if (x_1 == 0)
{
uint8_t x_48; 
x_48 = 1;
x_9 = x_48;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = 0;
x_9 = x_49;
goto block_47;
}
block_47:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 1, x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_8, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_nat_sub(x_8, x_13);
lean_inc(x_3);
x_18 = l___private_Lean_Data_Format_6__spaceUptoLine_x27___main(x_3, x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_nat_add(x_13, x_19);
lean_dec(x_19);
lean_dec(x_13);
x_21 = lean_nat_dec_le(x_20, x_8);
lean_dec(x_8);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 1, x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_dec(x_8);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_nat_dec_le(x_13, x_8);
lean_dec(x_8);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1 + 1, x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_8);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 1, x_1);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_nat_dec_le(x_13, x_8);
lean_dec(x_8);
lean_dec(x_13);
x_40 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 1, x_1);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_8);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_1);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
}
}
}
}
lean_object* l___private_Lean_Data_Format_8__pushGroup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_Format_8__pushGroup(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Data_Format_9__pushOutput(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_string_append(x_3, x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_string_length(x_1);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Data_Format_9__pushOutput___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Format_9__pushOutput(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Format_10__pushNewline___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
lean_object* l___private_Lean_Data_Format_10__pushNewline(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = 32;
x_5 = l___private_Lean_Data_Format_10__pushNewline___closed__1;
lean_inc(x_1);
x_6 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_4, x_1, x_5);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Data_Format_11__be___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Format_11__be___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Iterator_HasRepr___closed__2;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Format_11__be___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Format_11__be___main___closed__1;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Format_11__be___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_12);
x_2 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_25 = x_7;
} else {
 lean_dec_ref(x_7);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
x_2 = x_27;
goto _start;
}
}
case 1:
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_32 = lean_ctor_get(x_6, 0);
lean_dec(x_32);
if (x_31 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_7, 1);
x_36 = lean_ctor_get(x_7, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_dec(x_10);
x_38 = l_Int_toNat(x_37);
lean_dec(x_37);
x_39 = l___private_Lean_Data_Format_10__pushNewline(x_38, x_3);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_6, 0, x_35);
lean_ctor_set(x_7, 1, x_33);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_40;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = l_Int_toNat(x_43);
lean_dec(x_43);
x_45 = l___private_Lean_Data_Format_10__pushNewline(x_44, x_3);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_ctor_set(x_6, 0, x_42);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_33);
x_2 = x_47;
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_7, 1);
x_52 = lean_ctor_get(x_7, 0);
lean_dec(x_52);
x_53 = l_String_Iterator_HasRepr___closed__2;
x_54 = l___private_Lean_Data_Format_9__pushOutput(x_53, x_3);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set(x_6, 0, x_51);
lean_ctor_set(x_7, 1, x_49);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_55;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_dec(x_7);
x_58 = l_String_Iterator_HasRepr___closed__2;
x_59 = l___private_Lean_Data_Format_9__pushOutput(x_58, x_3);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_ctor_set(x_6, 0, x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_49);
x_2 = x_61;
x_3 = x_60;
goto _start;
}
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
lean_dec(x_2);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_66 = x_7;
} else {
 lean_dec_ref(x_7);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_dec(x_10);
x_68 = l_Int_toNat(x_67);
lean_dec(x_67);
x_69 = l___private_Lean_Data_Format_10__pushNewline(x_68, x_3);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_63);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 1, x_29);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_2 = x_72;
x_3 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_10);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_76 = x_7;
} else {
 lean_dec_ref(x_7);
 x_76 = lean_box(0);
}
x_77 = l_String_Iterator_HasRepr___closed__2;
x_78 = l___private_Lean_Data_Format_9__pushOutput(x_77, x_3);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_63);
lean_ctor_set_uint8(x_80, sizeof(void*)*1 + 1, x_29);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
x_2 = x_81;
x_3 = x_79;
goto _start;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_85 = lean_ctor_get(x_7, 1);
lean_inc(x_85);
lean_dec(x_7);
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_dec(x_10);
x_87 = l_Int_toNat(x_86);
lean_dec(x_86);
if (x_84 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = l___private_Lean_Data_Format_10__pushNewline(x_87, x_3);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l___private_Lean_Data_Format_8__pushGroup(x_29, x_85, x_83, x_1, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_2 = x_91;
x_3 = x_92;
goto _start;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_94 = l___private_Lean_Data_Format_11__be___main___closed__2;
x_95 = lean_nat_sub(x_1, x_94);
lean_inc(x_83);
lean_inc(x_85);
x_96 = l___private_Lean_Data_Format_8__pushGroup(x_29, x_85, x_83, x_95, x_3);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_97);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l___private_Lean_Data_Format_10__pushNewline(x_87, x_100);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l___private_Lean_Data_Format_8__pushGroup(x_29, x_85, x_83, x_1, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_2 = x_104;
x_3 = x_105;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_83);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_dec(x_96);
x_108 = l_String_Iterator_HasRepr___closed__2;
x_109 = l___private_Lean_Data_Format_9__pushOutput(x_108, x_107);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_2 = x_97;
x_3 = x_110;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_6);
if (x_113 == 0)
{
uint8_t x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_115 = lean_ctor_get(x_6, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_7);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_7, 1);
x_118 = lean_ctor_get(x_7, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_10);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_10, 1);
x_121 = lean_ctor_get(x_10, 0);
lean_dec(x_121);
x_122 = !lean_is_exclusive(x_11);
if (x_122 == 0)
{
lean_object* x_123; uint32_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_11, 0);
x_124 = 10;
x_125 = lean_string_utf8_byte_size(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_String_posOfAux___main(x_123, x_124, x_125, x_126);
x_128 = lean_nat_dec_eq(x_127, x_125);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_6);
x_129 = lean_string_utf8_extract(x_123, x_126, x_127);
x_130 = l___private_Lean_Data_Format_9__pushOutput(x_129, x_3);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Int_toNat(x_120);
x_133 = l___private_Lean_Data_Format_10__pushNewline(x_132, x_131);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_string_utf8_next(x_123, x_127);
lean_dec(x_127);
x_136 = lean_string_utf8_extract(x_123, x_135, x_125);
lean_dec(x_125);
lean_dec(x_135);
lean_dec(x_123);
lean_ctor_set(x_11, 0, x_136);
x_137 = l___private_Lean_Data_Format_8__pushGroup(x_114, x_7, x_112, x_1, x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_2 = x_138;
x_3 = x_139;
goto _start;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_127);
lean_dec(x_125);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_120);
x_141 = l___private_Lean_Data_Format_9__pushOutput(x_123, x_3);
lean_dec(x_123);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_ctor_set(x_6, 0, x_117);
lean_ctor_set(x_7, 1, x_112);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_142;
goto _start;
}
}
else
{
lean_object* x_144; uint32_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_11, 0);
lean_inc(x_144);
lean_dec(x_11);
x_145 = 10;
x_146 = lean_string_utf8_byte_size(x_144);
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_String_posOfAux___main(x_144, x_145, x_146, x_147);
x_149 = lean_nat_dec_eq(x_148, x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_free_object(x_6);
x_150 = lean_string_utf8_extract(x_144, x_147, x_148);
x_151 = l___private_Lean_Data_Format_9__pushOutput(x_150, x_3);
lean_dec(x_150);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Int_toNat(x_120);
x_154 = l___private_Lean_Data_Format_10__pushNewline(x_153, x_152);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_string_utf8_next(x_144, x_148);
lean_dec(x_148);
x_157 = lean_string_utf8_extract(x_144, x_156, x_146);
lean_dec(x_146);
lean_dec(x_156);
lean_dec(x_144);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_10, 0, x_158);
x_159 = l___private_Lean_Data_Format_8__pushGroup(x_114, x_7, x_112, x_1, x_155);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_2 = x_160;
x_3 = x_161;
goto _start;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_148);
lean_dec(x_146);
lean_free_object(x_10);
lean_dec(x_120);
x_163 = l___private_Lean_Data_Format_9__pushOutput(x_144, x_3);
lean_dec(x_144);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_ctor_set(x_6, 0, x_117);
lean_ctor_set(x_7, 1, x_112);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_164;
goto _start;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint32_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_166 = lean_ctor_get(x_10, 1);
lean_inc(x_166);
lean_dec(x_10);
x_167 = lean_ctor_get(x_11, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_168 = x_11;
} else {
 lean_dec_ref(x_11);
 x_168 = lean_box(0);
}
x_169 = 10;
x_170 = lean_string_utf8_byte_size(x_167);
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_String_posOfAux___main(x_167, x_169, x_170, x_171);
x_173 = lean_nat_dec_eq(x_172, x_170);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_6);
x_174 = lean_string_utf8_extract(x_167, x_171, x_172);
x_175 = l___private_Lean_Data_Format_9__pushOutput(x_174, x_3);
lean_dec(x_174);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Int_toNat(x_166);
x_178 = l___private_Lean_Data_Format_10__pushNewline(x_177, x_176);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_string_utf8_next(x_167, x_172);
lean_dec(x_172);
x_181 = lean_string_utf8_extract(x_167, x_180, x_170);
lean_dec(x_170);
lean_dec(x_180);
lean_dec(x_167);
if (lean_is_scalar(x_168)) {
 x_182 = lean_alloc_ctor(2, 1, 0);
} else {
 x_182 = x_168;
}
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_166);
lean_ctor_set(x_7, 0, x_183);
x_184 = l___private_Lean_Data_Format_8__pushGroup(x_114, x_7, x_112, x_1, x_179);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_2 = x_185;
x_3 = x_186;
goto _start;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_166);
x_188 = l___private_Lean_Data_Format_9__pushOutput(x_167, x_3);
lean_dec(x_167);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
lean_ctor_set(x_6, 0, x_117);
lean_ctor_set(x_7, 1, x_112);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_189;
goto _start;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint32_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_191 = lean_ctor_get(x_7, 1);
lean_inc(x_191);
lean_dec(x_7);
x_192 = lean_ctor_get(x_10, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_193 = x_10;
} else {
 lean_dec_ref(x_10);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_11, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_195 = x_11;
} else {
 lean_dec_ref(x_11);
 x_195 = lean_box(0);
}
x_196 = 10;
x_197 = lean_string_utf8_byte_size(x_194);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_String_posOfAux___main(x_194, x_196, x_197, x_198);
x_200 = lean_nat_dec_eq(x_199, x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_free_object(x_6);
x_201 = lean_string_utf8_extract(x_194, x_198, x_199);
x_202 = l___private_Lean_Data_Format_9__pushOutput(x_201, x_3);
lean_dec(x_201);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Int_toNat(x_192);
x_205 = l___private_Lean_Data_Format_10__pushNewline(x_204, x_203);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_string_utf8_next(x_194, x_199);
lean_dec(x_199);
x_208 = lean_string_utf8_extract(x_194, x_207, x_197);
lean_dec(x_197);
lean_dec(x_207);
lean_dec(x_194);
if (lean_is_scalar(x_195)) {
 x_209 = lean_alloc_ctor(2, 1, 0);
} else {
 x_209 = x_195;
}
lean_ctor_set(x_209, 0, x_208);
if (lean_is_scalar(x_193)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_193;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_192);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_191);
x_212 = l___private_Lean_Data_Format_8__pushGroup(x_114, x_211, x_112, x_1, x_206);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_2 = x_213;
x_3 = x_214;
goto _start;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_192);
x_216 = l___private_Lean_Data_Format_9__pushOutput(x_194, x_3);
lean_dec(x_194);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
lean_ctor_set(x_6, 0, x_191);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_6);
lean_ctor_set(x_218, 1, x_112);
x_2 = x_218;
x_3 = x_217;
goto _start;
}
}
}
else
{
uint8_t x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint32_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_220 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_221 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_222 = lean_ctor_get(x_7, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_223 = x_7;
} else {
 lean_dec_ref(x_7);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_10, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_225 = x_10;
} else {
 lean_dec_ref(x_10);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_11, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_227 = x_11;
} else {
 lean_dec_ref(x_11);
 x_227 = lean_box(0);
}
x_228 = 10;
x_229 = lean_string_utf8_byte_size(x_226);
x_230 = lean_unsigned_to_nat(0u);
x_231 = l_String_posOfAux___main(x_226, x_228, x_229, x_230);
x_232 = lean_nat_dec_eq(x_231, x_229);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_233 = lean_string_utf8_extract(x_226, x_230, x_231);
x_234 = l___private_Lean_Data_Format_9__pushOutput(x_233, x_3);
lean_dec(x_233);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_236 = l_Int_toNat(x_224);
x_237 = l___private_Lean_Data_Format_10__pushNewline(x_236, x_235);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_string_utf8_next(x_226, x_231);
lean_dec(x_231);
x_240 = lean_string_utf8_extract(x_226, x_239, x_229);
lean_dec(x_229);
lean_dec(x_239);
lean_dec(x_226);
if (lean_is_scalar(x_227)) {
 x_241 = lean_alloc_ctor(2, 1, 0);
} else {
 x_241 = x_227;
}
lean_ctor_set(x_241, 0, x_240);
if (lean_is_scalar(x_225)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_225;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_224);
if (lean_is_scalar(x_223)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_223;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_222);
x_244 = l___private_Lean_Data_Format_8__pushGroup(x_221, x_243, x_112, x_1, x_238);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_2 = x_245;
x_3 = x_246;
goto _start;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_224);
x_248 = l___private_Lean_Data_Format_9__pushOutput(x_226, x_3);
lean_dec(x_226);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_250, 0, x_222);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_220);
lean_ctor_set_uint8(x_250, sizeof(void*)*1 + 1, x_221);
if (lean_is_scalar(x_223)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_223;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_112);
x_2 = x_251;
x_3 = x_249;
goto _start;
}
}
}
case 3:
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_2);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_2, 0);
lean_dec(x_254);
x_255 = !lean_is_exclusive(x_6);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_6, 0);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_7);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_7, 0);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_10);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_ctor_get(x_10, 1);
x_261 = lean_ctor_get(x_10, 0);
lean_dec(x_261);
x_262 = lean_ctor_get(x_11, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_11, 1);
lean_inc(x_263);
lean_dec(x_11);
x_264 = lean_int_add(x_260, x_262);
lean_dec(x_262);
lean_dec(x_260);
lean_ctor_set(x_10, 1, x_264);
lean_ctor_set(x_10, 0, x_263);
goto _start;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_10, 1);
lean_inc(x_266);
lean_dec(x_10);
x_267 = lean_ctor_get(x_11, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_11, 1);
lean_inc(x_268);
lean_dec(x_11);
x_269 = lean_int_add(x_266, x_267);
lean_dec(x_267);
lean_dec(x_266);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_7, 0, x_270);
goto _start;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_272 = lean_ctor_get(x_7, 1);
lean_inc(x_272);
lean_dec(x_7);
x_273 = lean_ctor_get(x_10, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_274 = x_10;
} else {
 lean_dec_ref(x_10);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_11, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_11, 1);
lean_inc(x_276);
lean_dec(x_11);
x_277 = lean_int_add(x_273, x_275);
lean_dec(x_275);
lean_dec(x_273);
if (lean_is_scalar(x_274)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_274;
}
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_272);
lean_ctor_set(x_6, 0, x_279);
goto _start;
}
}
else
{
uint8_t x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_281 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_282 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_283 = lean_ctor_get(x_7, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_284 = x_7;
} else {
 lean_dec_ref(x_7);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_10, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_286 = x_10;
} else {
 lean_dec_ref(x_10);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_11, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_11, 1);
lean_inc(x_288);
lean_dec(x_11);
x_289 = lean_int_add(x_285, x_287);
lean_dec(x_287);
lean_dec(x_285);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_286;
}
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_283);
x_292 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_281);
lean_ctor_set_uint8(x_292, sizeof(void*)*1 + 1, x_282);
lean_ctor_set(x_2, 0, x_292);
goto _start;
}
}
else
{
lean_object* x_294; uint8_t x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_294 = lean_ctor_get(x_2, 1);
lean_inc(x_294);
lean_dec(x_2);
x_295 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_296 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_297 = x_6;
} else {
 lean_dec_ref(x_6);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_7, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_299 = x_7;
} else {
 lean_dec_ref(x_7);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_10, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_301 = x_10;
} else {
 lean_dec_ref(x_10);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_11, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_11, 1);
lean_inc(x_303);
lean_dec(x_11);
x_304 = lean_int_add(x_300, x_302);
lean_dec(x_302);
lean_dec(x_300);
if (lean_is_scalar(x_301)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_301;
}
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
if (lean_is_scalar(x_299)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_299;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_307 = lean_alloc_ctor(0, 1, 2);
} else {
 x_307 = x_297;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_295);
lean_ctor_set_uint8(x_307, sizeof(void*)*1 + 1, x_296);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_294);
x_2 = x_308;
goto _start;
}
}
case 4:
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_2);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_2, 1);
x_312 = lean_ctor_get(x_2, 0);
lean_dec(x_312);
x_313 = !lean_is_exclusive(x_6);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_6, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_7);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_7, 0);
lean_dec(x_316);
x_317 = !lean_is_exclusive(x_10);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_318 = lean_ctor_get(x_10, 1);
x_319 = lean_ctor_get(x_10, 0);
lean_dec(x_319);
x_320 = lean_ctor_get(x_11, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_11, 1);
lean_inc(x_321);
lean_dec(x_11);
lean_inc(x_318);
lean_ctor_set(x_10, 0, x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_7, 0, x_322);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set(x_6, 0, x_2);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_6);
lean_ctor_set(x_323, 1, x_311);
x_2 = x_323;
goto _start;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_325 = lean_ctor_get(x_10, 1);
lean_inc(x_325);
lean_dec(x_10);
x_326 = lean_ctor_get(x_11, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_11, 1);
lean_inc(x_327);
lean_dec(x_11);
lean_inc(x_325);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_325);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_325);
lean_ctor_set(x_7, 0, x_329);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_328);
lean_ctor_set(x_6, 0, x_2);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_6);
lean_ctor_set(x_330, 1, x_311);
x_2 = x_330;
goto _start;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_332 = lean_ctor_get(x_7, 1);
lean_inc(x_332);
lean_dec(x_7);
x_333 = lean_ctor_get(x_10, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_334 = x_10;
} else {
 lean_dec_ref(x_10);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_11, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_11, 1);
lean_inc(x_336);
lean_dec(x_11);
lean_inc(x_333);
if (lean_is_scalar(x_334)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_334;
}
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_333);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_333);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_332);
lean_ctor_set(x_2, 1, x_339);
lean_ctor_set(x_2, 0, x_337);
lean_ctor_set(x_6, 0, x_2);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_6);
lean_ctor_set(x_340, 1, x_311);
x_2 = x_340;
goto _start;
}
}
else
{
uint8_t x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_342 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_343 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_344 = lean_ctor_get(x_7, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_345 = x_7;
} else {
 lean_dec_ref(x_7);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_10, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_347 = x_10;
} else {
 lean_dec_ref(x_10);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_11, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_11, 1);
lean_inc(x_349);
lean_dec(x_11);
lean_inc(x_346);
if (lean_is_scalar(x_347)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_347;
}
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_346);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_346);
if (lean_is_scalar(x_345)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_345;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_344);
lean_ctor_set(x_2, 1, x_352);
lean_ctor_set(x_2, 0, x_350);
x_353 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_353, 0, x_2);
lean_ctor_set_uint8(x_353, sizeof(void*)*1, x_342);
lean_ctor_set_uint8(x_353, sizeof(void*)*1 + 1, x_343);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_311);
x_2 = x_354;
goto _start;
}
}
else
{
lean_object* x_356; uint8_t x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_356 = lean_ctor_get(x_2, 1);
lean_inc(x_356);
lean_dec(x_2);
x_357 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_358 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_359 = x_6;
} else {
 lean_dec_ref(x_6);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_7, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_361 = x_7;
} else {
 lean_dec_ref(x_7);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_10, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_363 = x_10;
} else {
 lean_dec_ref(x_10);
 x_363 = lean_box(0);
}
x_364 = lean_ctor_get(x_11, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_11, 1);
lean_inc(x_365);
lean_dec(x_11);
lean_inc(x_362);
if (lean_is_scalar(x_363)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_363;
}
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_362);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_362);
if (lean_is_scalar(x_361)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_361;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_360);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_368);
if (lean_is_scalar(x_359)) {
 x_370 = lean_alloc_ctor(0, 1, 2);
} else {
 x_370 = x_359;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_357);
lean_ctor_set_uint8(x_370, sizeof(void*)*1 + 1, x_358);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_356);
x_2 = x_371;
goto _start;
}
}
default: 
{
uint8_t x_373; 
x_373 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_373 == 0)
{
uint8_t x_374; 
x_374 = !lean_is_exclusive(x_2);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_2, 0);
lean_dec(x_375);
x_376 = !lean_is_exclusive(x_6);
if (x_376 == 0)
{
lean_object* x_377; uint8_t x_378; 
x_377 = lean_ctor_get(x_6, 0);
lean_dec(x_377);
x_378 = !lean_is_exclusive(x_7);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = lean_ctor_get(x_7, 1);
x_380 = lean_ctor_get(x_7, 0);
lean_dec(x_380);
x_381 = !lean_is_exclusive(x_10);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_382 = lean_ctor_get(x_10, 0);
lean_dec(x_382);
x_383 = lean_ctor_get(x_11, 0);
lean_inc(x_383);
x_384 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_383);
x_385 = lean_box(0);
lean_ctor_set(x_7, 1, x_385);
lean_ctor_set(x_6, 0, x_379);
x_386 = l___private_Lean_Data_Format_8__pushGroup(x_384, x_7, x_2, x_1, x_3);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_2 = x_387;
x_3 = x_388;
goto _start;
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_390 = lean_ctor_get(x_10, 1);
lean_inc(x_390);
lean_dec(x_10);
x_391 = lean_ctor_get(x_11, 0);
lean_inc(x_391);
x_392 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_390);
x_394 = lean_box(0);
lean_ctor_set(x_7, 1, x_394);
lean_ctor_set(x_7, 0, x_393);
lean_ctor_set(x_6, 0, x_379);
x_395 = l___private_Lean_Data_Format_8__pushGroup(x_392, x_7, x_2, x_1, x_3);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_2 = x_396;
x_3 = x_397;
goto _start;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_399 = lean_ctor_get(x_7, 1);
lean_inc(x_399);
lean_dec(x_7);
x_400 = lean_ctor_get(x_10, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_401 = x_10;
} else {
 lean_dec_ref(x_10);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_11, 0);
lean_inc(x_402);
x_403 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
if (lean_is_scalar(x_401)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_401;
}
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_400);
x_405 = lean_box(0);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set(x_6, 0, x_399);
x_407 = l___private_Lean_Data_Format_8__pushGroup(x_403, x_406, x_2, x_1, x_3);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_2 = x_408;
x_3 = x_409;
goto _start;
}
}
else
{
uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_411 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_412 = lean_ctor_get(x_7, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_413 = x_7;
} else {
 lean_dec_ref(x_7);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_10, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_415 = x_10;
} else {
 lean_dec_ref(x_10);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_11, 0);
lean_inc(x_416);
x_417 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
if (lean_is_scalar(x_415)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_415;
}
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_414);
x_419 = lean_box(0);
if (lean_is_scalar(x_413)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_413;
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_421, 0, x_412);
lean_ctor_set_uint8(x_421, sizeof(void*)*1, x_373);
lean_ctor_set_uint8(x_421, sizeof(void*)*1 + 1, x_411);
lean_ctor_set(x_2, 0, x_421);
x_422 = l___private_Lean_Data_Format_8__pushGroup(x_417, x_420, x_2, x_1, x_3);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_2 = x_423;
x_3 = x_424;
goto _start;
}
}
else
{
lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_426 = lean_ctor_get(x_2, 1);
lean_inc(x_426);
lean_dec(x_2);
x_427 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_428 = x_6;
} else {
 lean_dec_ref(x_6);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_7, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_430 = x_7;
} else {
 lean_dec_ref(x_7);
 x_430 = lean_box(0);
}
x_431 = lean_ctor_get(x_10, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_432 = x_10;
} else {
 lean_dec_ref(x_10);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_11, 0);
lean_inc(x_433);
x_434 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
if (lean_is_scalar(x_432)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_432;
}
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_431);
x_436 = lean_box(0);
if (lean_is_scalar(x_430)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_430;
}
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
if (lean_is_scalar(x_428)) {
 x_438 = lean_alloc_ctor(0, 1, 2);
} else {
 x_438 = x_428;
}
lean_ctor_set(x_438, 0, x_429);
lean_ctor_set_uint8(x_438, sizeof(void*)*1, x_373);
lean_ctor_set_uint8(x_438, sizeof(void*)*1 + 1, x_427);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_426);
x_440 = l___private_Lean_Data_Format_8__pushGroup(x_434, x_437, x_439, x_1, x_3);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_2 = x_441;
x_3 = x_442;
goto _start;
}
}
else
{
uint8_t x_444; 
x_444 = !lean_is_exclusive(x_2);
if (x_444 == 0)
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_ctor_get(x_2, 0);
lean_dec(x_445);
x_446 = !lean_is_exclusive(x_6);
if (x_446 == 0)
{
lean_object* x_447; uint8_t x_448; 
x_447 = lean_ctor_get(x_6, 0);
lean_dec(x_447);
x_448 = !lean_is_exclusive(x_7);
if (x_448 == 0)
{
lean_object* x_449; uint8_t x_450; 
x_449 = lean_ctor_get(x_7, 0);
lean_dec(x_449);
x_450 = !lean_is_exclusive(x_10);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_10, 0);
lean_dec(x_451);
x_452 = lean_ctor_get(x_11, 0);
lean_inc(x_452);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_452);
goto _start;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_10, 1);
lean_inc(x_454);
lean_dec(x_10);
x_455 = lean_ctor_get(x_11, 0);
lean_inc(x_455);
lean_dec(x_11);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
lean_ctor_set(x_7, 0, x_456);
goto _start;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_458 = lean_ctor_get(x_7, 1);
lean_inc(x_458);
lean_dec(x_7);
x_459 = lean_ctor_get(x_10, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_460 = x_10;
} else {
 lean_dec_ref(x_10);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_11, 0);
lean_inc(x_461);
lean_dec(x_11);
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_459);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_458);
lean_ctor_set(x_6, 0, x_463);
goto _start;
}
}
else
{
uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_465 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
lean_dec(x_6);
x_466 = lean_ctor_get(x_7, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_467 = x_7;
} else {
 lean_dec_ref(x_7);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_10, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_469 = x_10;
} else {
 lean_dec_ref(x_10);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_11, 0);
lean_inc(x_470);
lean_dec(x_11);
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_468);
if (lean_is_scalar(x_467)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_467;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_466);
x_473 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set_uint8(x_473, sizeof(void*)*1, x_373);
lean_ctor_set_uint8(x_473, sizeof(void*)*1 + 1, x_465);
lean_ctor_set(x_2, 0, x_473);
goto _start;
}
}
else
{
lean_object* x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_475 = lean_ctor_get(x_2, 1);
lean_inc(x_475);
lean_dec(x_2);
x_476 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_477 = x_6;
} else {
 lean_dec_ref(x_6);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_7, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_479 = x_7;
} else {
 lean_dec_ref(x_7);
 x_479 = lean_box(0);
}
x_480 = lean_ctor_get(x_10, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_481 = x_10;
} else {
 lean_dec_ref(x_10);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_11, 0);
lean_inc(x_482);
lean_dec(x_11);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_480);
if (lean_is_scalar(x_479)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_479;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_478);
if (lean_is_scalar(x_477)) {
 x_485 = lean_alloc_ctor(0, 1, 2);
} else {
 x_485 = x_477;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set_uint8(x_485, sizeof(void*)*1, x_373);
lean_ctor_set_uint8(x_485, sizeof(void*)*1 + 1, x_476);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_475);
x_2 = x_486;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l___private_Lean_Data_Format_11__be___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_11__be___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Data_Format_11__be(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_11__be___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Data_Format_11__be___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Format_11__be(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
static lean_object* _init_l_Lean_Format_paren___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_paren___closed__4() {
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
static lean_object* _init_l_Lean_Format_sbracket___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__2;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_sbracket___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_sbracket___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_sbracket___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_sbracket___closed__4() {
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
static lean_object* _init_l_Lean_Format_defIndent() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static uint8_t _init_l_Lean_Format_defUnicode() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Format_defWidth() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(120u);
return x_1;
}
}
static lean_object* _init_l_Lean_Format_getWidth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("format");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_getWidth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Format_getWidth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("width");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_getWidth___closed__4() {
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
static lean_object* _init_l_Lean_Format_getIndent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indent");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_getIndent___closed__2() {
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
static lean_object* _init_l_Lean_Format_getUnicode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unicode");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_getUnicode___closed__2() {
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
static lean_object* _init_l_Lean_Format_indentOption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defIndent;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_indentOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indentation");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_indentOption___closed__3() {
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
static lean_object* _init_l_Lean_Format_unicodeOption___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defUnicode;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_unicodeOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unicode characters");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_unicodeOption___closed__3() {
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
static lean_object* _init_l_Lean_Format_widthOption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_defWidth;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_widthOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("line width");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_widthOption___closed__3() {
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
static lean_object* _init_l_Lean_Format_prettyAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_format_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_11 = l_Lean_Format_prettyAux___closed__1;
x_12 = l___private_Lean_Data_Format_11__be___main(x_2, x_10, x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
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
static lean_object* _init_l_Lean_toStringToFormat___rarg___closed__1() {
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
static lean_object* _init_l_Lean_formatHasFormat() {
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
static lean_object* _init_l_Lean_List_format___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_List_format___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_List_format___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_List_format___rarg___closed__2;
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
x_4 = l_Lean_List_format___rarg___closed__3;
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
static lean_object* _init_l_Lean_arrayHasFormat___rarg___closed__1() {
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
static lean_object* _init_l_Lean_Option_format___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_format___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some ");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_format___rarg___closed__3() {
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
x_7 = l_Lean_List_format___rarg___closed__2;
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
static lean_object* _init_l_Lean_Format_repr___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.nil");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.line");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.text");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__7() {
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
static lean_object* _init_l_Lean_Format_repr___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.nest");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__10() {
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
static lean_object* _init_l_Lean_Format_repr___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.append ");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__13() {
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
static lean_object* _init_l_Lean_Format_repr___main___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.group");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__16() {
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
static lean_object* _init_l_Lean_Format_repr___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Format.fill");
return x_1;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Format_repr___main___closed__19() {
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
lean_dec(x_5);
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
lean_dec(x_17);
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
static lean_object* _init_l_Lean_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HasRepr___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_HasRepr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Format_repr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_HasRepr___closed__3() {
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
static lean_object* _init_l_Lean_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HasRepr___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_formatDataValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_formatDataValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_HasRepr___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_formatDataValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
static lean_object* _init_l_Lean_formatDataValue___closed__4() {
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
lean_dec(x_2);
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
static lean_object* _init_l_Lean_dataValueHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatDataValue), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_dataValueHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_dataValueHasFormat___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_formatEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l_Lean_formatEntry___closed__2() {
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
static lean_object* _init_l_Lean_entryHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatEntry), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_entryHasFormat() {
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
static lean_object* _init_l_Lean_formatKVMap___closed__1() {
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
static lean_object* _init_l_Lean_kvMapHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatKVMap), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_kvMapHasFormat() {
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
x_2 = l___private_Lean_Data_Format_10__pushNewline___closed__1;
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
l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1 = _init_l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1();
lean_mark_persistent(l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__1);
l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2 = _init_l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2();
lean_mark_persistent(l___private_Lean_Data_Format_3__spaceUptoLine___main___closed__2);
l___private_Lean_Data_Format_10__pushNewline___closed__1 = _init_l___private_Lean_Data_Format_10__pushNewline___closed__1();
lean_mark_persistent(l___private_Lean_Data_Format_10__pushNewline___closed__1);
l___private_Lean_Data_Format_11__be___main___closed__1 = _init_l___private_Lean_Data_Format_11__be___main___closed__1();
lean_mark_persistent(l___private_Lean_Data_Format_11__be___main___closed__1);
l___private_Lean_Data_Format_11__be___main___closed__2 = _init_l___private_Lean_Data_Format_11__be___main___closed__2();
lean_mark_persistent(l___private_Lean_Data_Format_11__be___main___closed__2);
l___private_Lean_Data_Format_11__be___main___closed__3 = _init_l___private_Lean_Data_Format_11__be___main___closed__3();
lean_mark_persistent(l___private_Lean_Data_Format_11__be___main___closed__3);
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
l_Lean_Format_prettyAux___closed__1 = _init_l_Lean_Format_prettyAux___closed__1();
lean_mark_persistent(l_Lean_Format_prettyAux___closed__1);
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
