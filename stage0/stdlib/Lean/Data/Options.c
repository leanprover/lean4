// Lean compiler output
// Module: Lean.Data.Options
// Imports: Init Lean.Data.KVMap
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
lean_object* l_Lean_getBoolOption___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__3;
lean_object* l_Lean_setOptionFromString_match__1(lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19;
lean_object* l_Lean_Option_register(lean_object*);
extern lean_object* l_termDepIfThenElse___closed__12;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d__;
extern lean_object* l_Char_quote___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_OptionDecl_group___default;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Option_Decl_group___default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_instReprBool___closed__1;
lean_object* l_Lean_Option_get___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDefaulValue(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
lean_object* l_Lean_instInhabitedOptionDecl___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toInt_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7;
lean_object* l_Lean_KVMap_instToStringKVMap(lean_object*);
lean_object* l_IO_mkRef___at___private_Lean_Data_Options_0__Lean_initOptionDeclsRef___spec__1(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_getOptionDecl___closed__1;
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9;
lean_object* l_Lean_setOptionFromString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedOptions;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13;
lean_object* l_Lean_setOptionFromString_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getNatOption(lean_object*);
lean_object* l_Lean_getBoolOption___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6;
lean_object* l_Lean_registerOption___closed__1;
lean_object* l_Lean_registerOption___closed__2;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5;
lean_object* l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20;
lean_object* l_Lean_setOptionFromString___closed__4;
lean_object* l_Lean_instMonadOptions(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18;
lean_object* l_Lean_OptionDecl_descr___default;
lean_object* l_Lean_instToStringOptions;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_setOptionFromString_match__4(lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16;
lean_object* l_Lean_instMonadOptions___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826_(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprBool___closed__3;
extern lean_object* l_Lean_instInhabitedDataValue___closed__1;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10;
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_get_option_decls_array(lean_object*);
lean_object* l_Lean_getNatOption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3;
extern lean_object* l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__3;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
lean_object* l_Lean_setOptionFromString___closed__5;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_object* l_Lean_Option_set___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_termDepIfThenElse___closed__14;
extern lean_object* l_termDepIfThenElse___closed__9;
extern lean_object* l_termIfLet___x3a_x3d__Then__Else_____closed__8;
lean_object* l_Lean_instInhabitedOptionDecl;
lean_object* l_Lean_getBoolOption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__6;
lean_object* l_Lean_registerOption___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* l_Lean_setOptionFromString_match__3(lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getBoolOption___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_getNatOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8;
lean_object* l_Lean_instInhabitedOption(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_Decl_descr___default;
lean_object* l_Lean_getBoolOption(lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* l_Lean_Option_set(lean_object*);
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_getOptionDecl_match__1(lean_object*);
lean_object* l_Lean_setOptionFromString_match__2(lean_object*);
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_instToStringOptions___closed__1;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2;
lean_object* l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_setOptionFromString___spec__1(lean_object*);
lean_object* l___private_Lean_Data_Options_0__Lean_initOptionDeclsRef(lean_object*);
lean_object* l_Lean_Option_get(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__2;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11;
lean_object* l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_object* l_Lean_registerOption___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17;
extern lean_object* l_Lean_Parser_Tactic_rwRule___closed__3;
lean_object* l_Lean_setOptionFromString___closed__7;
lean_object* l_Lean_instInhabitedOptionDecls;
lean_object* l_Lean_setOptionFromString_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8;
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1;
lean_object* l_Lean_getOptionDescr(lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
lean_object* l_Lean_getNatOption___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedOption___rarg(lean_object*);
static lean_object* _init_l_Lean_Options_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptions() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringOptions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_instToStringKVMap), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringOptions() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToStringOptions___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_OptionDecl_group___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_OptionDecl_descr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedDataValue___closed__1;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedOptionDecl___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_IO_mkRef___at___private_Lean_Data_Options_0__Lean_initOptionDeclsRef___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Data_Options_0__Lean_initOptionDeclsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___at___private_Lean_Data_Options_0__Lean_initOptionDeclsRef___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerOption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_2, x_3);
x_7 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_8 = lean_st_ref_set(x_7, x_6, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_registerOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid option declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_registerOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', option already exists");
return x_1;
}
}
lean_object* lean_register_option(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_NameMap_contains___rarg(x_7, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_5);
x_10 = lean_box(0);
x_11 = l_Lean_registerOption___lambda__1(x_7, x_1, x_2, x_10, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_2);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep(x_12, x_1);
x_14 = l_Lean_registerOption___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_registerOption___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = l_Lean_NameMap_contains___rarg(x_19, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_registerOption___lambda__1(x_19, x_1, x_2, x_22, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_2);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep(x_24, x_1);
x_26 = l_Lean_registerOption___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_registerOption___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
return x_31;
}
}
}
}
lean_object* l_Lean_registerOption___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerOption___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_getOptionDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
lean_object* lean_get_option_decls_array(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_getOptionDecls(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Array_empty___closed__1;
x_6 = l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(x_5, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = l_Array_empty___closed__1;
x_10 = l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(x_9, x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
lean_object* l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___at_Lean_getOptionDeclsArray___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_getOptionDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_getOptionDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getOptionDecl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
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
static lean_object* _init_l_Lean_getOptionDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown option '");
return x_1;
}
}
lean_object* l_Lean_getOptionDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_getOptionDecls(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1(x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_1);
x_9 = l_Lean_getOptionDecl___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Char_quote___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1(x_15, x_1);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep(x_18, x_1);
x_20 = l_Lean_getOptionDecl___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Char_quote___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
return x_27;
}
}
}
}
lean_object* l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_getOptionDecl___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getOptionDefaulValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_getOptionDescr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_setOptionFromString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_setOptionFromString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setOptionFromString_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setOptionFromString_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_setOptionFromString_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setOptionFromString_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setOptionFromString_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_5, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_6, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_setOptionFromString_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setOptionFromString_match__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_setOptionFromString_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
}
lean_object* l_Lean_setOptionFromString_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setOptionFromString_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_setOptionFromString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_String_trim(x_4);
lean_dec(x_4);
x_7 = l_List_map___at_Lean_setOptionFromString___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_String_trim(x_8);
lean_dec(x_8);
x_11 = l_List_map___at_Lean_setOptionFromString___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid configuration option entry, it must be of the form '<key> = <value>'");
return x_1;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setOptionFromString___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_instReprBool___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_instReprBool___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Bool option value '");
return x_1;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Nat option value '");
return x_1;
}
}
static lean_object* _init_l_Lean_setOptionFromString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Int option value '");
return x_1;
}
}
lean_object* l_Lean_setOptionFromString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__3;
x_5 = l_String_splitOn(x_2, x_4);
x_6 = l_List_map___at_Lean_setOptionFromString___spec__1(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_setOptionFromString___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_Lean_setOptionFromString___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_name_mk_string(x_15, x_13);
lean_inc(x_16);
x_17 = l_Lean_getOptionDefaulValue(x_16, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_KVMap_setString(x_1, x_16, x_14);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_KVMap_setString(x_1, x_16, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
case 1:
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_17, 0);
lean_dec(x_26);
x_27 = l_Lean_setOptionFromString___closed__3;
x_28 = lean_name_eq(x_16, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_setOptionFromString___closed__4;
x_30 = lean_name_eq(x_16, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_1);
x_31 = l_Lean_setOptionFromString___closed__5;
x_32 = lean_string_append(x_31, x_14);
lean_dec(x_14);
x_33 = l_Char_quote___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
else
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_14);
x_36 = 0;
x_37 = l_Lean_KVMap_setBool(x_1, x_16, x_36);
lean_ctor_set(x_17, 0, x_37);
return x_17;
}
}
else
{
uint8_t x_38; lean_object* x_39; 
lean_dec(x_14);
x_38 = 1;
x_39 = l_Lean_KVMap_setBool(x_1, x_16, x_38);
lean_ctor_set(x_17, 0, x_39);
return x_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_dec(x_17);
x_41 = l_Lean_setOptionFromString___closed__3;
x_42 = lean_name_eq(x_16, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_setOptionFromString___closed__4;
x_44 = lean_name_eq(x_16, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
lean_dec(x_1);
x_45 = l_Lean_setOptionFromString___closed__5;
x_46 = lean_string_append(x_45, x_14);
lean_dec(x_14);
x_47 = l_Char_quote___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
x_51 = 0;
x_52 = l_Lean_KVMap_setBool(x_1, x_16, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
return x_53;
}
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_14);
x_54 = 1;
x_55 = l_Lean_KVMap_setBool(x_1, x_16, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
return x_56;
}
}
}
case 2:
{
uint8_t x_57; 
lean_dec(x_18);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
lean_dec(x_58);
x_59 = l_String_toName(x_14);
x_60 = l_Lean_KVMap_setName(x_1, x_16, x_59);
lean_ctor_set(x_17, 0, x_60);
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_dec(x_17);
x_62 = l_String_toName(x_14);
x_63 = l_Lean_KVMap_setName(x_1, x_16, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
case 3:
{
uint8_t x_65; 
lean_dec(x_18);
x_65 = !lean_is_exclusive(x_17);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_17, 0);
lean_dec(x_66);
x_67 = l_String_toNat_x3f(x_14);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_16);
lean_dec(x_1);
x_68 = l_Lean_setOptionFromString___closed__6;
x_69 = lean_string_append(x_68, x_14);
lean_dec(x_14);
x_70 = l_Char_quote___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_72);
return x_17;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_14);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l_Lean_KVMap_setNat(x_1, x_16, x_73);
lean_ctor_set(x_17, 0, x_74);
return x_17;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_dec(x_17);
x_76 = l_String_toNat_x3f(x_14);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_16);
lean_dec(x_1);
x_77 = l_Lean_setOptionFromString___closed__6;
x_78 = lean_string_append(x_77, x_14);
lean_dec(x_14);
x_79 = l_Char_quote___closed__1;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_14);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
lean_dec(x_76);
x_84 = l_Lean_KVMap_setNat(x_1, x_16, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
return x_85;
}
}
}
default: 
{
uint8_t x_86; 
lean_dec(x_18);
x_86 = !lean_is_exclusive(x_17);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_17, 0);
lean_dec(x_87);
lean_inc(x_14);
x_88 = l_String_toInt_x3f(x_14);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_16);
lean_dec(x_1);
x_89 = l_Lean_setOptionFromString___closed__7;
x_90 = lean_string_append(x_89, x_14);
lean_dec(x_14);
x_91 = l_Char_quote___closed__1;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_93);
return x_17;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_14);
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
lean_dec(x_88);
x_95 = l_Lean_KVMap_setInt(x_1, x_16, x_94);
lean_ctor_set(x_17, 0, x_95);
return x_17;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_17, 1);
lean_inc(x_96);
lean_dec(x_17);
lean_inc(x_14);
x_97 = l_String_toInt_x3f(x_14);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_16);
lean_dec(x_1);
x_98 = l_Lean_setOptionFromString___closed__7;
x_99 = lean_string_append(x_98, x_14);
lean_dec(x_14);
x_100 = l_Char_quote___closed__1;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_14);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
lean_dec(x_97);
x_105 = l_Lean_KVMap_setInt(x_1, x_16, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_96);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_17);
if (x_107 == 0)
{
return x_17;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_17, 0);
x_109 = lean_ctor_get(x_17, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_17);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_111 = l_Lean_setOptionFromString___closed__2;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
}
}
lean_object* l_Lean_instMonadOptions___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_instMonadOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadOptions___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_getBoolOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_KVMap_getBool(x_4, x_2, x_3);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_getBoolOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getBoolOption___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_7);
return x_8;
}
}
lean_object* l_Lean_getBoolOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getBoolOption___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_getBoolOption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_getBoolOption___rarg___lambda__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_getBoolOption___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_getBoolOption___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_getNatOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_KVMap_getNat(x_4, x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_getNatOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_getNatOption___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
lean_object* l_Lean_getNatOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getNatOption___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_getNatOption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getNatOption___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_instInhabitedOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_instInhabitedOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instInhabitedOption___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_Decl_group___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Option_Decl_descr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
lean_object* l_Lean_Option_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_KVMap_findCore(x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Option_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_get___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Option_get___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_get___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Option_set___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_6, x_4);
x_8 = l_Lean_KVMap_insertCore(x_2, x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_Option_set(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_set___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Option_register___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_6);
x_9 = lean_apply_1(x_5, x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_inc(x_2);
x_11 = lean_register_option(x_2, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Option_register(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_register___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandRegister_builtin_option__:_:=_");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("register_builtin_option");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5;
x_3 = l_termDepIfThenElse___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6;
x_3 = l_termDepIfThenElse___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7;
x_3 = l_termDepIfThenElse___closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8;
x_3 = l_termIfLet___x3a_x3d__Then__Else_____closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9;
x_3 = l_termDepIfThenElse___closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3;
x_2 = lean_unsigned_to_nat(1023u);
x_3 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d__() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtin_initialize");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__3;
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Option");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqIndent");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqItem");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Option.register");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("register");
return x_1;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(5u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1;
lean_inc(x_16);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_20);
lean_inc(x_9);
x_23 = lean_array_push(x_21, x_9);
x_24 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_inc(x_16);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_21, x_25);
x_27 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
lean_inc(x_17);
lean_inc(x_18);
x_28 = l_Lean_addMacroScope(x_18, x_27, x_17);
x_29 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5;
x_30 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7;
lean_inc(x_16);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_array_push(x_21, x_31);
x_33 = lean_array_push(x_21, x_11);
x_34 = l_Lean_nullKind___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_32, x_35);
x_37 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_26, x_38);
x_40 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_array_push(x_23, x_41);
x_43 = l_Lean_Parser_Tactic_rwRule___closed__3;
lean_inc(x_16);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_42, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_22, x_46);
x_48 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18;
x_49 = l_Lean_addMacroScope(x_18, x_48, x_17);
x_50 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16;
x_51 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20;
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_array_push(x_21, x_52);
x_54 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_55 = l___private_Init_Meta_0__Lean_quoteName(x_54);
x_56 = lean_array_push(x_21, x_55);
x_57 = lean_array_push(x_56, x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_34);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_push(x_53, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_37);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_21, x_60);
x_62 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_21, x_63);
x_65 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_66 = lean_array_push(x_64, x_65);
x_67 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_21, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_34);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_21, x_70);
x_72 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_47, x_73);
x_75 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_14, 0, x_76);
return x_14;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_77 = lean_ctor_get(x_14, 0);
x_78 = lean_ctor_get(x_14, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_14);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1;
lean_inc(x_77);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Array_empty___closed__1;
x_84 = lean_array_push(x_83, x_82);
lean_inc(x_9);
x_85 = lean_array_push(x_83, x_9);
x_86 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_inc(x_77);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_83, x_87);
x_89 = l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1;
lean_inc(x_79);
lean_inc(x_80);
x_90 = l_Lean_addMacroScope(x_80, x_89, x_79);
x_91 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5;
x_92 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7;
lean_inc(x_77);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_array_push(x_83, x_93);
x_95 = lean_array_push(x_83, x_11);
x_96 = l_Lean_nullKind___closed__2;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_array_push(x_94, x_97);
x_99 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_array_push(x_88, x_100);
x_102 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_array_push(x_85, x_103);
x_105 = l_Lean_Parser_Tactic_rwRule___closed__3;
lean_inc(x_77);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_77);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_104, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_push(x_84, x_108);
x_110 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18;
x_111 = l_Lean_addMacroScope(x_80, x_110, x_79);
x_112 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16;
x_113 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20;
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_77);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_array_push(x_83, x_114);
x_116 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_117 = l___private_Init_Meta_0__Lean_quoteName(x_116);
x_118 = lean_array_push(x_83, x_117);
x_119 = lean_array_push(x_118, x_13);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_96);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_115, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_99);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_push(x_83, x_122);
x_124 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_push(x_83, x_125);
x_127 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_128 = lean_array_push(x_126, x_127);
x_129 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_83, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_96);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_83, x_132);
x_134 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_109, x_135);
x_137 = l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_78);
return x_139;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_KVMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Options(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean_mark_persistent(l_Lean_Options_empty);
l_Lean_instInhabitedOptions = _init_l_Lean_instInhabitedOptions();
lean_mark_persistent(l_Lean_instInhabitedOptions);
l_Lean_instToStringOptions___closed__1 = _init_l_Lean_instToStringOptions___closed__1();
lean_mark_persistent(l_Lean_instToStringOptions___closed__1);
l_Lean_instToStringOptions = _init_l_Lean_instToStringOptions();
lean_mark_persistent(l_Lean_instToStringOptions);
l_Lean_OptionDecl_group___default = _init_l_Lean_OptionDecl_group___default();
lean_mark_persistent(l_Lean_OptionDecl_group___default);
l_Lean_OptionDecl_descr___default = _init_l_Lean_OptionDecl_descr___default();
lean_mark_persistent(l_Lean_OptionDecl_descr___default);
l_Lean_instInhabitedOptionDecl___closed__1 = _init_l_Lean_instInhabitedOptionDecl___closed__1();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl___closed__1);
l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
res = l___private_Lean_Data_Options_0__Lean_initOptionDeclsRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Data_Options_0__Lean_optionDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Data_Options_0__Lean_optionDeclsRef);
lean_dec_ref(res);
l_Lean_registerOption___closed__1 = _init_l_Lean_registerOption___closed__1();
lean_mark_persistent(l_Lean_registerOption___closed__1);
l_Lean_registerOption___closed__2 = _init_l_Lean_registerOption___closed__2();
lean_mark_persistent(l_Lean_registerOption___closed__2);
l_Lean_getOptionDecl___closed__1 = _init_l_Lean_getOptionDecl___closed__1();
lean_mark_persistent(l_Lean_getOptionDecl___closed__1);
l_Lean_setOptionFromString___closed__1 = _init_l_Lean_setOptionFromString___closed__1();
lean_mark_persistent(l_Lean_setOptionFromString___closed__1);
l_Lean_setOptionFromString___closed__2 = _init_l_Lean_setOptionFromString___closed__2();
lean_mark_persistent(l_Lean_setOptionFromString___closed__2);
l_Lean_setOptionFromString___closed__3 = _init_l_Lean_setOptionFromString___closed__3();
lean_mark_persistent(l_Lean_setOptionFromString___closed__3);
l_Lean_setOptionFromString___closed__4 = _init_l_Lean_setOptionFromString___closed__4();
lean_mark_persistent(l_Lean_setOptionFromString___closed__4);
l_Lean_setOptionFromString___closed__5 = _init_l_Lean_setOptionFromString___closed__5();
lean_mark_persistent(l_Lean_setOptionFromString___closed__5);
l_Lean_setOptionFromString___closed__6 = _init_l_Lean_setOptionFromString___closed__6();
lean_mark_persistent(l_Lean_setOptionFromString___closed__6);
l_Lean_setOptionFromString___closed__7 = _init_l_Lean_setOptionFromString___closed__7();
lean_mark_persistent(l_Lean_setOptionFromString___closed__7);
l_Lean_Option_Decl_group___default = _init_l_Lean_Option_Decl_group___default();
lean_mark_persistent(l_Lean_Option_Decl_group___default);
l_Lean_Option_Decl_descr___default = _init_l_Lean_Option_Decl_descr___default();
lean_mark_persistent(l_Lean_Option_Decl_descr___default);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__1);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__2);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__3);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__4);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__5);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__6);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__7);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__8);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__9);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__10);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11 = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d_____closed__11);
l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d__ = _init_l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d__();
lean_mark_persistent(l_Lean_Option_commandRegister__builtin__option_____x3a___x3a_x3d__);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__1);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__2);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__3);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__4);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__5);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__6);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__7);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__8);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__9);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__10);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__11);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__12);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__13);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__14);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__15);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__16);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__17);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__18);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__19);
l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20 = _init_l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20();
lean_mark_persistent(l_Lean_Option_myMacro____x40_Lean_Data_Options___hyg_826____closed__20);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
