// Lean compiler output
// Module: Lean.Elab.Util
// Imports: Init Lean.Util.Trace Lean.Parser.Extension Lean.KeyedDeclsAttribute Lean.Elab.Exception
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
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Elab_ppMacroStackDefault;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__7;
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_String_toFormat(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_setMacroStackOption___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__12;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam_match__1(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Array_findSomeM_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2;
lean_object* l_Lean_Elab_getMacroStackOption___closed__2;
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1;
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
extern lean_object* l_Lean_mkAttributeImplOfConstant___closed__1;
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__6;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_853____closed__1;
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint_match__1(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_467_(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136_(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834_(lean_object*);
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5;
lean_object* l_Lean_Elab_addMacroStack(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__9;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1;
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3;
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__1;
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute(lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2(lean_object*);
lean_object* l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__2(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__2;
extern lean_object* l_Lean_getSanitizeNames___closed__1;
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_getBetterRef___closed__1;
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__1(lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacroStackOption___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacroStackOption___closed__1;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros_match__1(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__3;
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_Lean_KeyedDeclsAttribute___instance__3___closed__1;
lean_object* l_Lean_Elab_getBetterRef_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
uint8_t l_Lean_Elab_getMacroStackOption(lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2;
extern lean_object* l_IO_Error_Init_System_IOError___instance__3___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__4;
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__8;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Elab_addMacroStack_match__1(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Syntax_prettyPrint_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_prettyPrint_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_prettyPrint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_unsetTrailing(x_1);
x_3 = l_Lean_Syntax_reprint(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_formatStxAux(x_4, x_5, x_6, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_String_toFormat(x_8);
return x_9;
}
}
}
lean_object* l_Lean_MacroScopesView_format(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = l_List_isEmpty___rarg(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_name_eq(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Name_append(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Name_append(x_9, x_5);
lean_dec(x_9);
x_11 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_10, x_3);
x_12 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_append(x_13, x_14);
lean_dec(x_13);
x_16 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_15, x_3);
x_17 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(x_18);
return x_19;
}
}
}
lean_object* l_Lean_MacroScopesView_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MacroScopesView_format(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getBetterRef_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getBetterRef_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getBetterRef_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getBetterRef_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getBetterRef_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getBetterRef_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
static lean_object* _init_l_Lean_Elab_getBetterRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_getBetterRef___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_getBetterRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_getBetterRef___closed__1;
x_5 = l_List_find_x3f___rarg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_getBetterRef___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getBetterRef(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static uint8_t _init_l_Lean_Elab_ppMacroStackDefault() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getMacroStackOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macroStack");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getMacroStackOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_Elab_getMacroStackOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_getMacroStackOption(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_getMacroStackOption___closed__2;
x_3 = l_Lean_Elab_ppMacroStackDefault;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_getMacroStackOption___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_getMacroStackOption(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_setMacroStackOption(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_getMacroStackOption___closed__2;
x_4 = l_Lean_KVMap_setBool(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_setMacroStackOption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Elab_setMacroStackOption(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ppMacroStackDefault;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dispaly macro expansion stack");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_getMacroStackOption___closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_addMacroStack_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_apply_3(x_3, x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_addMacroStack_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("while expanding");
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3;
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_inc(x_1);
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with resulting expansion");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Elab_getMacroStackOption(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_2);
return x_8;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = l_Lean_MessageData_ofList___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_13, x_22, x_3);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_addMacroStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_addMacroStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSyntaxNodeKind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Parser_isValidSyntaxNodeKind(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
lean_dec(x_1);
x_12 = l_Lean_Elab_checkSyntaxNodeKind___closed__3;
x_13 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_12, x_2, x_3, x_4, x_9);
return x_13;
}
else
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Parser_isValidSyntaxNodeKind(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Elab_checkSyntaxNodeKind___closed__3;
x_19 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_18, x_2, x_3, x_4, x_15);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_4(x_2, x_1, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_2, x_1);
x_9 = l_Lean_Elab_checkSyntaxNodeKind(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_7;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Elab_checkSyntaxNodeKind___closed__3;
x_13 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1___rarg(x_12, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_syntaxNodeKindOfAttrParam_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax node kind is missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid syntax node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
x_9 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1___rarg(x_8, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_10);
x_11 = l_Lean_Name_append(x_1, x_10);
lean_inc(x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_10);
x_17 = l_Lean_Elab_checkSyntaxNodeKind(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_10, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_16);
lean_dec(x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_checkSyntaxNodeKind(x_11, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1___rarg(x_16, x_3, x_4, x_5, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2;
x_5 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAttributeImplOfConstant___closed__1;
return x_4;
}
}
lean_object* l_Lean_Elab_evalSyntaxConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_evalSyntaxConstant(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" elaborator");
return x_1;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_init___rarg(x_11, x_1, x_7);
return x_12;
}
}
lean_object* l_Lean_Elab_mkElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_mkElabAttribute___rarg___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macroAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinMacro");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macro");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__4;
x_3 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__6;
x_4 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__8;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__9;
x_7 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__7;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Init_System_IOError___instance__3___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_467_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_9 = lean_apply_3(x_7, x_1, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_getMacros_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getMacros_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getMacros_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_getMacros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_5 = l_Lean_Syntax_getKind(x_2);
x_6 = l_Lean_Elab_macroAttribute;
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_1);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_9, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns(x_2, x_13, x_3, x_4);
return x_14;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getMacros___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getMacros(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_2);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Lean_Elab_Util___instance__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Lean_Elab_Util___instance__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Lean_Elab_Util___instance__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getMacros(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_3(x_3, x_10, x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_liftMacroM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM_match__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = x_13;
x_15 = lean_environment_main_module(x_1);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_3);
lean_ctor_set(x_16, 4, x_4);
x_17 = lean_apply_2(x_5, x_16, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_apply_1(x_20, x_19);
x_22 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_22, 0, x_7);
lean_closure_set(x_22, 1, x_18);
x_23 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_6);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_throwErrorAt___rarg(x_7, x_9, x_10, x_11, lean_box(0), x_25, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_9);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1), 12, 11);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_1);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_7);
lean_closure_set(x_13, 8, x_8);
lean_closure_set(x_13, 9, x_9);
lean_closure_set(x_13, 10, x_10);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2), 11, 10);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
lean_closure_set(x_13, 6, x_7);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_9);
lean_closure_set(x_13, 9, x_10);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3), 11, 10);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_8);
lean_closure_set(x_12, 9, x_9);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__4), 10, 9);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
lean_closure_set(x_11, 8, x_8);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__5), 9, 8);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_liftMacroM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = x_14;
x_16 = lean_environment_main_module(x_1);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
x_18 = lean_apply_3(x_5, x_6, x_17, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_apply_1(x_21, x_20);
x_23 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_8);
lean_closure_set(x_23, 1, x_19);
x_24 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_7);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_throwErrorAt___rarg(x_8, x_10, x_11, x_12, lean_box(0), x_26, x_29);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_31 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_10);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__1), 13, 12);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_1);
lean_closure_set(x_14, 7, x_7);
lean_closure_set(x_14, 8, x_8);
lean_closure_set(x_14, 9, x_9);
lean_closure_set(x_14, 10, x_10);
lean_closure_set(x_14, 11, x_11);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__2), 12, 11);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_9);
lean_closure_set(x_14, 9, x_10);
lean_closure_set(x_14, 10, x_11);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__3), 12, 11);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_7);
lean_closure_set(x_13, 8, x_8);
lean_closure_set(x_13, 9, x_9);
lean_closure_set(x_13, 10, x_10);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__4), 11, 10);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_8);
lean_closure_set(x_12, 9, x_9);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__5), 10, 9);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_9);
lean_closure_set(x_12, 4, x_1);
lean_closure_set(x_12, 5, x_10);
lean_closure_set(x_12, 6, x_5);
lean_closure_set(x_12, 7, x_6);
lean_closure_set(x_12, 8, x_7);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_adaptMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
x_2 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_853____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_Trace(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_getBetterRef___closed__1 = _init_l_Lean_Elab_getBetterRef___closed__1();
lean_mark_persistent(l_Lean_Elab_getBetterRef___closed__1);
l_Lean_Elab_ppMacroStackDefault = _init_l_Lean_Elab_ppMacroStackDefault();
l_Lean_Elab_getMacroStackOption___closed__1 = _init_l_Lean_Elab_getMacroStackOption___closed__1();
lean_mark_persistent(l_Lean_Elab_getMacroStackOption___closed__1);
l_Lean_Elab_getMacroStackOption___closed__2 = _init_l_Lean_Elab_getMacroStackOption___closed__2();
lean_mark_persistent(l_Lean_Elab_getMacroStackOption___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136____closed__3);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_136_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1);
l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2 = _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2);
l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3 = _init_l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3();
lean_mark_persistent(l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3);
l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1);
l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2);
l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3);
l_Lean_Elab_checkSyntaxNodeKind___closed__1 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__1);
l_Lean_Elab_checkSyntaxNodeKind___closed__2 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__2();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__2);
l_Lean_Elab_checkSyntaxNodeKind___closed__3 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__3();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__3);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__4);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__5);
l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1 = _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1);
l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2 = _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__2);
l_Lean_Elab_mkElabAttribute___rarg___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___closed__1);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__1 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__2 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__3 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__4 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__4);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__5 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__6 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__6();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__6);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__7 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__7();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__7);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__8 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__8();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__8);
l_Lean_Elab_mkMacroAttributeUnsafe___closed__9 = _init_l_Lean_Elab_mkMacroAttributeUnsafe___closed__9();
lean_mark_persistent(l_Lean_Elab_mkMacroAttributeUnsafe___closed__9);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_467_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__2);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
