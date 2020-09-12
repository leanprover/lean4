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
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Elab_macroAttribute___spec__1(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__7;
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object*);
lean_object* l_Lean_Elab_macroAttribute___closed__2;
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_String_toFormat(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_macroAttribute___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_Def_inhabited___closed__2;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__2(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_macroAttribute___closed__4;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__5;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* lean_get_namespaces(lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* l___private_Lean_Elab_Util_2__evalConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_monadMacroAdapterTrans___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_monadMacroAdapterTrans___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__3;
size_t l_USize_shiftRight(size_t, size_t);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_macroAttribute___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
extern lean_object* l_Lean_mkAttributeImplOfConstant___closed__1;
lean_object* l_Lean_Elab_macroAttribute___closed__5;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__2;
lean_object* l_Lean_Elab_mkMacroAttribute___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__10;
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Elab_macroAttribute___closed__6;
lean_object* l_Lean_Elab_expandMacro_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___private_Lean_Elab_Util_2__evalConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_monadMacroAdapterTrans(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2;
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___closed__2;
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___closed__1;
lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_macroAttribute;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_macroAttribute___closed__7;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_expandMacros___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute(lean_object*);
lean_object* l_Lean_Elab_adaptMacro(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__3;
lean_object* l___private_Lean_Elab_Util_4__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__6;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__4;
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2;
lean_object* l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___closed__3;
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_3__expandMacroFns___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_ReaderT_Monad___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__8;
lean_object* l___private_Lean_Elab_Util_3__expandMacroFns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_mkMacroAttribute___closed__2;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Elab_mkMacroAttribute___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_unsetTrailing(x_1);
x_3 = l_Lean_Syntax_reprint___main(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_formatStxAux___main(x_4, x_5, x_6, x_1);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Name_append___main(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Name_append___main(x_9, x_5);
lean_dec(x_9);
x_11 = l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(x_10, x_3);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Name_append___main(x_15, x_16);
lean_dec(x_15);
x_18 = l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(x_17, x_3);
x_19 = l_System_FilePath_dirName___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_18);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_System_FilePath_dirName___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_22);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
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
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Syntax_getPos(x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_1) == 0)
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
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
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
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_getBetterRef___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_List_find_x3f___main___rarg(x_4, x_2);
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
lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_getBetterRef___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
lean_object* _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("while expanding");
return x_1;
}
}
lean_object* _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Syntax_prettyPrint(x_6);
lean_inc(x_1);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_1);
x_9 = l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_7);
lean_inc(x_1);
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_2 = x_15;
x_3 = x_5;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_addMacroStack___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with resulting expansion");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_addMacroStack___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_addMacroStack___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_addMacroStack(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_prettyPrint(x_4);
x_6 = l_Lean_MessageData_ofList___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Elab_addMacroStack___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1(x_6, x_14, x_2);
return x_15;
}
}
}
lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkSyntaxNodeKind___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_7 = l_Lean_Name_append___main(x_5, x_2);
x_8 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
lean_dec(x_2);
return x_8;
}
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax node kind is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid syntax node kind '");
return x_1;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_6);
x_7 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_6);
lean_inc(x_1);
x_8 = lean_get_namespaces(x_1);
lean_inc(x_6);
x_9 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_1, x_6, x_8);
lean_dec(x_8);
lean_inc(x_6);
x_10 = l_Lean_Name_append___main(x_2, x_6);
x_11 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_10);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_6);
x_16 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_20 = l_System_FilePath_dirName___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_6);
x_22 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Char_HasRepr___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
return x_9;
}
else
{
lean_dec(x_9);
return x_7;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
return x_11;
}
else
{
lean_dec(x_11);
return x_7;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
return x_9;
}
else
{
lean_dec(x_9);
return x_7;
}
}
}
}
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2;
x_4 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAttributeImplOfConstant___closed__1;
return x_3;
}
}
lean_object* l_Lean_Elab_evalSyntaxConstant___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_evalSyntaxConstant(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_2__evalConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAttributeImplOfConstant___closed__1;
return x_5;
}
}
lean_object* l___private_Lean_Elab_Util_2__evalConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Util_2__evalConstant(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_3, x_1, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1() {
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
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 4, 1);
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
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_mkElabAttribute___rarg___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_mkMacroAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macroAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttribute___closed__2;
x_2 = l_Lean_Elab_mkMacroAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinMacro");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macro");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Macro");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_mkMacroAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_mkMacroAttribute___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_mkMacroAttribute___closed__4;
x_3 = l_Lean_Elab_mkMacroAttribute___closed__6;
x_4 = l_Lean_Elab_mkMacroAttribute___closed__8;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_mkMacroAttribute___closed__10;
x_7 = l_Lean_Elab_mkMacroAttribute___closed__7;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Elab_macroAttribute___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_macroAttribute___closed__1;
x_3 = l_Lean_LocalContext_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_macroAttribute___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_macroAttribute___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_macroAttribute___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_macroAttribute___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_macroAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_KeyedDeclsAttribute_Def_inhabited___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_macroAttribute___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Util_3__expandMacroFns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Util_3__expandMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Util_3__expandMacroFns___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
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
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6(x_2, x_7);
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
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
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
x_14 = l___private_Lean_Elab_Util_3__expandMacroFns___main(x_2, x_13, x_3, x_4);
return x_14;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_getMacros___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_getMacros___spec__3(x_1, x_4, x_3);
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
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_getMacros___spec__6(x_1, x_2);
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
lean_object* l_Lean_Elab_monadMacroAdapterTrans___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_monadMacroAdapterTrans___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_monadMacroAdapterTrans___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_monadMacroAdapterTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_monadMacroAdapterTrans___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_environment_main_module(x_1);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_apply_2(x_4, x_12, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_apply_1(x_16, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_18, 0, x_7);
lean_closure_set(x_18, 1, x_14);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_6);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_throwErrorAt___rarg(x_7, x_9, lean_box(0), x_21, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1), 10, 9);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
lean_closure_set(x_12, 7, x_8);
lean_closure_set(x_12, 8, x_9);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2), 10, 9);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
lean_closure_set(x_11, 8, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3), 9, 8);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_1);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
lean_closure_set(x_10, 7, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__4), 8, 7);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
lean_closure_set(x_10, 6, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__5), 8, 7);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_6);
lean_closure_set(x_9, 4, x_1);
lean_closure_set(x_9, 5, x_7);
lean_closure_set(x_9, 6, x_5);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_liftMacroM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_environment_main_module(x_1);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_apply_3(x_4, x_5, x_13, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_apply_1(x_17, x_16);
x_19 = lean_alloc_closure((void*)(l_ReaderT_Monad___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_15);
x_20 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_7);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwErrorAt___rarg(x_8, x_10, lean_box(0), x_22, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__1), 11, 10);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
lean_closure_set(x_13, 6, x_7);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_9);
lean_closure_set(x_13, 9, x_10);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__2), 11, 10);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_10);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
lean_closure_set(x_12, 8, x_8);
lean_closure_set(x_12, 9, x_9);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__3), 10, 9);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_1);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
lean_closure_set(x_11, 8, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__4), 9, 8);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
lean_closure_set(x_11, 7, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__5), 9, 8);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_6);
lean_closure_set(x_10, 4, x_7);
lean_closure_set(x_10, 5, x_1);
lean_closure_set(x_10, 6, x_8);
lean_closure_set(x_10, 7, x_5);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_adaptMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_expandMacro_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_expandMacro_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacro_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_expandMacros___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Elab_expandMacros___main(x_1, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_12, x_2, x_19);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_20;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_expandMacros___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_expandMacro_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = x_6;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_expandMacros___main___spec__1), 5, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_12);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_nat_dec_eq(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_free_object(x_7);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_18, x_24);
lean_dec(x_18);
lean_ctor_set(x_3, 2, x_25);
x_26 = x_14;
x_27 = lean_apply_2(x_26, x_3, x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_2, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_2);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_18, x_37);
lean_dec(x_18);
lean_ctor_set(x_3, 2, x_38);
x_39 = x_14;
x_40 = lean_apply_2(x_39, x_3, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_48 = x_40;
} else {
 lean_dec_ref(x_40);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
x_50 = l_Lean_maxRecDepthErrorMessage;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_51);
return x_7;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_56 = lean_nat_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_57 = x_2;
} else {
 lean_dec_ref(x_2);
 x_57 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_54, x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_55);
x_61 = x_14;
x_62 = lean_apply_2(x_61, x_60, x_10);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_5);
lean_ctor_set(x_66, 1, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_5);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_14);
lean_dec(x_5);
x_72 = l_Lean_maxRecDepthErrorMessage;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_73);
return x_7;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_dec(x_7);
x_75 = x_6;
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_expandMacros___main___spec__1), 5, 3);
lean_closure_set(x_77, 0, x_1);
lean_closure_set(x_77, 1, x_76);
lean_closure_set(x_77, 2, x_75);
x_78 = lean_ctor_get(x_3, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_82 = x_3;
} else {
 lean_dec_ref(x_3);
 x_82 = lean_box(0);
}
x_83 = lean_nat_dec_eq(x_80, x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_84 = x_2;
} else {
 lean_dec_ref(x_2);
 x_84 = lean_box(0);
}
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_80, x_85);
lean_dec(x_80);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 4, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_81);
x_88 = x_77;
x_89 = lean_apply_2(x_88, x_87, x_74);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_84;
}
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_84);
lean_dec(x_5);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_5);
x_99 = l_Lean_maxRecDepthErrorMessage;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_74);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_102 = lean_ctor_get(x_7, 1);
lean_inc(x_102);
lean_dec(x_7);
x_103 = lean_ctor_get(x_8, 0);
lean_inc(x_103);
lean_dec(x_8);
x_2 = x_103;
x_4 = x_102;
goto _start;
}
}
else
{
uint8_t x_105; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_7);
if (x_105 == 0)
{
return x_7;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_7, 0);
x_107 = lean_ctor_get(x_7, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_7);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_2);
lean_ctor_set(x_109, 1, x_4);
return x_109;
}
}
}
lean_object* l_Lean_Elab_expandMacros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacros___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__3;
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
l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1 = _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__1);
l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2 = _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2();
lean_mark_persistent(l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__2);
l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3 = _init_l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3();
lean_mark_persistent(l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1___closed__3);
l_Lean_Elab_addMacroStack___closed__1 = _init_l_Lean_Elab_addMacroStack___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___closed__1);
l_Lean_Elab_addMacroStack___closed__2 = _init_l_Lean_Elab_addMacroStack___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___closed__2);
l_Lean_Elab_addMacroStack___closed__3 = _init_l_Lean_Elab_addMacroStack___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___closed__3);
l_Lean_Elab_checkSyntaxNodeKind___closed__1 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__1);
l_Lean_Elab_checkSyntaxNodeKind___closed__2 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__2();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__2);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1 = _init_l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1);
l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2 = _init_l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__2);
l_Lean_Elab_mkElabAttribute___rarg___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___closed__1);
l_Lean_Elab_mkMacroAttribute___closed__1 = _init_l_Lean_Elab_mkMacroAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__1);
l_Lean_Elab_mkMacroAttribute___closed__2 = _init_l_Lean_Elab_mkMacroAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__2);
l_Lean_Elab_mkMacroAttribute___closed__3 = _init_l_Lean_Elab_mkMacroAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__3);
l_Lean_Elab_mkMacroAttribute___closed__4 = _init_l_Lean_Elab_mkMacroAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__4);
l_Lean_Elab_mkMacroAttribute___closed__5 = _init_l_Lean_Elab_mkMacroAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__5);
l_Lean_Elab_mkMacroAttribute___closed__6 = _init_l_Lean_Elab_mkMacroAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__6);
l_Lean_Elab_mkMacroAttribute___closed__7 = _init_l_Lean_Elab_mkMacroAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__7);
l_Lean_Elab_mkMacroAttribute___closed__8 = _init_l_Lean_Elab_mkMacroAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__8);
l_Lean_Elab_mkMacroAttribute___closed__9 = _init_l_Lean_Elab_mkMacroAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__9);
l_Lean_Elab_mkMacroAttribute___closed__10 = _init_l_Lean_Elab_mkMacroAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_mkMacroAttribute___closed__10);
l_Lean_Elab_macroAttribute___closed__1 = _init_l_Lean_Elab_macroAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__1);
l_Lean_Elab_macroAttribute___closed__2 = _init_l_Lean_Elab_macroAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__2);
l_Lean_Elab_macroAttribute___closed__3 = _init_l_Lean_Elab_macroAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__3);
l_Lean_Elab_macroAttribute___closed__4 = _init_l_Lean_Elab_macroAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__4);
l_Lean_Elab_macroAttribute___closed__5 = _init_l_Lean_Elab_macroAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__5);
l_Lean_Elab_macroAttribute___closed__6 = _init_l_Lean_Elab_macroAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__6);
l_Lean_Elab_macroAttribute___closed__7 = _init_l_Lean_Elab_macroAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_macroAttribute___closed__7);
res = l_Lean_Elab_mkMacroAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
l___private_Lean_Elab_Util_4__regTraceClasses___closed__1 = _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Util_4__regTraceClasses___closed__1);
l___private_Lean_Elab_Util_4__regTraceClasses___closed__2 = _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Util_4__regTraceClasses___closed__2);
l___private_Lean_Elab_Util_4__regTraceClasses___closed__3 = _init_l___private_Lean_Elab_Util_4__regTraceClasses___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Util_4__regTraceClasses___closed__3);
res = l___private_Lean_Elab_Util_4__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
