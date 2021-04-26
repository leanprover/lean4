// Lean compiler output
// Module: Lean.Elab.Util
// Imports: Init Lean.Util.Trace Lean.Parser.Syntax Lean.Parser.Extension Lean.KeyedDeclsAttribute Lean.Elab.Exception
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
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4;
lean_object* l_Lean_Elab_expandOptNamedName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Attribute_Builtin_getId___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_format_unicode___closed__1;
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__7;
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format___boxed(lean_object*, lean_object*);
lean_object* l_String_toFormat(lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_917____closed__1;
extern lean_object* l_Lean_Parser_Command_namedPrio___elambda__1___closed__2;
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__4;
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__1(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1;
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_KeyedDeclsAttribute_getValues___spec__1___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1(lean_object*);
lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2;
lean_object* l_Lean_Elab_expandOptNamedName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAttributeImplOfConstant___closed__1;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__6;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__2;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object*);
lean_object* l_Lean_addTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_53____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint_match__1(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2___boxed(lean_object**);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__5;
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_36____closed__8;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instMonadMacroAdapter(lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280_(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_640_(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253_(lean_object*);
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2(lean_object*);
lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_addMacroStack(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__1(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namedName___elambda__1___closed__2;
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1(lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__1;
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___closed__2;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3;
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__1;
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute(lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2(lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__2(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__2;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__1;
lean_object* l_Lean_throwError___at_Lean_Attribute_Builtin_getId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef___closed__1;
lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux_match__1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__1(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros_match__1(lean_object*);
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__2;
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacroFns_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__4;
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Elab_addMacroStack_match__1(lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_12 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_11);
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
x_17 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_16);
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
x_19 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_18);
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
lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Parser_Command_namedPrio___elambda__1___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_6, x_11);
lean_dec(x_6);
x_13 = l_Lean_evalPrio(x_12, x_2, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1000u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_expandOptNamedPrio(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_expandOptNamedName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Parser_Command_namedName___elambda__1___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_6, x_11);
lean_dec(x_6);
x_13 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
lean_object* l_Lean_Elab_expandOptNamedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_expandOptNamedName(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
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
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
uint8_t l_Lean_Elab_getBetterRef___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Syntax_getPos_x3f(x_2, x_3);
x_5 = lean_box(0);
x_6 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
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
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Syntax_getPos_x3f(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_getBetterRef___closed__1;
x_6 = l_List_find_x3f___rarg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____at_Lean_Elab_getBetterRef___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("macroStack");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dispaly macro expansion stack");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_53____spec__1(x_2, x_3, x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
x_11 = l_Lean_indentD(x_10);
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_2 = x_12;
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
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_pp_macroStack;
x_6 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_2);
return x_9;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = l_Lean_MessageData_ofList___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_14, x_21, x_3);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
return x_25;
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_isValidSyntaxNodeKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
x_12 = l_Lean_throwError___at_Lean_Attribute_Builtin_getId___spec__2(x_11, x_2, x_3, x_8);
return x_12;
}
else
{
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
x_18 = l_Lean_throwError___at_Lean_Attribute_Builtin_getId___spec__2(x_17, x_2, x_3, x_14);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSyntaxNodeKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_7 = l_Lean_Name_append(x_2, x_1);
x_8 = l_Lean_Elab_checkSyntaxNodeKind(x_7, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_2 = x_6;
x_5 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Elab_checkSyntaxNodeKind___closed__2;
x_12 = l_Lean_throwError___at_Lean_Attribute_Builtin_getId___spec__2(x_11, x_3, x_4, x_5);
return x_12;
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Elab_checkSyntaxNodeKindAtNamespacesAux(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid syntax node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lean_Name_append(x_1, x_7);
lean_inc(x_7);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_KernelException_toMessageData___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_7);
x_15 = l_Lean_Elab_checkSyntaxNodeKind(x_7, x_3, x_4, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_7, x_3, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_checkSyntaxNodeKind(x_9, x_3, x_4, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_14);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_throwError___at_Lean_Attribute_Builtin_getId___spec__2(x_14, x_3, x_4, x_20);
lean_dec(x_3);
return x_21;
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Parser_Syntax_addPrec___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
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
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_3, x_4, x_5, x_6);
return x_7;
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
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 6, 1);
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
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_mkElabAttribute___rarg___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
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
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Attribute_Builtin_getId___closed__1;
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
x_4 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__7;
x_5 = lean_box(0);
x_6 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_36____closed__8;
x_7 = l_Lean_Attribute_Builtin_getId___closed__1;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_mkMacroAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_640_(lean_object* x_1) {
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
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_ScopedEnvExtension_getState___at_Lean_KeyedDeclsAttribute_getValues___spec__1___rarg___closed__1;
x_7 = l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
x_8 = lean_panic_fn(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_17 = x_2 >> x_5 % (sizeof(size_t) * 8);
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6(x_4, x_2);
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6(x_11, x_2);
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
x_8 = l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1(x_7, x_1);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2(x_9, x_5);
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
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ScopedEnvExtension_getState___at_Lean_Elab_getMacros___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_getMacros___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_getMacros___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_getMacros___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Elab_getMacros___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_getMacros___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__2(x_1, x_2);
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
lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_instMonadMacroAdapter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapter___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_instMonadMacroAdapter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapter___rarg), 2, 0);
return x_3;
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
lean_object* l_Lean_Elab_liftMacroM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_liftMacroM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_liftMacroM_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_liftMacroM_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM_match__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_addTrace___rarg(x_1, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_13);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_16);
lean_inc(x_5);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_16);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_22, x_15);
return x_23;
}
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_List_reverse___rarg(x_10);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_8);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_environment_main_module(x_1);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_4);
lean_ctor_set(x_18, 4, x_5);
lean_ctor_set(x_18, 5, x_6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_2(x_7, x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_8, 2);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_apply_1(x_24, x_25);
lean_inc(x_13);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed), 9, 8);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_9);
lean_closure_set(x_27, 2, x_10);
lean_closure_set(x_27, 3, x_11);
lean_closure_set(x_27, 4, x_12);
lean_closure_set(x_27, 5, x_13);
lean_closure_set(x_27, 6, x_14);
lean_closure_set(x_27, 7, x_22);
x_28 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_throwErrorAt___rarg(x_9, x_15, x_30, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__5), 16, 15);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_6);
lean_closure_set(x_17, 6, x_7);
lean_closure_set(x_17, 7, x_1);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
lean_closure_set(x_17, 11, x_11);
lean_closure_set(x_17, 12, x_12);
lean_closure_set(x_17, 13, x_13);
lean_closure_set(x_17, 14, x_14);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__6), 15, 14);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_6);
lean_closure_set(x_17, 6, x_7);
lean_closure_set(x_17, 7, x_8);
lean_closure_set(x_17, 8, x_9);
lean_closure_set(x_17, 9, x_10);
lean_closure_set(x_17, 10, x_11);
lean_closure_set(x_17, 11, x_12);
lean_closure_set(x_17, 12, x_13);
lean_closure_set(x_17, 13, x_14);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__7), 15, 14);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_14);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
lean_closure_set(x_16, 11, x_11);
lean_closure_set(x_16, 12, x_12);
lean_closure_set(x_16, 13, x_13);
x_17 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__8), 14, 13);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_5);
lean_closure_set(x_15, 6, x_6);
lean_closure_set(x_15, 7, x_7);
lean_closure_set(x_15, 8, x_8);
lean_closure_set(x_15, 9, x_9);
lean_closure_set(x_15, 10, x_10);
lean_closure_set(x_15, 11, x_11);
lean_closure_set(x_15, 12, x_12);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_14, 0, x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_12);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_12);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = x_18;
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__9), 13, 12);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_8);
lean_closure_set(x_22, 7, x_9);
lean_closure_set(x_22, 8, x_10);
lean_closure_set(x_22, 9, x_11);
lean_closure_set(x_22, 10, x_20);
lean_closure_set(x_22, 11, x_3);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__10), 12, 11);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
lean_closure_set(x_14, 8, x_9);
lean_closure_set(x_14, 9, x_10);
lean_closure_set(x_14, 10, x_11);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__11), 12, 11);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_7);
lean_closure_set(x_13, 8, x_8);
lean_closure_set(x_13, 9, x_9);
lean_closure_set(x_13, 10, x_10);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__12), 11, 10);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_10);
lean_closure_set(x_13, 5, x_1);
lean_closure_set(x_13, 6, x_7);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_9);
lean_closure_set(x_13, 9, x_11);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_liftMacroM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg), 10, 0);
return x_3;
}
}
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_13);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_16);
lean_inc(x_5);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_liftMacroM___spec__2___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_16);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_22, x_15);
return x_23;
}
}
}
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_List_reverse___rarg(x_10);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_8);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_environment_main_module(x_1);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_4);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set(x_19, 5, x_6);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_apply_3(x_7, x_8, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_9, 2);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_apply_1(x_25, x_26);
lean_inc(x_14);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_28, 0, x_24);
lean_closure_set(x_28, 1, x_10);
lean_closure_set(x_28, 2, x_11);
lean_closure_set(x_28, 3, x_12);
lean_closure_set(x_28, 4, x_13);
lean_closure_set(x_28, 5, x_14);
lean_closure_set(x_28, 6, x_15);
lean_closure_set(x_28, 7, x_23);
x_29 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_throwErrorAt___rarg(x_10, x_16, x_31, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__2___boxed), 17, 16);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_8);
lean_closure_set(x_18, 8, x_1);
lean_closure_set(x_18, 9, x_9);
lean_closure_set(x_18, 10, x_10);
lean_closure_set(x_18, 11, x_11);
lean_closure_set(x_18, 12, x_12);
lean_closure_set(x_18, 13, x_13);
lean_closure_set(x_18, 14, x_14);
lean_closure_set(x_18, 15, x_15);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__3), 16, 15);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_8);
lean_closure_set(x_18, 8, x_9);
lean_closure_set(x_18, 9, x_10);
lean_closure_set(x_18, 10, x_11);
lean_closure_set(x_18, 11, x_12);
lean_closure_set(x_18, 12, x_13);
lean_closure_set(x_18, 13, x_14);
lean_closure_set(x_18, 14, x_15);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__4), 16, 15);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
lean_closure_set(x_17, 11, x_11);
lean_closure_set(x_17, 12, x_12);
lean_closure_set(x_17, 13, x_13);
lean_closure_set(x_17, 14, x_14);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__5), 15, 14);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_14);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
lean_closure_set(x_16, 11, x_11);
lean_closure_set(x_16, 12, x_12);
lean_closure_set(x_16, 13, x_13);
x_17 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_15, 0, x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_13);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
x_20 = x_19;
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__6), 14, 13);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_8);
lean_closure_set(x_23, 7, x_9);
lean_closure_set(x_23, 8, x_10);
lean_closure_set(x_23, 9, x_11);
lean_closure_set(x_23, 10, x_12);
lean_closure_set(x_23, 11, x_21);
lean_closure_set(x_23, 12, x_3);
x_24 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__7), 13, 12);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
lean_closure_set(x_15, 7, x_8);
lean_closure_set(x_15, 8, x_9);
lean_closure_set(x_15, 9, x_10);
lean_closure_set(x_15, 10, x_11);
lean_closure_set(x_15, 11, x_12);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__8), 13, 12);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_7);
lean_closure_set(x_14, 8, x_8);
lean_closure_set(x_14, 9, x_9);
lean_closure_set(x_14, 10, x_10);
lean_closure_set(x_14, 11, x_11);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg___lambda__9), 12, 11);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_10);
lean_closure_set(x_14, 5, x_11);
lean_closure_set(x_14, 6, x_1);
lean_closure_set(x_14, 7, x_7);
lean_closure_set(x_14, 8, x_8);
lean_closure_set(x_14, 9, x_9);
lean_closure_set(x_14, 10, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_adaptMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_adaptMacro___rarg), 11, 0);
return x_2;
}
}
lean_object* l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Elab_adaptMacro___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_adaptMacro___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_adaptMacro___rarg___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_adaptMacro___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l_Lean_Elab_mkUnusedBaseName_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_Name_appendIndexAfter(x_1, x_3);
lean_inc(x_6);
x_7 = l_Lean_Name_append(x_2, x_6);
lean_inc(x_4);
x_8 = l_Lean_Macro_hasDecl(x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_3 = x_17;
x_5 = x_15;
goto _start;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_mkUnusedBaseName_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Macro_getCurrNamespace(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = l_Lean_Name_append(x_5, x_1);
lean_inc(x_2);
x_8 = l_Lean_Macro_hasDecl(x_7, x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Elab_mkUnusedBaseName_loop(x_1, x_5, x_16, x_2, x_15);
lean_dec(x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1;
x_2 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_917____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2;
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
lean_object* initialize_Lean_Parser_Syntax(lean_object*);
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
res = initialize_Lean_Parser_Syntax(lean_io_mk_world());
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
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280____closed__4);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_280_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_pp_macroStack = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_pp_macroStack);
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
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2);
l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1 = _init_l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1);
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
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_640_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253____closed__2);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1253_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
